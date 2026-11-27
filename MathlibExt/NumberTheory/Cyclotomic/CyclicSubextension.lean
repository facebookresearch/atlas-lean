/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_NumberField_exists_intermediateField_cyclotomicField_isCyclic_finrank_eq_pow.lean`
and
`P2M/Sol/S_NumberField_exists_intermediateField_cyclotomicField_isCyclic_finrank_eq_pow.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic

import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.RingTheory.ZMod.UnitsCyclic

@[expose] public section

open NumberField

private theorem core {G A : Type*} [Group G] [CommGroup A] [Finite A]
    (χ : G →* A) (hχ : Function.Injective χ) (u : A) {p t a D : ℕ} (hp : p.Prime)
    (hu : orderOf u = p ^ t) (hA : Nat.card A ≤ p ^ t * p)
    (hbig : p ^ (a + D + 2) ≤ D * Nat.card G) :
    ∃ (H : Subgroup G) (_ : H.Normal), IsCyclic (G ⧸ H) ∧ Nat.card (G ⧸ H) = p ^ a := by
  classical
  have hCcard : Nat.card (Subgroup.zpowers u) = p ^ t := (Nat.card_zpowers u).trans hu
  have hCM := (Subgroup.zpowers u).card_mul_index
  rw [hCcard] at hCM
  set C := Subgroup.zpowers u with hCdef
  set M := C.index with hMdef
  have hpt : 0 < p ^ t := pow_pos hp.pos t
  have hM0 : M ≠ 0 := by
    intro h
    rw [h, mul_zero] at hCM
    exact (Nat.card_pos (α := A)).ne' hCM.symm
  have hMpos : 0 < M := Nat.pos_of_ne_zero hM0
  have hMp : M ≤ p := by
    have h' : p ^ t * M ≤ p ^ t * p := by rw [hCM]; exact hA
    exact Nat.le_of_mul_le_mul_left h' hpt

  let f : G →* A := (powMonoidHom M).comp χ
  have hf : ∀ g, f g = χ g ^ M := fun g => rfl
  have hfC : f.range ≤ C := by
    rintro _ ⟨g, rfl⟩
    rw [hf]
    exact C.pow_index_mem (χ g)
  haveI hRcyc : IsCyclic f.range :=
    isCyclic_of_injective (Subgroup.inclusion hfC) (Subgroup.inclusion_injective hfC)
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow hp).1
    (show Nat.card f.range ∣ p ^ t from hCcard ▸ Subgroup.card_dvd_of_le hfC)

  have hle : Nat.card G ≤ p ^ b * (p * p) := by
    set G₀ : Subgroup G := C.comap χ with hG₀
    let φ : G₀ →* C := (χ.comp G₀.subtype).codRestrict C (fun g => g.2)
    have hφ : Function.Injective φ := fun x y h =>
      Subtype.ext (hχ (congrArg Subtype.val h))
    haveI : IsCyclic G₀ := isCyclic_of_injective φ hφ
    obtain ⟨g₀, hg₀⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := G₀)
    have hidx : G₀.index ≤ M := by
      rw [hG₀, Subgroup.index_comap]
      exact Nat.le_of_dvd hMpos (Subgroup.relIndex_dvd_index_of_normal C χ.range)
    have h1 : Nat.card G ≤ orderOf (g₀ : G) * M := by
      rw [Subgroup.orderOf_coe, hg₀, ← G₀.card_mul_index]
      exact Nat.mul_le_mul_left _ hidx
    have h2 : orderOf (g₀ : G) ≤ orderOf (f g₀) * M := by
      rw [← orderOf_injective χ hχ (g₀ : G), hf, orderOf_pow' _ hM0]
      calc orderOf (χ g₀)
          = orderOf (χ g₀) / (orderOf (χ g₀)).gcd M * (orderOf (χ g₀)).gcd M :=
            (Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)).symm
        _ ≤ orderOf (χ g₀) / (orderOf (χ g₀)).gcd M * M :=
            Nat.mul_le_mul_left _ (Nat.gcd_le_right _ hMpos)
    have h3 : orderOf (f g₀) ≤ p ^ b := by
      apply Nat.le_of_dvd (pow_pos hp.pos b)
      rw [← hb]
      exact f.range.orderOf_dvd_natCard (MonoidHom.mem_range.mpr ⟨g₀, rfl⟩)
    calc Nat.card G ≤ orderOf (g₀ : G) * M := h1
      _ ≤ orderOf (f g₀) * M * M := Nat.mul_le_mul_right _ h2
      _ ≤ p ^ b * p * p := by gcongr
      _ = p ^ b * (p * p) := by ring

  have hab : a ≤ b := by
    by_contra hab
    push Not at hab
    have h4 : p ^ b * (p * p) ≤ p ^ (a + 1) := by
      rw [← pow_two, ← pow_add]
      exact Nat.pow_le_pow_right hp.pos (by omega)
    have h5 : D < p ^ D := Nat.lt_pow_self hp.one_lt
    have h6 : p ^ D * p ^ (a + 1) ≤ p ^ (a + D + 2) := by
      rw [← pow_add]
      exact Nat.pow_le_pow_right hp.pos (by omega)
    have h8 : D * p ^ (a + 1) < p ^ D * p ^ (a + 1) :=
      Nat.mul_lt_mul_of_pos_right h5 (pow_pos hp.pos _)
    exact lt_irrefl _ ((((hbig.trans (Nat.mul_le_mul_left D hle)).trans
      (Nat.mul_le_mul_left D h4)).trans_lt h8).trans_le h6)

  obtain ⟨w₀, hw₀⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := f.range)
  have hNcard : Nat.card (Subgroup.zpowers (w₀ ^ (p ^ a))) = p ^ (b - a) := by
    rw [Nat.card_zpowers, orderOf_pow' _ (pow_ne_zero a hp.ne_zero), hw₀, hb,
      Nat.gcd_eq_right (pow_dvd_pow p hab), Nat.pow_div hab hp.pos]
  have hNidx : (Subgroup.zpowers (w₀ ^ (p ^ a))).index = p ^ a := by
    have h := (Subgroup.zpowers (w₀ ^ (p ^ a))).card_mul_index
    rw [hNcard, hb] at h
    have hpb : p ^ (b - a) * p ^ a = p ^ b := by rw [← pow_add, Nat.sub_add_cancel hab]
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos _) (h.trans hpb.symm)
  set N : Subgroup f.range := Subgroup.zpowers (w₀ ^ (p ^ a)) with hNdef
  let ψ : G →* f.range ⧸ N := (QuotientGroup.mk' N).comp f.rangeRestrict
  have hψ : Function.Surjective ψ :=
    (QuotientGroup.mk'_surjective N).comp f.rangeRestrict_surjective
  let e := QuotientGroup.quotientKerEquivOfSurjective ψ hψ
  haveI : IsCyclic (f.range ⧸ N) :=
    isCyclic_of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  refine ⟨ψ.ker, inferInstance, isCyclic_of_surjective e.symm e.symm.surjective, ?_⟩
  rw [Nat.card_congr e.toEquiv]
  exact hNidx

/-- For every number field `K`, prime `p`, and `a`, some prime-power
cyclotomic extension of `K` has a cyclic Galois intermediate field over `K`
of degree `p ^ a`. -/
public theorem NumberField.exists_intermediateField_cyclotomicField_isCyclic_finrank_eq_pow
    (K : Type*) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime] (a : ℕ) :
    ∃ (k : ℕ) (L : IntermediateField K (CyclotomicField (p ^ k) K)),
      IsGalois K L ∧ IsCyclic (L ≃ₐ[K] L) ∧ Module.finrank K L = p ^ a := by
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨D, hD⟩ : ∃ D, D = Module.finrank ℚ K := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n, n = a + D + 1 := ⟨_, rfl⟩
  haveI : NeZero (p ^ (n + 2)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  haveI : IsGalois K (CyclotomicField (p ^ (n + 2)) K) :=
    IsCyclotomicExtension.isGalois {p ^ (n + 2)} K _
  have hζ := IsCyclotomicExtension.zeta_spec (p ^ (n + 2)) K (CyclotomicField (p ^ (n + 2)) K)

  obtain ⟨u, t, hu, hA⟩ : ∃ (u : (ZMod (p ^ (n + 2)))ˣ) (t : ℕ),
      orderOf u = p ^ t ∧ Nat.card (ZMod (p ^ (n + 2)))ˣ ≤ p ^ t * p := by
    have hcard : Nat.card (ZMod (p ^ (n + 2)))ˣ = p ^ (n + 1) * (p - 1) := by
      rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
        Nat.totient_prime_pow hp (Nat.succ_pos _), (by omega : n + 2 - 1 = n + 1)]
    rcases eq_or_ne p 2 with rfl | hp2
    · have h5 : orderOf (5 : ZMod (2 ^ (n + 2))) = 2 ^ n := ZMod.orderOf_five n
      have hfin : IsOfFinOrder (5 : ZMod (2 ^ (n + 2))) :=
        orderOf_pos_iff.mp (by rw [h5]; exact pow_pos two_pos n)
      refine ⟨hfin.unit, n, by rw [← orderOf_units, hfin.val_unit, h5], ?_⟩
      rw [hcard, pow_succ]
      simp
    · have h1 : orderOf (1 + (p : ZMod (p ^ (n + 2)))) = p ^ (n + 1) :=
        ZMod.orderOf_one_add_prime hp hp2 (n + 1)
      have hfin : IsOfFinOrder (1 + (p : ZMod (p ^ (n + 2)))) :=
        orderOf_pos_iff.mp (by rw [h1]; exact pow_pos hp.pos _)
      refine ⟨hfin.unit, n + 1, by rw [← orderOf_units, hfin.val_unit, h1], ?_⟩
      rw [hcard]
      exact Nat.mul_le_mul_left _ (Nat.sub_le p 1)

  have hG := IsGalois.card_aut_eq_finrank K (CyclotomicField (p ^ (n + 2)) K)
  have htower : D * Module.finrank K (CyclotomicField (p ^ (n + 2)) K)
      = Module.finrank ℚ (CyclotomicField (p ^ (n + 2)) K) := by
    rw [hD]; exact Module.finrank_mul_finrank ℚ K _
  have hdeg : p ^ (n + 1) ≤ Module.finrank ℚ (CyclotomicField (p ^ (n + 2)) K) := by
    have h1 : (Polynomial.cyclotomic (p ^ (n + 2)) ℚ).natDegree = p ^ (n + 1) * (p - 1) := by
      rw [Polynomial.natDegree_cyclotomic, Nat.totient_prime_pow hp (Nat.succ_pos _),
        (by omega : n + 2 - 1 = n + 1)]
    have h2 := Polynomial.cyclotomic_eq_minpoly_rat hζ (pow_pos hp.pos _)
    have h3 := minpoly.natDegree_le (A := ℚ)
      (IsCyclotomicExtension.zeta (p ^ (n + 2)) K (CyclotomicField (p ^ (n + 2)) K))
    calc p ^ (n + 1) ≤ p ^ (n + 1) * (p - 1) :=
          Nat.le_mul_of_pos_right _ (Nat.sub_pos_of_lt hp.one_lt)
      _ = _ := h1.symm
      _ ≤ _ := by rw [h2]; exact h3
  have hbig : p ^ (a + D + 2) ≤
      D * Nat.card ((CyclotomicField (p ^ (n + 2)) K) ≃ₐ[K] (CyclotomicField (p ^ (n + 2)) K)) := by
    rw [(by omega : a + D + 2 = n + 1), hG, htower]
    exact hdeg
  obtain ⟨H, hHn, hHcyc, hHcard⟩ :=
    core (hζ.autToPow K) (hζ.autToPow_injective K) u hp hu hA hbig
  haveI hLgal : IsGalois K (IntermediateField.fixedField H) :=
    IsGalois.of_fixedField_normal_subgroup H
  let e := IsGalois.normalAutEquivQuotient H
  refine ⟨n + 2, IntermediateField.fixedField H, hLgal, isCyclic_of_surjective e e.surjective, ?_⟩
  rw [← IsGalois.card_aut_eq_finrank K (IntermediateField.fixedField H), ← hHcard]
  exact Nat.card_congr e.symm.toEquiv
