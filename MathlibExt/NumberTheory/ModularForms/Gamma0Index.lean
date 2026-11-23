/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_ModularCurve_ProjectiveLine.lean`,
`Theorems/Thm_ModularCurve_Gamma0_index.lean`,
`Theorems/Thm_ModularCurve_card_quotient_gamma0_eq_index.lean`,
`Theorems/Thm_ModularCurve_card_projectiveLine_zmod.lean`,
`P2M/Sol/S_ModularCurve_Gamma0_index.lean`,
`P2M/Sol/S_ModularCurve_card_quotient_gamma0_eq_index.lean` and
`P2M/Sol/S_ModularCurve_card_projectiveLine_zmod.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib - https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and arguments are reused here with that machinery
removed, the names restated in Mathlib style, and the proofs rewritten to use
Mathlib APIs directly. The Dedekind psi value is the arithmetic function
`ArithmeticFunction.dedekindPsi` already in this repository.
-/

module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.GroupTheory.Index
public import MathlibExt.NumberTheory.ArithmeticFunction.DedekindPsi

import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Data.Finite.Prod

/-!
# Index of the congruence subgroup Gamma0

The index of `Gamma0 N` in `SL(2, Z)` is the Dedekind psi value `psi(N)`.
The proof identifies the quotient by the Borel subgroup of upper-triangular
matrices with the projective line over `ZMod N`, counts that projective
line by a prime-power calculation and the Chinese remainder theorem, and
lifts surjectivity of reduction modulo `N` from `Z` to `ZMod N`.
-/

@[expose] public section

namespace ModularCurve

open Matrix CongruenceSubgroup
open scoped MatrixGroups

section ProjectiveLine

variable {R S : Type*} [CommRing R] [CommRing S]

def IsUnimodularRow (a c : R) : Prop :=
  ∃ x y : R, x * a + y * c = 1

theorem isUnimodularRow_one_left (t : R) : IsUnimodularRow (1 : R) t :=
  ⟨1, 0, by simp⟩

theorem isUnimodularRow_one_right (m : R) : IsUnimodularRow m (1 : R) :=
  ⟨0, 1, by simp⟩

theorem IsUnimodularRow.map (f : R →+* S) {a c : R} (h : IsUnimodularRow a c) :
    IsUnimodularRow (f a) (f c) := by
  obtain ⟨x, y, hxy⟩ := h
  exact ⟨f x, f y, by rw [← map_mul, ← map_mul, ← map_add, hxy, map_one]⟩

abbrev UnimodularRow (R : Type*) [CommRing R] := { v : R × R // IsUnimodularRow v.1 v.2 }

instance unimodularRowSetoid (R : Type*) [CommRing R] : Setoid (UnimodularRow R) where
  r v w := ∃ u : Rˣ, (u : R) * v.1.1 = w.1.1 ∧ (u : R) * v.1.2 = w.1.2
  iseqv := by
    refine ⟨fun v => ⟨1, by simp, by simp⟩, ?_, ?_⟩
    · rintro v w ⟨u, h1, h2⟩
      exact ⟨u⁻¹, by rw [← h1, Units.inv_mul_cancel_left],
        by rw [← h2, Units.inv_mul_cancel_left]⟩
    · rintro v w z ⟨u, h1, h2⟩ ⟨u', h1', h2'⟩
      exact ⟨u' * u, by rw [Units.val_mul, mul_assoc, h1, h1'],
        by rw [Units.val_mul, mul_assoc, h2, h2']⟩

def ProjectiveLine (R : Type*) [CommRing R] : Type _ :=
  Quotient (unimodularRowSetoid R)

instance instFiniteProjectiveLine [Finite R] : Finite (ProjectiveLine R) :=
  Quotient.finite _

def ProjectiveLine.map (f : R →+* S) : ProjectiveLine R → ProjectiveLine S :=
  Quotient.lift (fun v => (⟦⟨(f v.1.1, f v.1.2), v.2.map f⟩⟧ : ProjectiveLine S)) <| by
    rintro v w ⟨u, h1, h2⟩
    refine Quotient.sound ⟨⟨f u, f ↑u⁻¹, ?_, ?_⟩, ?_, ?_⟩
    · rw [← map_mul, Units.mul_inv, map_one]
    · rw [← map_mul, Units.inv_mul, map_one]
    · show f ↑u * f v.1.1 = f w.1.1
      rw [← map_mul, h1]
    · show f ↑u * f v.1.2 = f w.1.2
      rw [← map_mul, h2]

@[simp]
theorem ProjectiveLine.map_mk (f : R →+* S) (v : UnimodularRow R) :
    ProjectiveLine.map f ⟦v⟧ = ⟦⟨(f v.1.1, f v.1.2), v.2.map f⟩⟧ :=
  rfl

end ProjectiveLine

section Borel

variable {R : Type*} [CommRing R]

def borel (R : Type*) [CommRing R] : Subgroup (SpecialLinearGroup (Fin 2) R) where
  carrier := { M | M.1 1 0 = 0 }
  one_mem' := by
    show (1 : SpecialLinearGroup (Fin 2) R).1 1 0 = 0
    simp
  mul_mem' := by
    intro A B hA hB
    simp only [Set.mem_setOf_eq] at *
    show (A * B).1 1 0 = 0
    rw [SpecialLinearGroup.coe_mul, (Matrix.two_mul_expl A.1 B.1).2.2.1, hA, hB]
    ring
  inv_mem' := by
    intro A hA
    simp only [Set.mem_setOf_eq] at *
    show (A⁻¹).1 1 0 = 0
    rw [SpecialLinearGroup.SL2_inv_expl A]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, neg_eq_zero]
    exact hA

theorem mem_borel_iff {A : SpecialLinearGroup (Fin 2) R} : A ∈ borel R ↔ A.1 1 0 = 0 :=
  Iff.rfl

end Borel

section PrimePower

private theorem isUnit_zmod_prime_pow_iff {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) (z : ZMod (p ^ k)) :
    IsUnit z ↔ ZMod.castHom (dvd_pow_self p hk) (ZMod p) z ≠ 0 := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.pos.ne'⟩
  haveI : Fact p.Prime := ⟨hp⟩
  constructor
  · intro h hzero
    exact (h.map (ZMod.castHom (dvd_pow_self p hk) (ZMod p))).ne_zero hzero
  · intro h
    by_contra hz
    apply h

    have hval : ¬z.val.Coprime (p ^ k) := fun hcop =>
      hz (by rw [← ZMod.natCast_zmod_val z]; exact (ZMod.isUnit_iff_coprime _ _).mpr hcop)
    have hdvd : p ∣ z.val := by
      by_contra hndvd
      exact hval (((hp.coprime_iff_not_dvd).mpr hndvd).symm.pow_right k)
    calc ZMod.castHom (dvd_pow_self p hk) (ZMod p) z
        = ZMod.castHom (dvd_pow_self p hk) (ZMod p) ((z.val : ℕ) : ZMod (p ^ k)) := by
          rw [ZMod.natCast_zmod_val]
      _ = ((z.val : ℕ) : ZMod p) := map_natCast _ _
      _ = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd

namespace IsUnimodularRow

private theorem _root_.ModularCurve.IsUnimodularRow.isUnit_or_isUnit {p k : ℕ}
    (hp : p.Prime) (hk : k ≠ 0)
    {a c : ZMod (p ^ k)} (h : IsUnimodularRow a c) : IsUnit a ∨ IsUnit c := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hcon
  rw [not_or] at hcon
  have ha : ZMod.castHom (dvd_pow_self p hk) (ZMod p) a = 0 := by
    by_contra hne
    exact hcon.1 ((isUnit_zmod_prime_pow_iff hp hk a).mpr hne)
  have hc : ZMod.castHom (dvd_pow_self p hk) (ZMod p) c = 0 := by
    by_contra hne
    exact hcon.2 ((isUnit_zmod_prime_pow_iff hp hk c).mpr hne)
  obtain ⟨x, y, hxy⟩ := h
  apply_fun ZMod.castHom (dvd_pow_self p hk) (ZMod p) at hxy
  rw [map_add, map_mul, map_mul, map_one, ha, hc, mul_zero, mul_zero, add_zero] at hxy
  exact zero_ne_one hxy

end IsUnimodularRow

private noncomputable def isUnitSubtypeEquivUnits (M : Type*) [Monoid M] :
    { z : M // IsUnit z } ≃ Mˣ where
  toFun z := z.2.unit
  invFun u := ⟨u, u.isUnit⟩
  left_inv z := Subtype.ext z.2.unit_spec
  right_inv u := Units.ext u.isUnit.unit_spec

private theorem card_not_isUnit_zmod_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    Nat.card { z : ZMod (p ^ k) // ¬IsUnit z } = p ^ (k - 1) := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.pos.ne'⟩
  classical

  have hsplit : Nat.card { z : ZMod (p ^ k) // IsUnit z } +
      Nat.card { z : ZMod (p ^ k) // ¬IsUnit z } = p ^ k := by
    rw [← Nat.card_sum, Nat.card_congr (Equiv.sumCompl (IsUnit ·)),
      Nat.card_eq_fintype_card, ZMod.card]

  have hunits : Nat.card { z : ZMod (p ^ k) // IsUnit z } = (p ^ k).totient := by
    rw [Nat.card_congr (isUnitSubtypeEquivUnits (ZMod (p ^ k))), Nat.card_eq_fintype_card,
      ZMod.card_units_eq_totient]

  have htot : (p ^ k).totient + p ^ (k - 1) = p ^ k := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hp1 : p - 1 + 1 = p := Nat.succ_pred_eq_of_pos hp.pos
    calc (p ^ (j + 1)).totient + p ^ (j + 1 - 1)
        = p ^ j * (p - 1) + p ^ j := by rw [Nat.totient_prime_pow_succ hp, Nat.add_sub_cancel]
      _ = p ^ j * (p - 1 + 1) := by ring
      _ = p ^ j * p := by rw [hp1]
      _ = p ^ (j + 1) := (pow_succ p j).symm
  omega

private theorem card_projectiveLine_prime_pow (p k : ℕ) (hp : p.Prime) (hk : k ≠ 0) :
    Nat.card (ProjectiveLine (ZMod (p ^ k))) = p ^ k + p ^ (k - 1) := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.pos.ne'⟩

  let f : ZMod (p ^ k) ⊕ { z : ZMod (p ^ k) // ¬IsUnit z } → ProjectiveLine (ZMod (p ^ k)) :=
    fun s => Sum.rec (fun t => ⟦⟨(1, t), isUnimodularRow_one_left t⟩⟧)
      (fun m => ⟦⟨(m.1, 1), isUnimodularRow_one_right m.1⟩⟧) s
  have hbij : Function.Bijective f := by
    constructor
    · rintro (t | m) (t' | m') hff
      ·
        obtain ⟨u, h1, h2⟩ := Quotient.exact hff
        have h1' : (u : ZMod (p ^ k)) * 1 = 1 := h1
        have h2' : (u : ZMod (p ^ k)) * t = t' := h2
        rw [mul_one] at h1'
        rw [h1', one_mul] at h2'
        exact congrArg Sum.inl h2'
      ·
        obtain ⟨u, h1, _⟩ := Quotient.exact hff
        have h1' : (u : ZMod (p ^ k)) * 1 = m'.1 := h1
        exact absurd (h1' ▸ (u.isUnit.mul isUnit_one)) m'.2
      ·
        obtain ⟨u, h1, _⟩ := Quotient.exact hff
        have h1' : (u : ZMod (p ^ k)) * m.1 = 1 := h1
        exact absurd ⟨⟨m.1, u, (mul_comm m.1 u).trans h1', h1'⟩, rfl⟩ m.2
      ·
        obtain ⟨u, h1, h2⟩ := Quotient.exact hff
        have h1' : (u : ZMod (p ^ k)) * m.1 = m'.1 := h1
        have h2' : (u : ZMod (p ^ k)) * 1 = 1 := h2
        rw [mul_one] at h2'
        rw [h2', one_mul] at h1'
        exact congrArg Sum.inr (Subtype.ext h1')
    · intro q
      obtain ⟨v, rfl⟩ := Quotient.exists_rep q
      by_cases ha : IsUnit v.1.1
      ·
        refine ⟨Sum.inl ((ha.unit⁻¹ : (ZMod (p ^ k))ˣ) * v.1.2), Quotient.sound ⟨ha.unit, ?_, ?_⟩⟩
        · show (ha.unit : ZMod (p ^ k)) * 1 = v.1.1
          rw [mul_one, ha.unit_spec]
        · show (ha.unit : ZMod (p ^ k)) * ((ha.unit⁻¹ : (ZMod (p ^ k))ˣ) * v.1.2) = v.1.2
          rw [Units.mul_inv_cancel_left]
      ·
        have hc : IsUnit v.1.2 := (v.2.isUnit_or_isUnit hp hk).resolve_left ha
        have hm : ¬IsUnit ((hc.unit⁻¹ : (ZMod (p ^ k))ˣ) * v.1.1) := fun hcon => by
          have : IsUnit ((hc.unit : ZMod (p ^ k)) * ((hc.unit⁻¹ : (ZMod (p ^ k))ˣ) * v.1.1)) :=
            hc.unit.isUnit.mul hcon
          rw [Units.mul_inv_cancel_left] at this
          exact ha this
        refine ⟨Sum.inr ⟨(hc.unit⁻¹ : (ZMod (p ^ k))ˣ) * v.1.1, hm⟩,
          Quotient.sound ⟨hc.unit, ?_, ?_⟩⟩
        · show (hc.unit : ZMod (p ^ k)) * ((hc.unit⁻¹ : (ZMod (p ^ k))ˣ) * v.1.1) = v.1.1
          rw [Units.mul_inv_cancel_left]
        · show (hc.unit : ZMod (p ^ k)) * 1 = v.1.2
          rw [mul_one, hc.unit_spec]
  rw [← Nat.card_eq_of_bijective f hbij, Nat.card_sum, Nat.card_eq_fintype_card, ZMod.card,
    card_not_isUnit_zmod_prime_pow hp hk]

end PrimePower

section CRT

private def crtFst (M N : ℕ) (h : M.Coprime N) : ZMod (M * N) →+* ZMod M :=
  (RingHom.fst (ZMod M) (ZMod N)).comp (ZMod.chineseRemainder h).toRingHom

private def crtSnd (M N : ℕ) (h : M.Coprime N) : ZMod (M * N) →+* ZMod N :=
  (RingHom.snd (ZMod M) (ZMod N)).comp (ZMod.chineseRemainder h).toRingHom

private theorem crtFst_apply (M N : ℕ) (h : M.Coprime N) (z : ZMod (M * N)) :
    crtFst M N h z = (ZMod.chineseRemainder h z).1 :=
  rfl

private theorem crtSnd_apply (M N : ℕ) (h : M.Coprime N) (z : ZMod (M * N)) :
    crtSnd M N h z = (ZMod.chineseRemainder h z).2 :=
  rfl

private theorem card_projectiveLine_mul (M N : ℕ) [NeZero M] [NeZero N] (h : M.Coprime N) :
    Nat.card (ProjectiveLine (ZMod (M * N))) =
      Nat.card (ProjectiveLine (ZMod M)) * Nat.card (ProjectiveLine (ZMod N)) := by
  haveI : NeZero (M * N) := ⟨mul_ne_zero (NeZero.ne M) (NeZero.ne N)⟩
  set e := ZMod.chineseRemainder h with he

  let F : ProjectiveLine (ZMod (M * N)) → ProjectiveLine (ZMod M) × ProjectiveLine (ZMod N) :=
    fun q => (ProjectiveLine.map (crtFst M N h) q, ProjectiveLine.map (crtSnd M N h) q)
  have hbij : Function.Bijective F := by
    constructor
    ·
      intro q q'
      refine Quotient.inductionOn₂ q q' ?_
      intro v w hvw
      obtain ⟨hM, hN⟩ := Prod.mk.injEq .. ▸ hvw
      obtain ⟨u₁, h1M, h2M⟩ := Quotient.exact hM
      obtain ⟨u₂, h1N, h2N⟩ := Quotient.exact hN
      have h1M' : (u₁ : ZMod M) * crtFst M N h v.1.1 = crtFst M N h w.1.1 := h1M
      have h2M' : (u₁ : ZMod M) * crtFst M N h v.1.2 = crtFst M N h w.1.2 := h2M
      have h1N' : (u₂ : ZMod N) * crtSnd M N h v.1.1 = crtSnd M N h w.1.1 := h1N
      have h2N' : (u₂ : ZMod N) * crtSnd M N h v.1.2 = crtSnd M N h w.1.2 := h2N

      have hUmul : e.symm (↑u₁, ↑u₂) * e.symm (↑u₁⁻¹, ↑u₂⁻¹) = 1 := by
        rw [← map_mul, Prod.mk_mul_mk, Units.mul_inv, Units.mul_inv]
        exact map_one e.symm
      have hUmul' : e.symm (↑u₁⁻¹, ↑u₂⁻¹) * e.symm (↑u₁, ↑u₂) = 1 :=
        (mul_comm _ _).trans hUmul

      have key : ∀ z z' : ZMod (M * N), (u₁ : ZMod M) * (e z).1 = (e z').1 →
          (u₂ : ZMod N) * (e z).2 = (e z').2 →
          e.symm (↑u₁, ↑u₂) * z = z' := by
        intro z z' hz1 hz2
        apply e.injective
        rw [map_mul, RingEquiv.apply_symm_apply]
        calc (((u₁ : ZMod M), (u₂ : ZMod N)) : ZMod M × ZMod N) * e z
            = (↑u₁ * (e z).1, ↑u₂ * (e z).2) := Prod.mk_mul_mk ..
          _ = ((e z').1, (e z').2) := by rw [hz1, hz2]
          _ = e z' := rfl
      exact Quotient.sound ⟨⟨e.symm (↑u₁, ↑u₂), e.symm (↑u₁⁻¹, ↑u₂⁻¹), hUmul, hUmul'⟩,
        key v.1.1 w.1.1 h1M' h1N', key v.1.2 w.1.2 h2M' h2N'⟩
    ·
      rintro ⟨x, y⟩
      obtain ⟨a, rfl⟩ := Quotient.exists_rep x
      obtain ⟨b, rfl⟩ := Quotient.exists_rep y
      obtain ⟨xa, ya, hab⟩ := a.2
      obtain ⟨xb, yb, hbb⟩ := b.2

      have hglue : IsUnimodularRow (e.symm (a.1.1, b.1.1)) (e.symm (a.1.2, b.1.2)) := by
        refine ⟨e.symm (xa, xb), e.symm (ya, yb), ?_⟩
        rw [← map_mul, ← map_mul, ← map_add, Prod.mk_mul_mk, Prod.mk_mul_mk, Prod.mk_add_mk,
          hab, hbb]
        exact map_one e.symm
      refine ⟨⟦⟨(e.symm (a.1.1, b.1.1), e.symm (a.1.2, b.1.2)), hglue⟩⟧, ?_⟩
      have e1 : crtFst M N h (e.symm (a.1.1, b.1.1)) = a.1.1 := by
        rw [crtFst_apply, RingEquiv.apply_symm_apply]
      have e2 : crtFst M N h (e.symm (a.1.2, b.1.2)) = a.1.2 := by
        rw [crtFst_apply, RingEquiv.apply_symm_apply]
      have e3 : crtSnd M N h (e.symm (a.1.1, b.1.1)) = b.1.1 := by
        rw [crtSnd_apply, RingEquiv.apply_symm_apply]
      have e4 : crtSnd M N h (e.symm (a.1.2, b.1.2)) = b.1.2 := by
        rw [crtSnd_apply, RingEquiv.apply_symm_apply]
      refine congrArg₂ Prod.mk (Quotient.sound ⟨1, ?_, ?_⟩) (Quotient.sound ⟨1, ?_, ?_⟩)
      · show (1 : ZMod M) * crtFst M N h (e.symm (a.1.1, b.1.1)) = a.1.1
        rw [one_mul, e1]
      · show (1 : ZMod M) * crtFst M N h (e.symm (a.1.2, b.1.2)) = a.1.2
        rw [one_mul, e2]
      · show (1 : ZMod N) * crtSnd M N h (e.symm (a.1.1, b.1.1)) = b.1.1
        rw [one_mul, e3]
      · show (1 : ZMod N) * crtSnd M N h (e.symm (a.1.2, b.1.2)) = b.1.2
        rw [one_mul, e4]
  rw [Nat.card_eq_of_bijective F hbij, Nat.card_prod]

end CRT



/-- The projective line over `ZMod N` has Dedekind psi many points. -/
theorem card_projectiveLine_zmod (N : ℕ) (hN : N ≠ 0) :
    Nat.card (ProjectiveLine (ZMod N)) = ArithmeticFunction.dedekindPsi N := by
  induction N using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp hn =>
      rw [card_projectiveLine_prime_pow p n hp hn.ne']
      obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
      have hpsi : ArithmeticFunction.dedekindPsi (p ^ (j + 1)) = p ^ j * (p + 1) := by
        rw [ArithmeticFunction.dedekindPsi_prime_pow hp (by omega)]
        simp
      rw [hpsi]; simp only [Nat.add_sub_cancel]; rw [pow_succ]; ring
  | zero => exact absurd rfl hN
  | one =>
      rw [ArithmeticFunction.dedekindPsi_one]
      have hrep : ∀ q : ProjectiveLine (ZMod 1),
          q = ⟦⟨((1 : ZMod 1), (0 : ZMod 1)), isUnimodularRow_one_left 0⟩⟧ := by
        intro q
        obtain ⟨v, rfl⟩ := Quotient.exists_rep q
        exact Quotient.sound ⟨1, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => (hrep a).trans (hrep b).symm⟩,
        ⟨⟦⟨((1 : ZMod 1), (0 : ZMod 1)), isUnimodularRow_one_left 0⟩⟧⟩⟩
  | coprime a b ha hb hab iha ihb =>
      haveI : NeZero a := ⟨by omega⟩
      haveI : NeZero b := ⟨by omega⟩
      rw [card_projectiveLine_mul a b hab, iha (by omega), ihb (by omega)]
      exact (ArithmeticFunction.isMultiplicative_dedekindPsi.map_mul_of_coprime hab).symm

section ArithmeticLemmas

private lemma natCast_dvd_int {p : ℕ} {z : ℤ} : (p : ℤ) ∣ z ↔ p ∣ z.natAbs :=
  Int.natCast_dvd

private def primeSel (c d : ℤ) : ℕ :=
  ∏ p ∈ c.natAbs.primeFactors, if p ∣ d.natAbs then 1 else p

private lemma dvd_primeSel {c d : ℤ} {p : ℕ} (hc : c ≠ 0) (hp : p.Prime)
    (hpc : (p : ℤ) ∣ c) (hpd : ¬(p : ℤ) ∣ d) : p ∣ primeSel c d := by
  have hmem : p ∈ c.natAbs.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, natCast_dvd_int.mp hpc, Int.natAbs_ne_zero.mpr hc⟩
  have h := Finset.dvd_prod_of_mem (fun q : ℕ => if q ∣ d.natAbs then 1 else q) hmem
  simp only [if_neg (fun hcontra => hpd (natCast_dvd_int.mpr hcontra))] at h
  exact h

private lemma not_dvd_primeSel {c d : ℤ} {p : ℕ} (hp : p.Prime) (hpd : (p : ℤ) ∣ d) :
    ¬p ∣ primeSel c d := by
  intro hdvd
  obtain ⟨q, hq, hpq⟩ := (Nat.Prime.prime hp).dvd_finsetProd_iff _ |>.mp hdvd
  by_cases hqd : q ∣ d.natAbs
  · rw [if_pos hqd] at hpq
    exact hp.one_lt.ne' (Nat.dvd_one.mp hpq)
  · rw [if_neg hqd] at hpq
    have hq' : q.Prime := (Nat.mem_primeFactors.mp hq).1
    exact hqd (((Nat.prime_dvd_prime_iff_eq hp hq').mp hpq) ▸ natCast_dvd_int.mp hpd)

private theorem exists_coprime_lift (N : ℕ) [NeZero N] {c₀ d₀ : ℤ}
    (H : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ c₀ → (p : ℤ) ∣ d₀ → ¬(p : ℤ) ∣ (N : ℤ)) :
    ∃ γ δ : ℤ, Int.gcd γ δ = 1 ∧
      (γ : ZMod N) = (c₀ : ZMod N) ∧ (δ : ZMod N) = (d₀ : ZMod N) := by
  set γ : ℤ := if c₀ = 0 then (N : ℤ) else c₀ with hγ_def
  have hγ0 : γ ≠ 0 := by
    rw [hγ_def]; split
    · exact_mod_cast NeZero.ne N
    · assumption
  have hγc : (γ : ZMod N) = (c₀ : ZMod N) := by
    rw [hγ_def]; split
    · next h => simp [h]
    · rfl
  have Hγ : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ γ → (p : ℤ) ∣ d₀ → ¬(p : ℤ) ∣ (N : ℤ) := by
    intro p pp hpγ hpd
    refine H p pp ?_ hpd
    rw [hγ_def] at hpγ
    by_cases h : c₀ = 0
    · simp [h]
    · rwa [if_neg h] at hpγ
  refine ⟨γ, d₀ + (primeSel γ d₀ : ℤ) * (N : ℤ), ?_, hγc, ?_⟩
  · by_contra hne
    obtain ⟨p, pp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
    have h1 : (p : ℤ) ∣ γ :=
      natCast_dvd_int.mpr (hpdvd.trans (Nat.gcd_dvd_left _ _))
    have h2 : (p : ℤ) ∣ d₀ + (primeSel γ d₀ : ℤ) * (N : ℤ) :=
      natCast_dvd_int.mpr (hpdvd.trans (Nat.gcd_dvd_right _ _))
    by_cases hpd : (p : ℤ) ∣ d₀
    · have h3 : (p : ℤ) ∣ (primeSel γ d₀ : ℤ) * (N : ℤ) := by
        have := h2.sub hpd; rwa [add_sub_cancel_left] at this
      have h3' : p ∣ primeSel γ d₀ * N := by
        have : (p : ℤ) ∣ ((primeSel γ d₀ * N : ℕ) : ℤ) := by push_cast; exact h3
        exact_mod_cast this
      rcases (pp.prime.dvd_mul.mp h3') with h4 | h4
      · exact not_dvd_primeSel pp hpd h4
      · exact Hγ p pp h1 hpd (by exact_mod_cast h4)
    · have h3 : (p : ℤ) ∣ (primeSel γ d₀ : ℤ) :=
        natCast_dvd_int.mpr (dvd_primeSel hγ0 pp h1 hpd)
      refine hpd ?_
      have := h2.sub (h3.mul_right (N : ℤ)); rwa [add_sub_cancel_right] at this
  · push_cast; simp

private theorem exists_sl2_int_lift {N : ℕ} [NeZero N] {a b c d : ZMod N}
    (h : a * d - b * c = 1) :
    ∃ α β γ δ : ℤ, α * δ - β * γ = 1 ∧
      (α : ZMod N) = a ∧ (β : ZMod N) = b ∧ (γ : ZMod N) = c ∧ (δ : ZMod N) = d := by
  set a₀ : ℤ := ZMod.cast a with ha₀
  set b₀ : ℤ := ZMod.cast b with hb₀
  set c₀ : ℤ := ZMod.cast c with hc₀
  set d₀ : ℤ := ZMod.cast d with hd₀
  have hcasta : ((a₀ : ℤ) : ZMod N) = a := ZMod.intCast_zmod_cast a
  have hcastb : ((b₀ : ℤ) : ZMod N) = b := ZMod.intCast_zmod_cast b
  have hcastc : ((c₀ : ℤ) : ZMod N) = c := ZMod.intCast_zmod_cast c
  have hcastd : ((d₀ : ℤ) : ZMod N) = d := ZMod.intCast_zmod_cast d
  have hdvd : (N : ℤ) ∣ a₀ * d₀ - b₀ * c₀ - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hcasta, hcastb, hcastc, hcastd]
    rw [sub_eq_zero]; exact h
  have H : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ c₀ → (p : ℤ) ∣ d₀ → ¬(p : ℤ) ∣ (N : ℤ) := by
    intro p pp hpc hpd hpN
    have hone : (p : ℤ) ∣ 1 := by
      have h1 : (p : ℤ) ∣ a₀ * d₀ - b₀ * c₀ - 1 := hpN.trans hdvd
      have h2 : (p : ℤ) ∣ a₀ * d₀ := hpd.mul_left a₀
      have h3 : (p : ℤ) ∣ b₀ * c₀ := hpc.mul_left b₀
      have key : (1 : ℤ) = a₀ * d₀ - b₀ * c₀ - (a₀ * d₀ - b₀ * c₀ - 1) := by ring
      rw [key]; exact (h2.sub h3).sub h1
    exact pp.one_lt.ne' (Nat.dvd_one.mp (by exact_mod_cast hone))
  obtain ⟨γ, δ, hγδ, hγ, hδ⟩ := exists_coprime_lift N H
  rw [hcastc] at hγ; rw [hcastd] at hδ
  set α₀ : ℤ := Int.gcdB γ δ with hα₀
  set β₀ : ℤ := -Int.gcdA γ δ with hβ₀
  have hdet₀ : α₀ * δ - β₀ * γ = 1 := by
    have hbez := Int.gcd_eq_gcd_ab γ δ
    rw [hγδ] at hbez; push_cast at hbez
    rw [hα₀, hβ₀]; linear_combination -hbez
  have hdet₀' : (α₀ : ZMod N) * d - (β₀ : ZMod N) * c = 1 := by
    have := congrArg (fun z : ℤ => (z : ZMod N)) hdet₀
    push_cast at this; rwa [hγ, hδ] at this
  set lam : ZMod N := b * (α₀ : ZMod N) - a * (β₀ : ZMod N) with hlam
  set l : ℤ := ZMod.cast lam with hl
  have hcastl : ((l : ℤ) : ZMod N) = lam := ZMod.intCast_zmod_cast lam
  refine ⟨α₀ + l * γ, β₀ + l * δ, γ, δ, ?_, ?_, ?_, hγ, hδ⟩
  · linear_combination hdet₀
  · push_cast; rw [hcastl, hγ, hlam]
    linear_combination (-(α₀ : ZMod N)) * h + a * hdet₀'
  · push_cast; rw [hcastl, hδ, hlam]
    linear_combination (-(β₀ : ZMod N)) * h + b * hdet₀'

end ArithmeticLemmas

private theorem sl2_surj (N : ℕ) [NeZero N] :
    Function.Surjective
      (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod N))) := by
  intro M
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    have hM := M.prop; rwa [Matrix.det_fin_two] at hM
  obtain ⟨α, β, γ, δ, h1, ha, hb, hc, hd⟩ := exists_sl2_int_lift hdet
  refine ⟨⟨!![α, β; γ, δ], by rw [Matrix.det_fin_two_of]; exact h1⟩, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simpa [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
      using ‹_›

section QuotientBorel
variable {R : Type*} [CommRing R]

private theorem isUnimodularRow_firstCol (A : SpecialLinearGroup (Fin 2) R) :
    IsUnimodularRow (A.1 0 0) (A.1 1 0) := by
  refine ⟨A.1 1 1, -A.1 0 1, ?_⟩
  have hdet : A.1 0 0 * A.1 1 1 - A.1 0 1 * A.1 1 0 = 1 := by
    have h := A.2; rwa [Matrix.det_fin_two] at h
  linear_combination hdet

private def firstColumnClass (A : SpecialLinearGroup (Fin 2) R) : ProjectiveLine R :=
  ⟦⟨(A.1 0 0, A.1 1 0), isUnimodularRow_firstCol A⟩⟧

private theorem firstColumnClass_eq_iff (A B : SpecialLinearGroup (Fin 2) R) :
    firstColumnClass A = firstColumnClass B ↔ A⁻¹ * B ∈ borel R := by
  constructor
  · intro hAB
    obtain ⟨u, h1, h2⟩ := Quotient.exact hAB
    have h1' : (u : R) * A.1 0 0 = B.1 0 0 := h1
    have h2' : (u : R) * A.1 1 0 = B.1 1 0 := h2
    show (A⁻¹ * B).1 1 0 = 0
    rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.SL2_inv_expl A,
      (Matrix.two_mul_expl _ B.1).2.2.1]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [← h1', ← h2']; ring
  · intro hAB
    have hB : B = A * (A⁻¹ * B) := (mul_inv_cancel_left A B).symm
    have hC10 : (A⁻¹ * B).1 1 0 = 0 := hAB
    have hCdet : (A⁻¹ * B).1 0 0 * (A⁻¹ * B).1 1 1 = 1 := by
      have h := (A⁻¹ * B).2; rw [Matrix.det_fin_two, hC10] at h; linear_combination h
    have hB00 : B.1 0 0 = A.1 0 0 * (A⁻¹ * B).1 0 0 + A.1 0 1 * (A⁻¹ * B).1 1 0 := by
      conv_lhs => rw [hB, SpecialLinearGroup.coe_mul]
      exact (Matrix.two_mul_expl A.1 (A⁻¹ * B).1).1
    have hB10 : B.1 1 0 = A.1 1 0 * (A⁻¹ * B).1 0 0 + A.1 1 1 * (A⁻¹ * B).1 1 0 := by
      conv_lhs => rw [hB, SpecialLinearGroup.coe_mul]
      exact (Matrix.two_mul_expl A.1 (A⁻¹ * B).1).2.2.1
    refine Quotient.sound ⟨⟨(A⁻¹ * B).1 0 0, (A⁻¹ * B).1 1 1, hCdet,
      (mul_comm _ _).trans hCdet⟩, ?_, ?_⟩
    · show (A⁻¹ * B).1 0 0 * A.1 0 0 = B.1 0 0; rw [hB00, hC10]; ring
    · show (A⁻¹ * B).1 0 0 * A.1 1 0 = B.1 1 0; rw [hB10, hC10]; ring

private theorem card_quotient_borel (R : Type*) [CommRing R] :
    Nat.card (SpecialLinearGroup (Fin 2) R ⧸ borel R) = Nat.card (ProjectiveLine R) := by
  have hwd : ∀ A B : SpecialLinearGroup (Fin 2) R, QuotientGroup.leftRel (borel R) A B →
      firstColumnClass A = firstColumnClass B := by
    intro A B hAB
    rw [QuotientGroup.leftRel_apply] at hAB
    exact (firstColumnClass_eq_iff A B).mpr hAB
  refine Nat.card_eq_of_bijective (fun q => Quotient.liftOn' q firstColumnClass hwd) ⟨?_, ?_⟩
  · intro q q'
    refine Quotient.inductionOn₂' q q' ?_
    intro A B hAB
    have hAB' : firstColumnClass A = firstColumnClass B := hAB
    exact (QuotientGroup.eq).mpr ((firstColumnClass_eq_iff A B).mp hAB')
  · intro q
    obtain ⟨v, rfl⟩ := Quotient.exists_rep q
    obtain ⟨x, y, hxy⟩ := v.2
    refine ⟨QuotientGroup.mk ⟨!![v.1.1, -y; v.1.2, x], by
      rw [Matrix.det_fin_two_of]; linear_combination hxy⟩, ?_⟩
    show firstColumnClass _ = ⟦v⟧
    refine Quotient.sound ⟨1, ?_, ?_⟩
    · show (1 : R) * !![v.1.1, -y; v.1.2, x] 0 0 = v.1.1; simp
    · show (1 : R) * !![v.1.1, -y; v.1.2, x] 1 0 = v.1.2; simp

end QuotientBorel

private theorem Gamma0_eq_comap_borel (N : ℕ) :
    Gamma0 N = (borel (ZMod N)).comap
      (SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod N))) := by
  ext A
  rw [Gamma0_mem, Subgroup.mem_comap, mem_borel_iff]
  constructor
  · intro hA
    show (Int.castRingHom (ZMod N)).mapMatrix A.1 1 0 = 0; simpa using hA
  · intro hA
    have hA' : (Int.castRingHom (ZMod N)).mapMatrix A.1 1 0 = 0 := hA; simpa using hA'



/-- The index of `Gamma0 N` in `SL(2, Z)` equals the Dedekind psi value. -/
theorem Gamma0_index (N : ℕ) [NeZero N] :
    (CongruenceSubgroup.Gamma0 N).index = ArithmeticFunction.dedekindPsi N := by
  have h1 : (CongruenceSubgroup.Gamma0 N).index = (borel (ZMod N)).index := by
    rw [Gamma0_eq_comap_borel]
    exact Subgroup.index_comap_of_surjective _ (sl2_surj N)
  rw [h1, Subgroup.index_eq_card, card_quotient_borel,
    card_projectiveLine_zmod N (NeZero.ne N)]

end ModularCurve

open scoped MatrixGroups in
/-- The cardinality of the quotient of the modular group by the image of
`Gamma0 N` equals the index of `Gamma0 N`. -/
theorem ModularCurve.card_quotient_gamma0_eq_index (N : ℕ) :
    Nat.card (𝒮ℒ ⧸ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ)
      (CongruenceSubgroup.Gamma0 N)).subgroupOf 𝒮ℒ) =
      (CongruenceSubgroup.Gamma0 N).index := by
  rw [← Subgroup.index_eq_card]
  show Subgroup.relIndex _ _ = _
  rw [MonoidHom.range_eq_map,
    Subgroup.relIndex_map_map_of_injective _ _
      Matrix.SpecialLinearGroup.mapGL_injective,
    Subgroup.relIndex_top_right]
