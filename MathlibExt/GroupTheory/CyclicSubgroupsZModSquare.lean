/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_ZMod_natCard_isAddCyclic_addSubgroup_prod_eq_dedekindPsi.lean`
and
`P2M/Sol/S_ZMod_natCard_isAddCyclic_addSubgroup_prod_eq_dedekindPsi.lean`
and
`Definitions/Def_ModularCurve_ProjectiveLine.lean`
and
`P2M/Sol/S_ModularCurve_card_projectiveLine_zmod.lean`
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

public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import MathlibExt.NumberTheory.ArithmeticFunction.DedekindPsi

import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.OrderOfElement

@[expose] public section

/-- A pair `(a, c)` in a commutative ring is a unimodular row if it generates
the unit ideal, i.e. there are `x y` with `x * a + y * c = 1`. -/
def IsUnimodularRow {R : Type*} [CommRing R] (a c : R) : Prop :=
  ∃ x y : R, x * a + y * c = 1

theorem isUnimodularRow_one_left {R : Type*} [CommRing R] (t : R) :
    IsUnimodularRow (1 : R) t :=
  ⟨1, 0, by simp⟩

theorem isUnimodularRow_one_right {R : Type*} [CommRing R] (m : R) :
    IsUnimodularRow m (1 : R) :=
  ⟨0, 1, by simp⟩

theorem IsUnimodularRow.map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) {a c : R} (h : IsUnimodularRow a c) :
    IsUnimodularRow (f a) (f c) := by
  obtain ⟨x, y, hxy⟩ := h
  exact ⟨f x, f y, by rw [← map_mul, ← map_mul, ← map_add, hxy, map_one]⟩

/-- Unimodular rows in a commutative ring. -/
abbrev UnimodularRow (R : Type*) [CommRing R] :=
  { v : R × R // IsUnimodularRow v.1 v.2 }

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

/-- The projective line over a commutative ring: unimodular rows modulo
scaling by a unit. -/
def ProjectiveLine (R : Type*) [CommRing R] : Type _ :=
  Quotient (unimodularRowSetoid R)

instance {R : Type*} [CommRing R] [Finite R] : Finite (ProjectiveLine R) :=
  Quotient.finite _

/-- The image of a projective-line point under a ring homomorphism. -/
def ProjectiveLine.map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) : ProjectiveLine R → ProjectiveLine S :=
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
theorem ProjectiveLine.map_mk {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (v : UnimodularRow R) :
    ProjectiveLine.map f ⟦v⟧ = ⟦⟨(f v.1.1, f v.1.2), v.2.map f⟩⟧ :=
  rfl

section OrderUnimodular

variable (N : ℕ)

private theorem nsmul_pair (n : ℕ) (x : ZMod N × ZMod N) :
    n • x = (n • x.1, n • x.2) :=
  Prod.ext (map_nsmul (AddMonoidHom.fst (ZMod N) (ZMod N)) n x)
    (map_nsmul (AddMonoidHom.snd (ZMod N) (ZMod N)) n x)

private theorem zsmul_pair_fst (k : ℤ) (x : ZMod N × ZMod N) :
    (k • x).1 = k • x.1 :=
  map_zsmul (AddMonoidHom.fst (ZMod N) (ZMod N)) k x

private theorem zsmul_pair_snd (k : ℤ) (x : ZMod N × ZMod N) :
    (k • x).2 = k • x.2 :=
  map_zsmul (AddMonoidHom.snd (ZMod N) (ZMod N)) k x

private theorem nsmul_eq_zero_of_dvd_mul_val {m : ℕ} {z : ZMod N} [NeZero N]
    (h : N ∣ m * z.val) : m • z = 0 :=
  calc m • z = (m : ZMod N) * z := nsmul_eq_mul m z
    _ = (m : ZMod N) * (z.val : ZMod N) := by rw [ZMod.natCast_zmod_val]
    _ = ((m * z.val : ℕ) : ZMod N) := (Nat.cast_mul _ _).symm
    _ = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h

variable [NeZero N]

theorem IsUnimodularRow.addOrderOf_eq {a c : ZMod N} (h : IsUnimodularRow a c) :
    addOrderOf ((a, c) : ZMod N × ZMod N) = N := by
  obtain ⟨x, y, hxy⟩ := h
  have hdvdN : addOrderOf ((a, c) : ZMod N × ZMod N) ∣ N := by
    refine addOrderOf_dvd_iff_nsmul_eq_zero.mpr ?_
    rw [nsmul_pair]
    have hza : N • a = 0 := by rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    have hzc : N • c = 0 := by rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    rw [hza, hzc]
    rfl
  have hN : N ∣ addOrderOf ((a, c) : ZMod N × ZMod N) := by
    have hsmul : addOrderOf ((a, c) : ZMod N × ZMod N) • ((a, c) : ZMod N × ZMod N) = 0 :=
      addOrderOf_nsmul_eq_zero _
    rw [nsmul_pair] at hsmul
    have ha : addOrderOf ((a, c) : ZMod N × ZMod N) • a = 0 := congrArg Prod.fst hsmul
    have hc : addOrderOf ((a, c) : ZMod N × ZMod N) • c = 0 := congrArg Prod.snd hsmul
    rw [nsmul_eq_mul] at ha hc
    have hzero : ((addOrderOf ((a, c) : ZMod N × ZMod N) : ℕ) : ZMod N) = 0 := by
      calc ((addOrderOf ((a, c) : ZMod N × ZMod N) : ℕ) : ZMod N)
          = (addOrderOf ((a, c) : ZMod N × ZMod N) : ZMod N) * (x * a + y * c) := by
            rw [hxy, mul_one]
        _ = x * ((addOrderOf ((a, c) : ZMod N × ZMod N) : ZMod N) * a)
              + y * ((addOrderOf ((a, c) : ZMod N × ZMod N) : ZMod N) * c) := by ring
        _ = 0 := by rw [ha, hc, mul_zero, mul_zero, add_zero]
    exact (ZMod.natCast_eq_zero_iff _ _).mp hzero
  exact Nat.dvd_antisymm hdvdN hN

theorem isUnimodularRow_of_addOrderOf_eq {a c : ZMod N}
    (h : addOrderOf ((a, c) : ZMod N × ZMod N) = N) : IsUnimodularRow a c := by
  have hN0 : N ≠ 0 := NeZero.ne N
  set d : ℕ := Nat.gcd (Nat.gcd a.val c.val) N with hd
  have hdN : d ∣ N := Nat.gcd_dvd_right _ _
  have hdA : d ∣ a.val := dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_left _ _)
  have hdC : d ∣ c.val := dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)
  have hd1 : d = 1 := by
    have hkill : (N / d) • ((a, c) : ZMod N × ZMod N) = 0 := by
      rw [nsmul_pair]
      have hka : (N / d) • a = 0 := by
        refine nsmul_eq_zero_of_dvd_mul_val N ?_
        obtain ⟨A', hA'⟩ := hdA
        exact ⟨A', by rw [hA', ← mul_assoc, Nat.div_mul_cancel hdN]⟩
      have hkc : (N / d) • c = 0 := by
        refine nsmul_eq_zero_of_dvd_mul_val N ?_
        obtain ⟨C', hC'⟩ := hdC
        exact ⟨C', by rw [hC', ← mul_assoc, Nat.div_mul_cancel hdN]⟩
      rw [hka, hkc]
      rfl
    have horder : addOrderOf ((a, c) : ZMod N × ZMod N) ∣ N / d :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mpr hkill
    rw [h] at horder
    have hdivdvd : N / d ∣ N := Nat.div_dvd_of_dvd hdN
    have hNd : N / d = N := Nat.dvd_antisymm hdivdvd horder
    have hmul : d * (N / d) = N := Nat.mul_div_cancel' hdN
    rw [hNd] at hmul
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hN0) (hmul.trans (one_mul N).symm)
  have hcop : Nat.Coprime (Nat.gcd a.val c.val) N := hd1
  have hunit : IsUnit ((Nat.gcd a.val c.val : ℕ) : ZMod N) :=
    (ZMod.isUnit_iff_coprime _ N).mpr hcop
  obtain ⟨u, hu⟩ := hunit
  have hbez := Nat.gcd_eq_gcd_ab a.val c.val
  have hcast : ((Nat.gcd a.val c.val : ℕ) : ZMod N)
      = a * ((Nat.gcdA a.val c.val : ℤ) : ZMod N)
        + c * ((Nat.gcdB a.val c.val : ℤ) : ZMod N) := by
    have hℤ := congrArg (fun z : ℤ => (Int.castRingHom (ZMod N)) z) hbez
    simp only [map_add, map_mul, Int.coe_castRingHom] at hℤ
    rw [Int.cast_natCast, Int.cast_natCast, Int.cast_natCast, ZMod.natCast_zmod_val,
      ZMod.natCast_zmod_val] at hℤ
    exact hℤ
  refine ⟨((Nat.gcdA a.val c.val : ℤ) : ZMod N) * (↑u⁻¹ : ZMod N),
    ((Nat.gcdB a.val c.val : ℤ) : ZMod N) * (↑u⁻¹ : ZMod N), ?_⟩
  calc ((Nat.gcdA a.val c.val : ℤ) : ZMod N) * (↑u⁻¹ : ZMod N) * a
        + ((Nat.gcdB a.val c.val : ℤ) : ZMod N) * (↑u⁻¹ : ZMod N) * c
      = (a * ((Nat.gcdA a.val c.val : ℤ) : ZMod N)
          + c * ((Nat.gcdB a.val c.val : ℤ) : ZMod N)) * (↑u⁻¹ : ZMod N) := by ring
    _ = ((Nat.gcd a.val c.val : ℕ) : ZMod N) * (↑u⁻¹ : ZMod N) := by rw [← hcast]
    _ = (↑u : ZMod N) * (↑u⁻¹ : ZMod N) := by rw [hu]
    _ = 1 := u.mul_inv

theorem isUnimodularRow_iff_addOrderOf_eq {a c : ZMod N} :
    IsUnimodularRow a c ↔ addOrderOf ((a, c) : ZMod N × ZMod N) = N :=
  ⟨IsUnimodularRow.addOrderOf_eq N, isUnimodularRow_of_addOrderOf_eq N⟩

end OrderUnimodular

section Scaling

variable (N : ℕ) [NeZero N]

theorem zmultiples_unit_mul (u : (ZMod N)ˣ) (x : ZMod N × ZMod N) :
    AddSubgroup.zmultiples ((((u : ZMod N) * x.1, (u : ZMod N) * x.2)) : ZMod N × ZMod N)
      = AddSubgroup.zmultiples x := by
  have key : ∀ (w : (ZMod N)ˣ) (y : ZMod N × ZMod N),
      (((w : ZMod N) * y.1, (w : ZMod N) * y.2) : ZMod N × ZMod N)
        ∈ AddSubgroup.zmultiples y := by
    intro w y
    refine AddSubgroup.mem_zmultiples_iff.mpr ⟨((w : ZMod N).val : ℤ), ?_⟩
    refine Prod.ext ?_ ?_
    · show ((((w : ZMod N).val : ℤ)) • y).1 = (w : ZMod N) * y.1
      rw [zsmul_pair_fst, zsmul_eq_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
    · show ((((w : ZMod N).val : ℤ)) • y).2 = (w : ZMod N) * y.2
      rw [zsmul_pair_snd, zsmul_eq_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
  refine le_antisymm (AddSubgroup.zmultiples_le.mpr (key u x))
    (AddSubgroup.zmultiples_le.mpr ?_)
  have hmem := key u⁻¹ (((u : ZMod N) * x.1, (u : ZMod N) * x.2) : ZMod N × ZMod N)
  have hx : ((((u⁻¹ : (ZMod N)ˣ) : ZMod N)
        * (((u : ZMod N) * x.1, (u : ZMod N) * x.2) : ZMod N × ZMod N).1,
      ((u⁻¹ : (ZMod N)ˣ) : ZMod N)
        * (((u : ZMod N) * x.1, (u : ZMod N) * x.2) : ZMod N × ZMod N).2)
        : ZMod N × ZMod N) = x := by
    have h1 : ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * ((u : ZMod N) * x.1) = x.1 := by
      rw [← mul_assoc, u.inv_mul, one_mul]
    have h2 : ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * ((u : ZMod N) * x.2) = x.2 := by
      rw [← mul_assoc, u.inv_mul, one_mul]
    exact Prod.ext h1 h2
  rwa [hx] at hmem

theorem eq_of_mul_unimodularRow_eq {a c : ZMod N} (h : IsUnimodularRow a c)
    {r s : ZMod N} (h1 : r * a = s * a) (h2 : r * c = s * c) : r = s := by
  obtain ⟨x, y, hxy⟩ := h
  calc r = r * (x * a + y * c) := by rw [hxy, mul_one]
    _ = x * (r * a) + y * (r * c) := by ring
    _ = x * (s * a) + y * (s * c) := by rw [h1, h2]
    _ = s * (x * a + y * c) := by ring
    _ = s := by rw [hxy, mul_one]

theorem IsUnimodularRow.unit_mul {a c : ZMod N} (h : IsUnimodularRow a c)
    (u : (ZMod N)ˣ) :
    IsUnimodularRow ((u : ZMod N) * a) ((u : ZMod N) * c) := by
  obtain ⟨x, y, hxy⟩ := h
  refine ⟨x * ((u⁻¹ : (ZMod N)ˣ) : ZMod N), y * ((u⁻¹ : (ZMod N)ˣ) : ZMod N), ?_⟩
  calc x * ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * ((u : ZMod N) * a)
        + y * ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * ((u : ZMod N) * c)
      = (((u⁻¹ : (ZMod N)ˣ) : ZMod N) * (u : ZMod N)) * (x * a)
          + (((u⁻¹ : (ZMod N)ˣ) : ZMod N) * (u : ZMod N)) * (y * c) := by ring
    _ = x * a + y * c := by rw [u.inv_mul, one_mul, one_mul]
    _ = 1 := hxy

end Scaling

section Bijection

variable (N : ℕ) [NeZero N]

/-- The cyclic subgroup generated by a unimodular row. -/
def unimodularRowToCyclicAddSubgroup (v : UnimodularRow (ZMod N)) :
    {H : AddSubgroup (ZMod N × ZMod N) // IsAddCyclic H ∧ Nat.card H = N} :=
  ⟨AddSubgroup.zmultiples v.1,
    (AddSubgroup.isAddCyclic_iff_exists_zmultiples_eq_top _).mpr ⟨v.1, rfl⟩,
    by rw [Nat.card_zmultiples, IsUnimodularRow.addOrderOf_eq N v.2]⟩

/-- The map from the projective line to cyclic subgroups of order `N`. -/
def projectiveLineToCyclicAddSubgroup :
    ProjectiveLine (ZMod N)
      → {H : AddSubgroup (ZMod N × ZMod N) // IsAddCyclic H ∧ Nat.card H = N} :=
  Quotient.lift (unimodularRowToCyclicAddSubgroup N) <| by
    rintro v w ⟨u, h1, h2⟩
    refine Subtype.ext ?_
    show AddSubgroup.zmultiples v.1 = AddSubgroup.zmultiples w.1
    have hw : w.1 = (((u : ZMod N) * v.1.1, (u : ZMod N) * v.1.2) : ZMod N × ZMod N) := by
      rw [h1, h2]
    rw [hw, zmultiples_unit_mul]

@[simp]
theorem projectiveLineToCyclicAddSubgroup_mk (v : UnimodularRow (ZMod N)) :
    projectiveLineToCyclicAddSubgroup N ⟦v⟧ = unimodularRowToCyclicAddSubgroup N v :=
  rfl

theorem projectiveLineToCyclicAddSubgroup_injective :
    Function.Injective (projectiveLineToCyclicAddSubgroup N) := by
  intro q₁ q₂
  refine Quotient.inductionOn₂ q₁ q₂ ?_
  intro v w hvw
  have hsub : AddSubgroup.zmultiples v.1 = AddSubgroup.zmultiples w.1 :=
    congrArg Subtype.val hvw
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp
    (hsub ▸ AddSubgroup.mem_zmultiples w.1)
  obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp
    (hsub.symm ▸ AddSubgroup.mem_zmultiples v.1)
  have hk1 : ((k : ZMod N)) * v.1.1 = w.1.1 := by
    have h := congrArg Prod.fst hk; rwa [zsmul_pair_fst, zsmul_eq_mul] at h
  have hk2 : ((k : ZMod N)) * v.1.2 = w.1.2 := by
    have h := congrArg Prod.snd hk; rwa [zsmul_pair_snd, zsmul_eq_mul] at h
  have hm1 : ((m : ZMod N)) * w.1.1 = v.1.1 := by
    have h := congrArg Prod.fst hm; rwa [zsmul_pair_fst, zsmul_eq_mul] at h
  have hm2 : ((m : ZMod N)) * w.1.2 = v.1.2 := by
    have h := congrArg Prod.snd hm; rwa [zsmul_pair_snd, zsmul_eq_mul] at h
  have hmk : ((m : ZMod N)) * ((k : ZMod N)) = 1 := by
    refine eq_of_mul_unimodularRow_eq N v.2 ?_ ?_
    · rw [mul_assoc, hk1, hm1, one_mul]
    · rw [mul_assoc, hk2, hm2, one_mul]
  refine Quotient.sound ⟨⟨(k : ZMod N), (m : ZMod N), by rw [mul_comm]; exact hmk, hmk⟩, ?_, ?_⟩
  · exact hk1
  · exact hk2

theorem projectiveLineToCyclicAddSubgroup_surjective :
    Function.Surjective (projectiveLineToCyclicAddSubgroup N) := by
  rintro ⟨H, hcyc, hcard⟩
  obtain ⟨g, hg⟩ := (AddSubgroup.isAddCyclic_iff_exists_zmultiples_eq_top H).mp hcyc
  have horder : addOrderOf g = N := by
    have h := Nat.card_zmultiples g
    rw [hg, hcard] at h
    exact h.symm
  have hrow : IsUnimodularRow g.1 g.2 := by
    refine isUnimodularRow_of_addOrderOf_eq N ?_
    have hg' : ((g.1, g.2) : ZMod N × ZMod N) = g := rfl
    rw [hg', horder]
  refine ⟨⟦⟨(g.1, g.2), hrow⟩⟧, ?_⟩
  refine Subtype.ext ?_
  show AddSubgroup.zmultiples ((g.1, g.2) : ZMod N × ZMod N) = H
  have hg' : ((g.1, g.2) : ZMod N × ZMod N) = g := rfl
  rw [hg', hg]

/-- The projective line over `ZMod N` is equivalent to the type of cyclic
subgroups of order `N` in `(ZMod N) × (ZMod N)`. -/
noncomputable def projectiveLineEquivCyclicAddSubgroup :
    ProjectiveLine (ZMod N)
      ≃ {H : AddSubgroup (ZMod N × ZMod N) // IsAddCyclic H ∧ Nat.card H = N} :=
  Equiv.ofBijective (projectiveLineToCyclicAddSubgroup N)
    ⟨projectiveLineToCyclicAddSubgroup_injective N,
      projectiveLineToCyclicAddSubgroup_surjective N⟩

end Bijection

section CardProjectiveLine

private theorem isUnit_zmod_prime_pow_iff {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0)
    (z : ZMod (p ^ k)) :
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

private theorem isUnimodularRow_isUnit_or_isUnit {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0)
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
  let f : ZMod (p ^ k) ⊕ { z : ZMod (p ^ k) // ¬IsUnit z }
      → ProjectiveLine (ZMod (p ^ k)) :=
    fun s => Sum.rec (fun t => ⟦⟨(1, t), isUnimodularRow_one_left t⟩⟧)
      (fun m => ⟦⟨(m.1, 1), isUnimodularRow_one_right m.1⟩⟧) s
  have hbij : Function.Bijective f := by
    constructor
    · rintro (t | m) (t' | m') hff
      · obtain ⟨u, h1, h2⟩ := Quotient.exact hff
        have h1' : (u : ZMod (p ^ k)) * 1 = 1 := h1
        have h2' : (u : ZMod (p ^ k)) * t = t' := h2
        rw [mul_one] at h1'
        rw [h1', one_mul] at h2'
        exact congrArg Sum.inl h2'
      · obtain ⟨u, h1, _⟩ := Quotient.exact hff
        have h1' : (u : ZMod (p ^ k)) * 1 = m'.1 := h1
        exact absurd (h1' ▸ (u.isUnit.mul isUnit_one)) m'.2
      · obtain ⟨u, h1, _⟩ := Quotient.exact hff
        have h1' : (u : ZMod (p ^ k)) * m.1 = 1 := h1
        exact absurd ⟨⟨m.1, u, (mul_comm m.1 u).trans h1', h1'⟩, rfl⟩ m.2
      · obtain ⟨u, h1, h2⟩ := Quotient.exact hff
        have h1' : (u : ZMod (p ^ k)) * m.1 = m'.1 := h1
        have h2' : (u : ZMod (p ^ k)) * 1 = 1 := h2
        rw [mul_one] at h2'
        rw [h2', one_mul] at h1'
        exact congrArg Sum.inr (Subtype.ext h1')
    · intro q
      obtain ⟨v, rfl⟩ := Quotient.exists_rep q
      by_cases ha : IsUnit v.1.1
      · refine ⟨Sum.inl ((ha.unit⁻¹ : (ZMod (p ^ k))ˣ) * v.1.2),
          Quotient.sound ⟨ha.unit, ?_, ?_⟩⟩
        · show (ha.unit : ZMod (p ^ k)) * 1 = v.1.1
          rw [mul_one, ha.unit_spec]
        · show (ha.unit : ZMod (p ^ k)) * ((ha.unit⁻¹ : (ZMod (p ^ k))ˣ) * v.1.2) = v.1.2
          rw [Units.mul_inv_cancel_left]
      · have hc : IsUnit v.1.2 := (isUnimodularRow_isUnit_or_isUnit hp hk v.2).resolve_left ha
        have hm : ¬IsUnit ((hc.unit⁻¹ : (ZMod (p ^ k))ˣ) * v.1.1) := fun hcon => by
          have hthis : IsUnit ((hc.unit : ZMod (p ^ k))
              * ((hc.unit⁻¹ : (ZMod (p ^ k))ˣ) * v.1.1)) :=
            hc.unit.isUnit.mul hcon
          rw [Units.mul_inv_cancel_left] at hthis
          exact ha hthis
        refine ⟨Sum.inr ⟨(hc.unit⁻¹ : (ZMod (p ^ k))ˣ) * v.1.1, hm⟩,
          Quotient.sound ⟨hc.unit, ?_, ?_⟩⟩
        · show (hc.unit : ZMod (p ^ k)) * ((hc.unit⁻¹ : (ZMod (p ^ k))ˣ) * v.1.1) = v.1.1
          rw [Units.mul_inv_cancel_left]
        · show (hc.unit : ZMod (p ^ k)) * 1 = v.1.2
          rw [mul_one, hc.unit_spec]
  rw [← Nat.card_eq_of_bijective f hbij, Nat.card_sum, Nat.card_eq_fintype_card, ZMod.card,
    card_not_isUnit_zmod_prime_pow hp hk]

end CardProjectiveLine

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

private theorem card_projectiveLine_mul (M N : ℕ) [NeZero M] [NeZero N]
    (h : M.Coprime N) :
    Nat.card (ProjectiveLine (ZMod (M * N))) =
      Nat.card (ProjectiveLine (ZMod M)) * Nat.card (ProjectiveLine (ZMod N)) := by
  haveI : NeZero (M * N) := ⟨mul_ne_zero (NeZero.ne M) (NeZero.ne N)⟩
  set e := ZMod.chineseRemainder h with he
  let F : ProjectiveLine (ZMod (M * N))
      → ProjectiveLine (ZMod M) × ProjectiveLine (ZMod N) :=
    fun q => (ProjectiveLine.map (crtFst M N h) q, ProjectiveLine.map (crtSnd M N h) q)
  have hbij : Function.Bijective F := by
    constructor
    · intro q q'
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
    · rintro ⟨x, y⟩
      obtain ⟨a, rfl⟩ := Quotient.exists_rep x
      obtain ⟨b, rfl⟩ := Quotient.exists_rep y
      obtain ⟨xa, ya, hab⟩ := a.2
      obtain ⟨xb, yb, hbb⟩ := b.2
      have hglue : IsUnimodularRow (e.symm (a.1.1, b.1.1)) (e.symm (a.1.2, b.1.2)) := by
        refine ⟨e.symm (xa, xb), e.symm (ya, yb), ?_⟩
        rw [← map_mul, ← map_mul, ← map_add, Prod.mk_mul_mk, Prod.mk_mul_mk,
          Prod.mk_add_mk, hab, hbb]
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

/-- The cardinality of the projective line over `ZMod N` is the Dedekind psi
function. -/
theorem card_projectiveLine_zmod (N : ℕ) (hN : N ≠ 0) :
    Nat.card (ProjectiveLine (ZMod N)) = ArithmeticFunction.dedekindPsi N := by
  induction N using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp hn =>
      rw [card_projectiveLine_prime_pow p n hp hn.ne']
      have hpsi := ArithmeticFunction.dedekindPsi_prime_pow hp hn
      rw [hpsi]
      rcases Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn) with ⟨j, rfl⟩
      simp [pow_succ]
      ring
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

/-- The number of cyclic subgroups of order `n` in `(ZMod n) × (ZMod n)` is
the Dedekind psi function `ψ(n)`. -/
theorem ZMod.natCard_isAddCyclic_addSubgroup_prod_eq_dedekindPsi
    (n : ℕ) [NeZero n] :
    Nat.card {H : AddSubgroup (ZMod n × ZMod n) // IsAddCyclic H ∧ Nat.card H = n}
      = ArithmeticFunction.dedekindPsi n := by
  rw [← card_projectiveLine_zmod n (NeZero.ne n)]
  exact (Nat.card_congr (projectiveLineEquivCyclicAddSubgroup n)).symm
