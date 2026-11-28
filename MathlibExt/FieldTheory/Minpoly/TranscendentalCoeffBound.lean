/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Polynomial_natDegree_aeval_symm_minpoly_adjoin_coeff_le_of_transcendental.lean`
and
`P2M/Sol/S_Polynomial_natDegree_aeval_symm_minpoly_adjoin_coeff_le_of_transcendental.lean`
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

public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Valuation.LocalSubring

@[expose] public section

open Polynomial
open scoped IntermediateField.algebraAdjoinAdjoin

private theorem isIntegrallyClosed_adjoin_singleton_of_transcendental_aux
    {L : Type*} [Field L] {F : Type*} [CommRing F] [IsDomain F] [Algebra L F]
    (x : F) (hxL : Transcendental L x) :
    IsIntegrallyClosed (Algebra.adjoin L ({x} : Set F)) := by
  classical
  have hinj : Function.Injective (Polynomial.aeval (R := L) x) :=
    transcendental_iff_injective.mp hxL
  have hrange : (Polynomial.aeval (R := L) x).range = Algebra.adjoin L ({x} : Set F) :=
    (Algebra.adjoin_singleton_eq_range_aeval L x).symm
  let e : Polynomial L ≃ₐ[L] Algebra.adjoin L ({x} : Set F) :=
    (AlgEquiv.ofInjective (Polynomial.aeval (R := L) x) hinj).trans
      (Subalgebra.equivOfEq _ _ hrange)
  haveI : IsPrincipalIdealRing (Algebra.adjoin L ({x} : Set F)) := by
    constructor
    intro I
    obtain ⟨a, ha⟩ := IsPrincipalIdealRing.principal (I.comap e.toRingHom)
    refine ⟨e a, ?_⟩
    show I = Ideal.span {e a}
    rw [← Ideal.map_comap_of_surjective e.toRingHom e.surjective I,
      show Ideal.comap e.toRingHom I = Ideal.span {a} from ha,
      Ideal.map_span, Set.image_singleton]
    rfl
  infer_instance

private theorem natDegree_le_of_aeval_mul_inv_pow_mem_adjoin_inv_aux
    {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F]
    (x : F) (hxL : Transcendental L x) (hx0 : x ≠ 0)
    (c : Polynomial L) (n : ℕ)
    (h : Polynomial.aeval x c * (x ^ n)⁻¹ ∈ Algebra.adjoin L ({x⁻¹} : Set F)) :
    c.natDegree ≤ n := by
  classical
  by_cases hc0 : c = 0
  · simp [hc0]
  rw [Algebra.adjoin_singleton_eq_range_aeval L x⁻¹, AlgHom.mem_range] at h
  obtain ⟨p, hp⟩ := h
  set N : ℕ := max n p.natDegree with hN
  have hnN : n ≤ N := le_max_left _ _
  have hpN : p.natDegree ≤ N := le_max_right _ _
  haveI : Invertible (x⁻¹) := invertibleOfNonzero (inv_ne_zero hx0)
  have hxinvinv : ⅟(x⁻¹) = x := by rw [invOf_eq_inv, inv_inv]
  have hrefl : Polynomial.aeval x (p.reflect N) * (x⁻¹) ^ N = Polynomial.aeval x⁻¹ p := by
    rw [Polynomial.aeval_def, Polynomial.aeval_def]
    have := Polynomial.eval₂_reflect_mul_pow (algebraMap L F) x⁻¹ N p hpN
    rwa [hxinvinv] at this
  have heq : Polynomial.aeval x (p.reflect N) =
      Polynomial.aeval x (c * Polynomial.X ^ (N - n)) := by
    have hxN0 : (x ^ N : F) ≠ 0 := pow_ne_zero N hx0
    have h1 : Polynomial.aeval x (p.reflect N) * (x⁻¹) ^ N * x ^ N =
        Polynomial.aeval x c * (x ^ n)⁻¹ * x ^ N := by rw [hrefl, hp]
    rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ hx0, one_pow, mul_one] at h1
    rw [h1, map_mul, Polynomial.aeval_X_pow, mul_assoc, mul_comm ((x ^ n)⁻¹) (x ^ N),
      ← pow_sub₀ x hx0 hnN]
  have hpoly : p.reflect N = c * Polynomial.X ^ (N - n) :=
    (transcendental_iff_injective.mp hxL) heq
  have hdeg : c.natDegree + (N - n) ≤ N := by
    have hXne : (Polynomial.X : Polynomial L) ^ (N - n) ≠ 0 :=
      pow_ne_zero _ Polynomial.X_ne_zero
    calc c.natDegree + (N - n)
        = (c * Polynomial.X ^ (N - n)).natDegree := by
          rw [Polynomial.natDegree_mul hc0 hXne, Polynomial.natDegree_X_pow]
      _ = (p.reflect N).natDegree := by rw [hpoly]
      _ ≤ max N p.natDegree := Polynomial.natDegree_reflect_le
      _ = N := max_eq_left hpN
  omega

/-- Bound on the degree of a polynomial representing a minimal-polynomial
coefficient over a transcendental adjunction.

Let `x` be a nonzero transcendental element of a field extension `F / L`,
let `f` be integral over `L[x]`, and suppose `f / x ^ m` lies in every
valuation subring of `F` that contains `L` but not `x`. If a polynomial
`c` over `L` evaluates at `x` to the `j`-th coefficient of the minimal
polynomial of `f` over `L[x]`, then the natural degree of `c` is at most
`(natDegree (minpoly L[x] f) - j) * m`, with truncated subtraction. -/
public theorem Polynomial.natDegree_aeval_symm_minpoly_adjoin_coeff_le_of_transcendental
    {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F]
    (x : F) (hxL : Transcendental L x) (hx0 : x ≠ 0)
    (f : F) (hint : IsIntegral (Algebra.adjoin L ({x} : Set F)) f) (m : ℕ)
    (h₂ : ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → x ∉ V →
      f * (x ^ m)⁻¹ ∈ V)
    (j : ℕ) (c : Polynomial L)
    (hc : Polynomial.aeval x c =
      (((minpoly (Algebra.adjoin L ({x} : Set F)) f).coeff j :
        Algebra.adjoin L ({x} : Set F)) : F)) :
    c.natDegree ≤ ((minpoly (Algebra.adjoin L ({x} : Set F)) f).natDegree - j) * m := by
  classical
  set q : Polynomial (Algebra.adjoin L ({x} : Set F)) :=
    minpoly (Algebra.adjoin L ({x} : Set F)) f with hq
  set d : ℕ := q.natDegree with hd
  set n : ℕ := (d - j) * m with hn
  set y : F := x⁻¹ with hy
  have hy0 : y ≠ 0 := inv_ne_zero hx0
  have hyL : Transcendental L y := by
    intro ⟨p, hp0, hpy⟩
    refine hxL ⟨p.reflect p.natDegree, fun h => hp0 (Polynomial.reflect_eq_zero_iff.mp h), ?_⟩
    haveI : Invertible y := invertibleOfNonzero hy0
    rw [Polynomial.aeval_def, show x = ⅟y by rw [invOf_eq_inv, hy, inv_inv],
      Polynomial.eval₂_reflect_eq_zero_iff (algebraMap L F) y p.natDegree p (le_refl _),
      ← Polynomial.aeval_def]
    exact hpy
  set g : F := f * (x ^ m)⁻¹ with hg
  haveI hICx : IsIntegrallyClosed (Algebra.adjoin L ({x} : Set F)) :=
    isIntegrallyClosed_adjoin_singleton_of_transcendental_aux x hxL
  haveI hICy : IsIntegrallyClosed (Algebra.adjoin L ({y} : Set F)) :=
    isIntegrallyClosed_adjoin_singleton_of_transcendental_aux y hyL
  have hfallV : ∀ V : ValuationSubring F,
      (Algebra.adjoin L ({x} : Set F) : Set F) ⊆ (V : Set F) → f ∈ V := by
    intro V hLxV
    have hiInf := iInf_valuationSubring_superset (K := F)
      (s := ((Algebra.adjoin L ({x} : Set F)).toSubring : Set F))
    rw [Subring.closure_eq] at hiInf
    have hfmem : f ∈ (integralClosure
        (Algebra.adjoin L ({x} : Set F)).toSubring F).toSubring := hint
    rw [← hiInf] at hfmem
    exact (Subring.mem_iInf.mp hfmem) ⟨V, hLxV⟩
  have hgint : IsIntegral (Algebra.adjoin L ({y} : Set F)) g := by
    set s : Set F := Set.range (algebraMap L F) ∪ {y} with hsdef
    have hmem : g ∈ (integralClosure (Subring.closure s) F).toSubring := by
      rw [← iInf_valuationSubring_superset]
      simp only [Subring.mem_iInf]
      rintro ⟨V, hsV⟩
      have hLV : ∀ a : L, algebraMap L F a ∈ V := fun a => hsV (Or.inl ⟨a, rfl⟩)
      have hyV : y ∈ V := hsV (Or.inr rfl)
      by_cases hxV : x ∈ V
      · have hLxV : (Algebra.adjoin L ({x} : Set F) : Set F) ⊆ (V : Set F) := by
          show ((Algebra.adjoin L ({x} : Set F)).toSubring : Set F) ⊆ (V : Set F)
          rw [← (Algebra.adjoin_eq_ring_closure ({x} : Set F)).symm]
          exact Subring.closure_le.mpr (Set.union_subset
            (Set.range_subset_iff.mpr hLV) (Set.singleton_subset_iff.mpr hxV))
        have hfV : f ∈ V := hfallV V hLxV
        have hxmV : (x ^ m)⁻¹ ∈ V := by
          rw [← inv_pow, ← hy]; exact pow_mem hyV m
        exact mul_mem hfV hxmV
      · exact h₂ V hLV hxV
    have hcls : Subring.closure s = (Algebra.adjoin L ({y} : Set F)).toSubring :=
      (Algebra.adjoin_eq_ring_closure _).symm
    refine (hmem : IsIntegral (Subring.closure s) g).map_of_comp_eq
      (Subring.inclusion hcls.le) (RingHom.id F) ?_
    ext a; exact (Subring.coe_inclusion hcls.le a).symm
  have hxK : x ∈ IntermediateField.adjoin L ({y} : Set F) := by
    rw [show x = y⁻¹ from (inv_inv x).symm ▸ congrArg Inv.inv hy.symm]
    exact inv_mem (IntermediateField.mem_adjoin_simple_self L y)
  have hyKx : y ∈ IntermediateField.adjoin L ({x} : Set F) := by
    rw [hy]; exact inv_mem (IntermediateField.mem_adjoin_simple_self L x)
  have hKeq : IntermediateField.adjoin L ({x} : Set F) =
      IntermediateField.adjoin L ({y} : Set F) :=
    le_antisymm
      (IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hxK))
      (IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hyKx))
  have hmpgLy : ∀ i, ((minpoly (IntermediateField.adjoin L ({y} : Set F)) g).coeff i : F) ∈
      Algebra.adjoin L ({y} : Set F) := by
    intro i
    have heq := minpoly.isIntegrallyClosed_eq_field_fractions'
      (R := Algebra.adjoin L ({y} : Set F)) (IntermediateField.adjoin L ({y} : Set F)) hgint
    rw [heq, Polynomial.coeff_map]
    exact ((minpoly (Algebra.adjoin L ({y} : Set F)) g).coeff i).2
  have hmpfq : minpoly (IntermediateField.adjoin L ({x} : Set F)) f =
      q.map (algebraMap (Algebra.adjoin L ({x} : Set F))
        (IntermediateField.adjoin L ({x} : Set F))) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' _ hint
  have hmpfd : (minpoly (IntermediateField.adjoin L ({x} : Set F)) f).natDegree = d := by
    rw [hmpfq, (minpoly.monic hint).natDegree_map, hd]
  have hxKmem : x ∈ IntermediateField.adjoin L ({x} : Set F) :=
    IntermediateField.mem_adjoin_simple_self L x
  set xK : IntermediateField.adjoin L ({x} : Set F) := ⟨x, hxKmem⟩ with hxK
  have hxK0 : xK ≠ 0 := fun h => hx0 (congrArg Subtype.val h)
  have hgsmul : g = (xK ^ m)⁻¹ • f := by
    rw [hg, Algebra.smul_def, map_inv₀, map_pow, mul_comm]
    rfl
  have hfintK : IsIntegral (IntermediateField.adjoin L ({x} : Set F)) f := hint.tower_top
  have hmpg_scale : minpoly (IntermediateField.adjoin L ({x} : Set F)) g =
      (minpoly (IntermediateField.adjoin L ({x} : Set F)) f).scaleRoots ((xK ^ m)⁻¹) := by
    rw [hgsmul]
    exact IsIntegrallyClosed.minpoly_smul (inv_ne_zero (pow_ne_zero m hxK0)) hfintK
  have hcoefj : (minpoly (IntermediateField.adjoin L ({x} : Set F)) g).coeff j =
      (minpoly (IntermediateField.adjoin L ({x} : Set F)) f).coeff j *
        ((xK ^ m)⁻¹) ^ (d - j) := by
    rw [hmpg_scale, Polynomial.coeff_scaleRoots, hmpfd]
  have hcoefF : ((minpoly (IntermediateField.adjoin L ({x} : Set F)) g).coeff j : F) =
      ((q.coeff j : Algebra.adjoin L ({x} : Set F)) : F) * (x ^ n)⁻¹ := by
    have hcast1 : ((minpoly (IntermediateField.adjoin L ({x} : Set F)) f).coeff j : F) =
        ((q.coeff j : Algebra.adjoin L ({x} : Set F)) : F) := by
      rw [hmpfq, Polynomial.coeff_map]; rfl
    have hcast2 : (((xK ^ m)⁻¹ ^ (d - j) :
        IntermediateField.adjoin L ({x} : Set F)) : F) = (x ^ n)⁻¹ := by
      push_cast
      rw [show ((xK : IntermediateField.adjoin L ({x} : Set F)) : F) = x from rfl,
        ← inv_pow, ← pow_mul, hn, mul_comm m (d - j), inv_pow]
    calc ((minpoly (IntermediateField.adjoin L ({x} : Set F)) g).coeff j : F)
        = ((minpoly (IntermediateField.adjoin L ({x} : Set F)) f).coeff j : F) *
            (((xK ^ m)⁻¹ ^ (d - j) : IntermediateField.adjoin L ({x} : Set F)) : F) := by
          rw [hcoefj]; push_cast; ring
      _ = ((q.coeff j : Algebra.adjoin L ({x} : Set F)) : F) * (x ^ n)⁻¹ := by
          rw [hcast1, hcast2]
  have hkey : ((q.coeff j : Algebra.adjoin L ({x} : Set F)) : F) * (x ^ n)⁻¹ ∈
      Algebra.adjoin L ({y} : Set F) := by
    rw [← hcoefF, hKeq]
    exact hmpgLy j
  rw [← hc] at hkey
  have hy2 : ({x⁻¹} : Set F) = {y} := by rw [hy]
  rw [← hy2] at hkey
  exact natDegree_le_of_aeval_mul_inv_pow_mem_adjoin_inv_aux x hxL hx0 c n hkey
