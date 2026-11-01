/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Dimension.PolynomialCatenary
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.Antidiag.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
import Mathlib.Data.ENat.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finsupp.Order
import Mathlib.Data.Finsupp.Single
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Operations
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Order.WithBot
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Ideal.Defs
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Nullstellensatz

/-!
# Curve-meets-hyperplane lane (scoped hPDT resolution)

Goal: discharge-or-narrow the `MeetsInfinity` residual consumed by
`Geometry/AffineFinite.lean` (`affineZero_finite_of_meetsInfinity`, tex Lemma
`Zfinite` via Corollary `meetshyperplane`), scoped to exactly that shape and
without general PDT/closure/scheme APIs (all grep-verified absent from Mathlib
v4.34.0: `dehomog`, `catenary`, projective dimension theorem).

## Findings

* (§1) `MeetsInfinity` as stated is false: `meetsInfinity_ofLinear_false`
  refutes it at `F i = X i` (linear, non-homogeneous input): then
  `chartPoly = 0`, the affine quotient is the full polynomial ring
  (`ringKrullDim = m + 1 ≥ 1` via `PolynomialCatenary.mvPolynomial_ringKrullDim`),
  while the conclusion asks for a nonzero vector vanishing on all coordinates.
  The residual must carry the homogeneity hypothesis (`hFhom` shape, as
  threaded by `MkSystemChart`) to be true. Status: unconditional (refutation
  with witness — first-class per).
* (§§2–4) The corrected shape (plus `∀ i, (F i).IsHomogeneous 2` and the
  global `[IsAlgClosed K]` needed by the Nullstellensatz) is true, by
  an elementary route that avoids PDT/closure/DVR entirely:
  contrapositive via the Nullstellensatz (`Xⱼ^e ∈ (Fᵢ)`), homogeneous
  refinement of the Nullstellensatz cofactors (graded collapse at degree 2),
  degree reduction to a finite monomial spanning set, hence a finite
  `K`-module, hence Artinian, hence `KrullDimLE 0`.
* The suggested DVR/normalization line was surveyed and not taken:
  `IsDiscreteValuationRing` (`.../DiscreteValuationRing/Basic.lean`,
  `irreducible_iff_uniformizer`, `addVal_*`) and
  `IsIntegralClosure.isDedekindDomain`
  (`.../DedekindDomain/IntegralClosure.lean`) exist, but reaching them from a
  positive-dimensional quotient needs finiteness of normalization plus a
  Dedekind-dimension bridge plus a valuation-center ("zero of the hyperplane
  form") step, none of which exists in-tree. The Nullstellensatz route
  below is shorter and closes unconditionally.

## What this file proves

* §1: mirrored `MeetsInfinity` shape (by-name citation of
  `AffineFinite.MeetsInfinity`, never imported) + `meetsInfinity_ofLinear_false`
  (refutation at `F = X`).
* §2: `pow_mem_span_of_no_nonzero_common_zero` — Nullstellensatz power
  relations `Xⱼ ^ eⱼ ∈ span (range F)` from "no nonzero common zero".
* §3: `refined_pow_relation` — homogeneous refinement: the cofactors can be
  taken homogeneous of degree `eⱼ - 2` (with `eⱼ ≥ 2`), via the graded
  collapse lemmas `homogComp_mul_right_collapse` / `homogComp_mul_right_vanish`.
* §4: `meetsInfinity_of_isHomogeneous` — the corrected end-to-end shape:
  `(hF : ∀ i, (F i).IsHomogeneous 2) → [IsAlgClosed K] → MeetsInfinity`,
  via finite monomial spanning (`Module.Finite` of the affine quotient),
  `IsArtinianRing.of_finite`, and `Ring.KrullDimLE.mk₀`.

## Status

* `AffineFinite.MeetsInfinity` as stated: false (`meetsInfinity_ofLinear_false`).
* Corrected shape (this file's `CurveMeet.MeetsInfinity` + `hFhom` +
  `[IsAlgClosed K]`): unconditional (`meetsInfinity_of_isHomogeneous`).
* Consumer note: `affineZero_finite_of_meetsInfinity` can thread `hFhom`
  (available in `MkSystemChart`) and `[IsAlgClosed K]` (global, cf.
  `Statement.Statement.bezout_quadratic`) to use the corrected shape; that glue is
  left to downstream assembly and is not done here (this file is a leaf).

## DAG safety

Imports only `Dimension.PolynomialCatenary` (for `mvPolynomial_ringKrullDim`, used in
§1) plus narrow Mathlib modules. Never imports `Statement.Statement`,
`Geometry.Counting`, `Geometry.ProjectiveLocus`, `Geometry.AffineFinite`,
`Geometry.MkSystemChart`, or any `Bridge` file: the `MeetsInfinity`/`chartPoly`
shapes are mirrored under the `CurveMeet` namespace with by-name citations
(per the `MkSystemChart` precedent), so a future `AffineFinite → this file`
edge creates no cycle. Transfer of the mirrored statements to the originals is
by definitional unfolding (plain defs, `exact`-up-to-defeq). No other file
imports this one.

## References

Mathlib v4.34.0 (exact module paths and declaration names, each grep-verified
in-tree) is cited per declaration below.

## Standing context (routine binders)

Named once here; per-decl docstrings below repeat GRADE verdicts and name only
substantive non-routine premises.

* `hF`/`hFhom : ∀ i, (F i).IsHomogeneous 2` — quadratic input forms (the
  §1 refutation shows the un-homogeneous shape is false).
* `[IsAlgClosed K]` — global instance feeding the Nullstellensatz
  (§2 power relations).
* `Module.Finite` — finite monomial spanning of the affine quotient (§4).
* `[Fintype α]` — at `exists_coord_ge_of_degree_ge` only.
* `[Field K]` throughout.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace CurveMeet

/-! ## §1 Mirrored shape + refutation of `MeetsInfinity` as stated -/

/-- Mirror of `MkSystemChart.chartPoly` (`qᵢ(u) = Fᵢ(u) − uᵢ`), cited by name
and never imported (see the module docstring's DAG note). -/
noncomputable def chartPoly (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (i : Fin (m + 1)) : MvPolynomial (Fin (m + 1)) K :=
  F i - MvPolynomial.X i

/-- Mirror of `AffineFinite.MeetsInfinity` (the exact end-to-end hPDT residual:
positive-dimensional affine `chartPoly` quotient forces a nonzero common zero
of the input forms), cited by name and never imported. -/
def MeetsInfinity (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K) : Prop :=
  ¬ Ring.KrullDimLE 0
      (MvPolynomial (Fin (m + 1)) K ⧸
        Ideal.span (Set.range (chartPoly m K F))) →
    ∃ v : Fin (m + 1) → K, v ≠ 0 ∧ ∀ i, MvPolynomial.eval v (F i) = 0

/-- A positive-degree homogeneous polynomial vanishes at the origin (via
`eval_zero` + `constantCoeff`; the constant coefficient has degree `0 ≠ 2`).

## References

* `Mathlib/Algebra/MvPolynomial/Eval.lean`, `MvPolynomial.eval_zero`.
* `Mathlib/Algebra/MvPolynomial/Basic.lean`, `MvPolynomial.constantCoeff_eq`.
* `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`,
  `MvPolynomial.IsHomogeneous.coeff_eq_zero`. -/
theorem eval_zero_of_isHomogeneous_two {σ : Type*} {K : Type*} [Field K]
    {p : MvPolynomial σ K} (hp : p.IsHomogeneous 2) :
    MvPolynomial.eval 0 p = 0 := by
  rw [MvPolynomial.eval_zero, MvPolynomial.constantCoeff_eq]
  exact hp.coeff_eq_zero (by simp)

/-- The polynomial ring in `m + 1 ≥ 1` variables is positive-dimensional.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Dimension.PolynomialCatenary`,
  `Appendix_FixedPoint.BezoutChain.mvPolynomial_ringKrullDim`.
* `Mathlib/RingTheory/KrullDimension/Basic.lean`, `Ring.krullDimLE_iff`. -/
theorem not_krullDimLE_zero_mvPolynomial (m : ℕ) (K : Type*) [Field K] :
    ¬ Ring.KrullDimLE 0 (MvPolynomial (Fin (m + 1)) K) := by
  rw [Ring.krullDimLE_iff, mvPolynomial_ringKrullDim]
  intro hle
  have hN : m + 1 ≤ 0 := by exact_mod_cast hle
  omega

/-- At linear input `F i = X i`, the `chartPoly` family is identically zero,
so its span is `⊥`.

## References

* `Mathlib/Algebra/Module/Submodule/Basic.lean`, `Submodule.span_le`
  (used via `Ideal.span_le`). -/
theorem span_chartPoly_X_eq_bot (m : ℕ) (K : Type*) [Field K] :
    Ideal.span (Set.range
      (chartPoly m K (fun i => MvPolynomial.X i))) = ⊥ := by
  have hrange : Set.range (chartPoly m K (fun i => MvPolynomial.X i)) = {0} := by
    ext y
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      change MvPolynomial.X i - MvPolynomial.X i = 0
      exact sub_self _
    · intro hy
      rw [hy]
      exact ⟨⟨0, Nat.zero_lt_succ m⟩, sub_self _⟩
  rw [hrange]
  apply le_antisymm _ bot_le
  rw [Ideal.span_le]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  rw [hy]
  exact Submodule.zero_mem ⊥

/-- Refutation of `MeetsInfinity` as stated: at `F i = X i` the quotient is the
full polynomial ring (positive-dimensional by `mvPolynomial_ringKrullDim`)
while the conclusion demands a nonzero all-zero vector.


## References

* This module, `CurveMeet.not_krullDimLE_zero_mvPolynomial`,
  `CurveMeet.span_chartPoly_X_eq_bot`.
* `Mathlib/RingTheory/KrullDimension/Basic.lean`, `Ring.krullDimLE_iff`,
  `ringKrullDim_eq_of_ringEquiv`.
* `Mathlib/RingTheory/Ideal/Quotient/Operations.lean`,
  `RingEquiv.quotientBot`.
* `Mathlib/Algebra/MvPolynomial/Eval.lean`, `MvPolynomial.eval_X`. -/
theorem meetsInfinity_ofLinear_false (m : ℕ) (K : Type*) [Field K] :
    ¬ MeetsInfinity m K (fun i => MvPolynomial.X i) := by
  unfold MeetsInfinity
  intro h
  have hspan := span_chartPoly_X_eq_bot m K
  have heq : ringKrullDim
        (MvPolynomial (Fin (m + 1)) K ⧸ (⊥ : Ideal (MvPolynomial (Fin (m + 1)) K)))
        = ringKrullDim (MvPolynomial (Fin (m + 1)) K) :=
    ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _)
  have hpos : ¬ Ring.KrullDimLE 0
      (MvPolynomial (Fin (m + 1)) K ⧸
        Ideal.span (Set.range (chartPoly m K (fun i => MvPolynomial.X i)))) := by
    rw [hspan, Ring.krullDimLE_iff, heq, ← Ring.krullDimLE_iff]
    exact not_krullDimLE_zero_mvPolynomial m K
  have hfalse : ¬ ∃ v : Fin (m + 1) → K,
      v ≠ 0 ∧ ∀ i, MvPolynomial.eval v ((fun i => MvPolynomial.X i) i) = 0 := by
    rintro ⟨v, hv, hh⟩
    apply hv
    funext i
    simpa [MvPolynomial.eval_X] using hh i
  exact hfalse (h hpos)

/-! ## §2 Nullstellensatz power relations

Under quadric homogeneity, "no nonzero common zero" forces the joint zero
locus to be exactly `{0}`; the Nullstellensatz then puts every variable in the
radical, i.e. some power of each variable lies in the span of the forms. -/

/-- With no nonzero common zero, the joint zero locus is exactly `{0}`
(the origin always lies there by homogeneity).

## References

* `Mathlib/RingTheory/Nullstellensatz.lean`, `MvPolynomial.zeroLocus_span`.
* `Mathlib/Algebra/MvPolynomial/Eval.lean`, `MvPolynomial.aeval_eq_eval`.
* This module, `CurveMeet.eval_zero_of_isHomogeneous_two`. -/
theorem zeroLocus_span_range_eq_singleton_zero (m : ℕ) (K : Type*) [Field K]
    [IsAlgClosed K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2)
    (hno : ∀ v : Fin (m + 1) → K,
      (∀ i, MvPolynomial.eval v (F i) = 0) → v = 0) :
    MvPolynomial.zeroLocus K (Ideal.span (Set.range F)) = {0} := by
  rw [MvPolynomial.zeroLocus_span]
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · intro h
    apply hno
    intro i
    have hi := h _ ⟨i, rfl⟩
    simp only [MvPolynomial.aeval_eq_eval] at hi
    exact hi
  · intro hx
    rw [hx]
    intro p hp
    obtain ⟨i, rfl⟩ := hp
    simp only [MvPolynomial.aeval_eq_eval]
    exact eval_zero_of_isHomogeneous_two (hF i)

/-- Nullstellensatz power relations: some power of each variable lies in the
span of the forms.

## References

* This module, `CurveMeet.zeroLocus_span_range_eq_singleton_zero`.
* `Mathlib/RingTheory/Nullstellensatz.lean`,
  `MvPolynomial.mem_vanishingIdeal_singleton_iff`,
  `MvPolynomial.vanishingIdeal_zeroLocus_eq_radical`.
* `Mathlib/Algebra/MvPolynomial/Eval.lean`, `MvPolynomial.aeval_eq_eval`,
  `MvPolynomial.eval_X`.
* `Mathlib/RingTheory/Ideal/Operations.lean`, `Ideal.mem_radical_iff`. -/
theorem pow_mem_span_of_no_nonzero_common_zero (m : ℕ) (K : Type*) [Field K]
    [IsAlgClosed K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2)
    (hno : ∀ v : Fin (m + 1) → K,
      (∀ i, MvPolynomial.eval v (F i) = 0) → v = 0)
    (j : Fin (m + 1)) :
    ∃ e : ℕ, (MvPolynomial.X j) ^ e ∈ Ideal.span (Set.range F) := by
  have hZL := zeroLocus_span_range_eq_singleton_zero m K F hF hno
  have hmem : MvPolynomial.X j ∈
      MvPolynomial.vanishingIdeal K ({0} : Set (Fin (m + 1) → K)) := by
    rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
    simp
  rw [← hZL] at hmem
  rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical] at hmem
  exact Ideal.mem_radical_iff.mp hmem

/-! ## §3 Homogeneous refinement of the power relations

The Nullstellensatz cofactors from §2 are inhomogeneous. Since each `Fᵢ` is
homogeneous of degree 2, taking the degree-`e` homogeneous component collapses
each product `gᵢ * Fᵢ` to `(homogeneousComponent (e - 2) gᵢ) * Fᵢ`
(`homogComp_mul_right_collapse`), and forces `e ≥ 2`
(`homogComp_mul_right_vanish`, else `Xⱼ ^ e = 0`). The refined cofactors are
homogeneous of degree `e - 2`, which is exactly what the degree reduction in
§4 needs. -/

/-- Graded collapse: the degree-`(i+2)` component of `g * F` for `F`
homogeneous of degree 2 is the degree-`i` component of `g` times `F`
(coefficient-wise via `coeff_mul` + the antidiagonal degree equation).

## References

* `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`,
  `MvPolynomial.coeff_homogeneousComponent`,
  `MvPolynomial.IsHomogeneous.coeff_eq_zero`.
* `Mathlib/Algebra/MvPolynomial/Basic.lean`, `MvPolynomial.ext`,
  `MvPolynomial.coeff_mul`.
* `Mathlib/Algebra/Order/Antidiag/Prod.lean`, `Finset.mem_antidiagonal`.
* `Mathlib/Data/Finsupp/Weight.lean`, `Finsupp.degree` (`map_add`). -/
theorem homogComp_mul_right_collapse {σ : Type*} {K : Type*}
    [Field K] (g F : MvPolynomial σ K) (hF : F.IsHomogeneous 2) (i : ℕ) :
    MvPolynomial.homogeneousComponent (i + 2) (g * F)
      = MvPolynomial.homogeneousComponent i g * F := by
  classical
  apply MvPolynomial.ext
  intro d
  rw [MvPolynomial.coeff_homogeneousComponent]
  by_cases hd : d.degree = i + 2
  · rw [ite_eq_left hd, MvPolynomial.coeff_mul, MvPolynomial.coeff_mul]
    apply Finset.sum_congr rfl
    intro x hx
    rw [MvPolynomial.coeff_homogeneousComponent]
    by_cases h1 : x.1.degree = i
    · rw [ite_eq_left h1]
    · rw [ite_eq_right h1]
      have h2 : x.2.degree ≠ 2 := by
        intro hcon
        apply h1
        have hsum := Finset.mem_antidiagonal.mp hx
        have hdeg := map_add Finsupp.degree x.1 x.2
        rw [hsum] at hdeg
        omega
      rw [hF.coeff_eq_zero h2, mul_zero, mul_zero]
  · rw [ite_eq_right hd, MvPolynomial.coeff_mul]
    symm
    apply Finset.sum_eq_zero
    intro x hx
    rw [MvPolynomial.coeff_homogeneousComponent]
    by_cases h1 : x.1.degree = i
    · rw [ite_eq_left h1]
      have h2 : x.2.degree ≠ 2 := by
        intro hcon
        apply hd
        have hsum := Finset.mem_antidiagonal.mp hx
        have hdeg := map_add Finsupp.degree x.1 x.2
        rw [hsum] at hdeg
        omega
      rw [hF.coeff_eq_zero h2, mul_zero]
    · rw [ite_eq_right h1, zero_mul]

/-- Graded vanishing: below degree 2, the homogeneous component of `g * F`
for `F` homogeneous of degree 2 is zero (every antidiagonal term needs a
degree-2 `F`-factor).

## References

* Same as `CurveMeet.homogComp_mul_right_collapse`. -/
theorem homogComp_mul_right_vanish {σ : Type*} {K : Type*}
    [Field K] (g F : MvPolynomial σ K) (hF : F.IsHomogeneous 2) (e : ℕ)
    (he : e < 2) :
    MvPolynomial.homogeneousComponent e (g * F) = 0 := by
  classical
  apply MvPolynomial.ext
  intro d
  rw [MvPolynomial.coeff_homogeneousComponent]
  by_cases hd : d.degree = e
  · rw [ite_eq_left hd, MvPolynomial.coeff_mul]
    apply Finset.sum_eq_zero
    intro x hx
    have h2 : x.2.degree ≠ 2 := by
      intro hcon
      have hsum := Finset.mem_antidiagonal.mp hx
      have hdeg := map_add Finsupp.degree x.1 x.2
      rw [hsum] at hdeg
      omega
    rw [hF.coeff_eq_zero h2, mul_zero]
  · rw [ite_eq_right hd]
    simp

/-- Powers of variables are homogeneous (`Xⱼ ^ e` has degree `e`).

## References

* `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`,
  `MvPolynomial.isHomogeneous_X`, `MvPolynomial.IsHomogeneous.pow`. -/
theorem isHomogeneous_X_pow {σ : Type*} {K : Type*} [Field K] (j : σ) (e : ℕ) :
    ((MvPolynomial.X j : MvPolynomial σ K) ^ e).IsHomogeneous e := by
  have h1 := MvPolynomial.isHomogeneous_X K j
  have h2 := h1.pow e
  simpa using h2

/-- Homogeneous refinement: the §2 power relation can be taken with `e ≥ 2`
and homogeneous cofactors of degree `e - 2`.

## References

* This module, `CurveMeet.pow_mem_span_of_no_nonzero_common_zero`,
  `CurveMeet.homogComp_mul_right_collapse`,
  `CurveMeet.homogComp_mul_right_vanish`,
  `CurveMeet.isHomogeneous_X_pow`.
* `Mathlib/RingTheory/Ideal/Operations.lean`,
  `Ideal.mem_span_range_iff_exists_fun`.
* `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`,
  `MvPolynomial.homogeneousComponent_eq_self`,
  `MvPolynomial.homogeneousComponent_isHomogeneous`.
* `Mathlib/Algebra/MvPolynomial/Basic.lean`, `MvPolynomial.X_ne_zero`. -/
theorem refined_pow_relation (m : ℕ) (K : Type*) [Field K] [IsAlgClosed K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2)
    (hno : ∀ v : Fin (m + 1) → K,
      (∀ i, MvPolynomial.eval v (F i) = 0) → v = 0)
    (j : Fin (m + 1)) :
    ∃ e : ℕ, 2 ≤ e ∧ ∃ g' : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K,
      (MvPolynomial.X j) ^ e = ∑ i, g' i * F i ∧
        ∀ i, (g' i).IsHomogeneous (e - 2) := by
  obtain ⟨e, he⟩ := pow_mem_span_of_no_nonzero_common_zero m K F hF hno j
  obtain ⟨g, hg⟩ := (Ideal.mem_span_range_iff_exists_fun).mp he
  have hsum : (MvPolynomial.X j) ^ e = ∑ i, g i * F i := hg.symm
  have hhom : ((MvPolynomial.X j : MvPolynomial (Fin (m + 1)) K) ^ e).IsHomogeneous
      e :=
    isHomogeneous_X_pow j e
  have he2 : 2 ≤ e := by
    by_contra hcon
    have hlt : e < 2 := by omega
    have hX : (MvPolynomial.X j : MvPolynomial (Fin (m + 1)) K) ^ e ≠ 0 :=
      pow_ne_zero e (MvPolynomial.X_ne_zero j)
    apply hX
    have hL := MvPolynomial.homogeneousComponent_eq_self hhom
    have hR : MvPolynomial.homogeneousComponent e (∑ i, g i * F i) = 0 := by
      rw [map_sum]
      apply Finset.sum_eq_zero
      intro i _
      exact homogComp_mul_right_vanish (g i) (F i) (hF i) e hlt
    rw [hsum] at hL
    rw [hR] at hL
    rw [hsum]
    exact hL.symm
  refine ⟨e, he2, fun i => MvPolynomial.homogeneousComponent (e - 2) (g i),
    ?_, fun i => MvPolynomial.homogeneousComponent_isHomogeneous _ _⟩
  have hL : MvPolynomial.homogeneousComponent e ((MvPolynomial.X j) ^ e)
      = (MvPolynomial.X j) ^ e :=
    MvPolynomial.homogeneousComponent_eq_self hhom
  rw [hsum, map_sum] at hL
  have hcollapse : ∀ i : Fin (m + 1),
      MvPolynomial.homogeneousComponent e (g i * F i)
        = MvPolynomial.homogeneousComponent (e - 2) (g i) * F i := by
    intro i
    have hbase := homogComp_mul_right_collapse (g i) (F i) (hF i) (e - 2)
    rw [show (e - 2) + 2 = e by omega] at hbase
    exact hbase
  rw [hsum, ← hL]
  apply Finset.sum_congr rfl
  intro i _
  change MvPolynomial.homogeneousComponent e (g i * F i)
      = MvPolynomial.homogeneousComponent (e - 2) (g i) * F i
  exact hcollapse i

/-! ## §4 Finite spanning, Artinian, corrected `MeetsInfinity`

From the §3 refined relations, every monomial of degree `≥ E` reduces (modulo
the `chartPoly` span) to a combination of strictly-smaller-degree polynomials;
strong induction shows the affine quotient is spanned by the finitely many
monomial classes of degree `< E`. Hence the quotient is a finite `K`-module,
hence Artinian (`IsArtinianRing.of_finite`), hence `KrullDimLE 0`
(`Ring.KrullDimLE.mk₀` + Artinian primes are maximal) — contradicting the
positive-dimensionality hypothesis. This closes the corrected end-to-end
hPDT shape unconditionally. -/

/-- The finsupp `sum id` is the degree (definitional).

## References

* `Mathlib/Data/Finsupp/Weight.lean`, `Finsupp.degree`. -/
theorem finsupp_sum_id_eq_degree {α : Type*} (s : α →₀ ℕ) :
    s.sum (fun _ e => e) = s.degree := rfl

/-- Each coordinate is bounded by the degree.

## References

* `Mathlib/Data/Finsupp/Weight.lean`, `Finsupp.degree_eq_sum`.
* `Mathlib/Algebra/Order/BigOperators/Group/Finset.lean`,
  `Finset.single_le_sum`. -/
theorem coord_le_degree {m : ℕ} (v : Fin (m + 1) →₀ ℕ) (j : Fin (m + 1)) :
    v j ≤ v.degree := by
  rw [Finsupp.degree_eq_sum]
  exact Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ j)

/-- Pigeonhole: a finsupp of degree `≥ E` has a coordinate `≥ eⱼ` for some `j`.

## References

* `Mathlib/Data/Finsupp/Weight.lean`, `Finsupp.degree_eq_sum`.
* `Mathlib/Algebra/Order/BigOperators/Group/Finset.lean`,
  `Finset.sum_le_sum`. -/
theorem exists_coord_ge_of_degree_ge {α : Type*} [Fintype α] (e : α → ℕ) (E : ℕ)
    (hE : E = (∑ j, (e j - 1)) + 1)
    (v : α →₀ ℕ) (hv : E ≤ v.degree) :
    ∃ j, e j ≤ v j := by
  by_contra hcon
  simp only [not_exists, not_le] at hcon
  have hle : v.degree ≤ ∑ j, (e j - 1) := by
    rw [Finsupp.degree_eq_sum]
    apply Finset.sum_le_sum
    intro j _
    have hj := hcon j
    omega
  omega

/-- Finsupp splitting: peeling off `t ≤ v j` from coordinate `j` is reversible.

## References

* `Mathlib/Algebra/Group/Finsupp.lean`, `Finsupp.add_apply`.
* `Mathlib/Data/Finsupp/Order.lean`, `Finsupp.tsub_apply`.
* `Mathlib/Data/Finsupp/Single.lean`, `Finsupp.single_eq_same`,
  `Finsupp.single_eq_of_ne`. -/
theorem finsupp_sub_single_add_cancel (v : Fin (m + 1) →₀ ℕ) (j : Fin (m + 1))
    (t : ℕ) (h : t ≤ v j) :
    (v - Finsupp.single j t) + Finsupp.single j t = v := by
  ext i
  rw [Finsupp.add_apply, Finsupp.tsub_apply]
  rcases eq_or_ne i j with rfl | hij
  · rw [Finsupp.single_eq_same]
    exact Nat.sub_add_cancel h
  · rw [Finsupp.single_eq_of_ne hij]
    simp

/-- Homogeneous polynomials have total degree at most their degree.

## References

* `Mathlib/Algebra/MvPolynomial/Degrees.lean`, `MvPolynomial.totalDegree`.
* `Mathlib/Data/Finset/Lattice/Fold.lean`, `Finset.sup_le_iff`.
* `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`,
  `MvPolynomial.IsHomogeneous.coeff_eq_zero`.
* `Mathlib/Data/Finsupp/Defs.lean`, `Finsupp.mem_support_iff`.
* This module, `CurveMeet.finsupp_sum_id_eq_degree`. -/
theorem totalDegree_homogeneous_le {σ : Type*} {K : Type*} [Field K]
    {p : MvPolynomial σ K} {n : ℕ} (hp : p.IsHomogeneous n) :
    p.totalDegree ≤ n := by
  unfold MvPolynomial.totalDegree
  rw [Finset.sup_le_iff]
  intro s hs
  have hds : s.degree = n := by
    by_contra hne
    have h0 : p.coeff s = 0 := hp.coeff_eq_zero hne
    have hs' := Finsupp.mem_support_iff.mp hs
    exact hs' h0
  have hdegeq : s.sum (fun _ e => e) = s.degree := finsupp_sum_id_eq_degree s
  rw [hdegeq, hds]

/-- The one-step reduction identity lies in the `chartPoly` span: splitting
`monomial (β + single j e) 1 = monomial β 1 * Xⱼ ^ e` and substituting the
refined relation leaves `Σᵢ monomial β 1 * Gᵢ * (Fᵢ - Xᵢ)`.

## References

* `Mathlib/Algebra/MvPolynomial/Basic.lean`,
  `MvPolynomial.monomial_add_single`.
* `Mathlib/Algebra/BigOperators/Ring/Finset.lean`, `Finset.mul_sum`.
* `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`,
  `Finset.sum_sub_distrib`.
* `Mathlib/RingTheory/Ideal/Defs.lean`, `Ideal.mul_mem_left`.
* `Mathlib/Algebra/Module/Submodule/Basic.lean`, `Submodule.sum_mem`.
* `Mathlib/LinearAlgebra/Span/Defs.lean`, `Submodule.subset_span`. -/
theorem reduction_mem_span (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (e : ℕ) (β : Fin (m + 1) →₀ ℕ) (j : Fin (m + 1))
    (G : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (hrel : (MvPolynomial.X j) ^ e = ∑ i, G i * F i) :
    MvPolynomial.monomial (β + Finsupp.single j e) 1
        - ∑ i, MvPolynomial.monomial β 1 * G i * MvPolynomial.X i
      ∈ Ideal.span (Set.range (chartPoly m K F)) := by
  have hmem : ∀ i : Fin (m + 1),
      F i - MvPolynomial.X i ∈ Ideal.span (Set.range (chartPoly m K F)) := by
    intro i
    exact Submodule.subset_span ⟨i, rfl⟩
  have hterm : ∀ i : Fin (m + 1),
      MvPolynomial.monomial β 1 * G i * (F i - MvPolynomial.X i)
        ∈ Ideal.span (Set.range (chartPoly m K F)) := by
    intro i
    exact Ideal.mul_mem_left _ _ (hmem i)
  have hsum : ∑ i, MvPolynomial.monomial β 1 * G i * (F i - MvPolynomial.X i)
      ∈ Ideal.span (Set.range (chartPoly m K F)) :=
    Submodule.sum_mem _ (fun i _ => hterm i)
  have hexpand : MvPolynomial.monomial (β + Finsupp.single j e) 1
      = ∑ i, MvPolynomial.monomial β 1 * (G i * F i) := by
    rw [MvPolynomial.monomial_add_single, hrel, Finset.mul_sum]
  have hsplit : ∀ i : Fin (m + 1),
      MvPolynomial.monomial β 1 * (G i * F i)
        - MvPolynomial.monomial β 1 * G i * MvPolynomial.X i
        = MvPolynomial.monomial β 1 * G i * (F i - MvPolynomial.X i) := by
    intro i
    rw [mul_sub]
    congr 1
    exact (mul_assoc _ _ _).symm
  have heq : MvPolynomial.monomial (β + Finsupp.single j e) 1
        - ∑ i, MvPolynomial.monomial β 1 * G i * MvPolynomial.X i
      = ∑ i, MvPolynomial.monomial β 1 * G i * (F i - MvPolynomial.X i) := by
    rw [hexpand, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => hsplit i)
  rw [heq]
  exact hsum

/-- The affine `chartPoly` quotient is a finite `K`-module: strong induction on
total degree reduces every monomial class to the finitely many classes of
degree `< E`.

## References

* This module, `CurveMeet.refined_pow_relation` (supplier of `e`, `G`),
  `CurveMeet.coord_le_degree`, `CurveMeet.exists_coord_ge_of_degree_ge`,
  `CurveMeet.finsupp_sub_single_add_cancel`,
  `CurveMeet.totalDegree_homogeneous_le`, `CurveMeet.reduction_mem_span`,
  `CurveMeet.finsupp_sum_id_eq_degree`.
* `Mathlib/RingTheory/Finiteness/Defs.lean`, `Module.finite_def`,
  `Submodule.fg_def`.
* `Mathlib/Data/Set/Finite/Basic.lean`, `Finset.finite_toSet`.
* `Mathlib/Data/Fintype/Pi.lean`, `Fintype.piFinset`, `Fintype.mem_piFinset`.
* `Mathlib/Data/Finset/Image.lean`, `Finset.coe_image`.
* `Mathlib/Data/Set/Operations.lean`, `Set.mem_image_of_mem`.
* `Mathlib/RingTheory/Ideal/Quotient/Operations.lean`,
  `Ideal.Quotient.mkₐ`, `Ideal.Quotient.mkₐ_eq_mk`.
* `Mathlib/RingTheory/Ideal/Quotient/Defs.lean`,
  `Ideal.Quotient.mk_surjective`, `Ideal.Quotient.eq_zero_iff_mem`.
* `Mathlib/Algebra/MvPolynomial/Basic.lean`, `MvPolynomial.as_sum`,
  `MvPolynomial.smul_monomial`.
* `Mathlib/Algebra/MvPolynomial/Degrees.lean`,
  `MvPolynomial.le_totalDegree`, `MvPolynomial.totalDegree_mul`,
  `MvPolynomial.totalDegree_monomial`, `MvPolynomial.totalDegree_X`.
* `Mathlib/Algebra/Module/Submodule/Basic.lean`, `Submodule.sum_mem`.
* `Mathlib/Algebra/Module/Submodule/Defs.lean`, `Submodule.smul_mem`;
  `Mathlib/LinearAlgebra/Span/Defs.lean`, `Submodule.subset_span`. -/
theorem module_finite_quotient_of_refined (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (e : Fin (m + 1) → ℕ)
    (G : Fin (m + 1) → Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (he2 : ∀ j, 2 ≤ e j)
    (hrel : ∀ j, (MvPolynomial.X j) ^ e j = ∑ i, G j i * F i)
    (hhom : ∀ j i, (G j i).IsHomogeneous (e j - 2)) :
    Module.Finite K (MvPolynomial (Fin (m + 1)) K ⧸
      Ideal.span (Set.range (chartPoly m K F))) := by
  classical
  set E : ℕ := (∑ j, (e j - 1)) + 1 with hE
  set S : Finset (MvPolynomial (Fin (m + 1)) K ⧸
      Ideal.span (Set.range (chartPoly m K F))) :=
    (Fintype.piFinset (fun _ : Fin (m + 1) => Finset.range E)).image
      (fun a : Fin (m + 1) → ℕ =>
        Ideal.Quotient.mkₐ K (Ideal.span (Set.range (chartPoly m K F)))
          (MvPolynomial.monomial
            (Finsupp.onFinset Finset.univ a (fun i _ => Finset.mem_univ i)) (1 : K)))
    with hS
  rw [Module.finite_def, Submodule.fg_def]
  refine ⟨↑S, Finset.finite_toSet S, ?_⟩
  refine le_antisymm le_top ?_
  intro y _
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective y
  have hy : y = Ideal.Quotient.mkₐ K (Ideal.span (Set.range (chartPoly m K F))) p := by
    rw [Ideal.Quotient.mkₐ_eq_mk]
    exact hp.symm
  rw [hy]
  suffices hmain : ∀ d : ℕ, ∀ q : MvPolynomial (Fin (m + 1)) K, q.totalDegree ≤ d →
      Ideal.Quotient.mkₐ K (Ideal.span (Set.range (chartPoly m K F))) q
        ∈ Submodule.span K (↑S : Set _) by
    exact hmain p.totalDegree p (le_refl _)
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro q hq
    rw [MvPolynomial.as_sum q, map_sum]
    apply Submodule.sum_mem
    intro v hv
    have hmc : MvPolynomial.monomial v (q.coeff v)
        = q.coeff v • MvPolynomial.monomial v (1 : K) := by
      rw [MvPolynomial.smul_monomial]
      simp
    rw [hmc, map_smul]
    apply Submodule.smul_mem
    have hvd : v.degree ≤ d := by
      have h1 : v.sum (fun _ e => e) ≤ q.totalDegree :=
        MvPolynomial.le_totalDegree hv
      rw [finsupp_sum_id_eq_degree] at h1
      exact le_trans h1 hq
    by_cases hbig : E ≤ v.degree
    · obtain ⟨j, hj⟩ := exists_coord_ge_of_degree_ge e E hE v hbig
      set β : Fin (m + 1) →₀ ℕ := v - Finsupp.single j (e j) with hβ
      have hsplit : β + Finsupp.single j (e j) = v := by
        rw [hβ]
        exact finsupp_sub_single_add_cancel v j (e j) hj
      have hdeg : β.degree + e j = v.degree := by
        have h1 : (β + Finsupp.single j (e j)).degree = v.degree := by rw [hsplit]
        rw [map_add, Finsupp.degree_single] at h1
        exact h1
      have hmem : MvPolynomial.monomial v (1 : K)
          - ∑ i, MvPolynomial.monomial β (1 : K) * G j i * MvPolynomial.X i
          ∈ Ideal.span (Set.range (chartPoly m K F)) := by
        have h := reduction_mem_span m K F (e j) β j (G j) (hrel j)
        rw [hsplit] at h
        exact h
      have h0 : Ideal.Quotient.mkₐ K (Ideal.span (Set.range (chartPoly m K F)))
          (MvPolynomial.monomial v (1 : K)
            - ∑ i, MvPolynomial.monomial β (1 : K) * G j i * MvPolynomial.X i) = 0 := by
        rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
        exact hmem
      have hred : Ideal.Quotient.mkₐ K (Ideal.span (Set.range (chartPoly m K F)))
          (MvPolynomial.monomial v (1 : K))
          = ∑ i, Ideal.Quotient.mkₐ K (Ideal.span (Set.range (chartPoly m K F)))
            (MvPolynomial.monomial β (1 : K) * G j i * MvPolynomial.X i) := by
        have hsub : Ideal.Quotient.mkₐ K (Ideal.span (Set.range (chartPoly m K F)))
              (MvPolynomial.monomial v (1 : K))
            - Ideal.Quotient.mkₐ K (Ideal.span (Set.range (chartPoly m K F)))
              (∑ i, MvPolynomial.monomial β (1 : K) * G j i * MvPolynomial.X i) = 0 := by
          rw [← map_sub]
          exact h0
        have heq := sub_eq_zero.mp hsub
        rw [heq, map_sum]
      rw [hred]
      apply Submodule.sum_mem
      intro i _
      have hdeg_bound : (MvPolynomial.monomial β (1 : K) * G j i
          * MvPolynomial.X i).totalDegree < v.degree := by
        have h1 : (MvPolynomial.monomial β (1 : K) * G j i
            * MvPolynomial.X i).totalDegree ≤ β.degree + (e j - 2) + 1 := by
          have hm : (MvPolynomial.monomial β (1 : K)).totalDegree ≤ β.degree := by
            rw [MvPolynomial.totalDegree_monomial _ one_ne_zero,
              finsupp_sum_id_eq_degree]
          have hg : (G j i).totalDegree ≤ e j - 2 :=
            totalDegree_homogeneous_le (hhom j i)
          have hX : ((MvPolynomial.X i :
              MvPolynomial (Fin (m + 1)) K)).totalDegree = 1 :=
            MvPolynomial.totalDegree_X i
          calc (MvPolynomial.monomial β (1 : K) * G j i
                * MvPolynomial.X i).totalDegree
              ≤ (MvPolynomial.monomial β (1 : K) * G j i).totalDegree
                + (MvPolynomial.X i).totalDegree :=
                MvPolynomial.totalDegree_mul _ _
            _ ≤ (MvPolynomial.monomial β (1 : K)).totalDegree
                + (G j i).totalDegree + 1 := by
                rw [hX]
                have hmul := MvPolynomial.totalDegree_mul
                  (MvPolynomial.monomial β (1 : K)) (G j i)
                exact Nat.add_le_add_right hmul 1
            _ ≤ β.degree + (e j - 2) + 1 :=
                Nat.add_le_add_right (Nat.add_le_add hm hg) 1
        have hej := he2 j
        omega
      have hlt : (MvPolynomial.monomial β (1 : K) * G j i
          * MvPolynomial.X i).totalDegree < d :=
        lt_of_lt_of_le hdeg_bound hvd
      exact ih _ hlt _ (le_refl _)
    · have hsmall : v.degree < E := by omega
      apply Submodule.subset_span
      have hvi : ∀ i, v i < E := fun i =>
        lt_of_le_of_lt (coord_le_degree v i) hsmall
      have hmemS : (⇑v : Fin (m + 1) → ℕ)
          ∈ (↑(Fintype.piFinset (fun _ : Fin (m + 1) => Finset.range E)) :
            Set (Fin (m + 1) → ℕ)) := by
        rw [Finset.mem_coe, Fintype.mem_piFinset]
        intro i
        exact Finset.mem_range.mpr (hvi i)
      have heta : Finsupp.onFinset Finset.univ (⇑v)
          (fun i _ => Finset.mem_univ i) = v := by
        ext i
        rfl
      have heq : (Ideal.Quotient.mkₐ K (Ideal.span (Set.range (chartPoly m K F)))
          (MvPolynomial.monomial
            (Finsupp.onFinset Finset.univ (⇑v) (fun i _ => Finset.mem_univ i)) (1 : K)))
          = Ideal.Quotient.mkₐ K (Ideal.span (Set.range (chartPoly m K F)))
            (MvPolynomial.monomial v (1 : K)) := by
        rw [heta]
      rw [hS, Finset.coe_image]
      rw [← heq]
      exact Set.mem_image_of_mem _ hmemS

/-- Corrected `MeetsInfinity`: under quadric homogeneity and over an
algebraically closed field, a positive-dimensional affine `chartPoly` quotient
forces a nonzero common zero of the input forms. (The uncorrected shape is
false — see `CurveMeet.meetsInfinity_ofLinear_false`.)


## References

* This module, `CurveMeet.MeetsInfinity`, `CurveMeet.refined_pow_relation`,
  `CurveMeet.module_finite_quotient_of_refined`.
* `Mathlib/RingTheory/Artinian/Module.lean`, `IsArtinianRing.of_finite`,
  `IsArtinianRing.isMaximal_of_isPrime`.
* `Mathlib/RingTheory/KrullDimension/Basic.lean`, `Ring.KrullDimLE.mk₀`. -/
theorem meetsInfinity_of_isHomogeneous (m : ℕ) (K : Type*) [Field K] [IsAlgClosed K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2) :
    MeetsInfinity m K F := by
  unfold MeetsInfinity
  intro hpos
  by_contra hcon
  have hno : ∀ v : Fin (m + 1) → K,
      (∀ i, MvPolynomial.eval v (F i) = 0) → v = 0 := by
    intro v hv
    by_contra hnv
    exact hcon ⟨v, hnv, hv⟩
  choose e he2 G hrel hhom using fun j => refined_pow_relation m K F hF hno j
  have hfin : Module.Finite K (MvPolynomial (Fin (m + 1)) K ⧸
      Ideal.span (Set.range (chartPoly m K F))) :=
    module_finite_quotient_of_refined m K F e G he2 hrel hhom
  have hart : IsArtinianRing (MvPolynomial (Fin (m + 1)) K ⧸
      Ideal.span (Set.range (chartPoly m K F))) :=
    @IsArtinianRing.of_finite K _ _ _ _ _ _ hfin
  have hdim : Ring.KrullDimLE 0 (MvPolynomial (Fin (m + 1)) K ⧸
      Ideal.span (Set.range (chartPoly m K F))) := by
    apply Ring.KrullDimLE.mk₀
    intro I hI
    exact @IsArtinianRing.isMaximal_of_isPrime _ _ I hI hart
  exact hpos hdim

end CurveMeet
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
