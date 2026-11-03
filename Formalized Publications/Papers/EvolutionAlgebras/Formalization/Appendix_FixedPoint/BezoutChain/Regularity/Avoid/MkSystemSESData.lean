/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Statement.Definitions
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.RegularityBridge
import Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Module.Submodule.Map
import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Regular.SMul
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Per-`(k,d)` graded-piece SES data for the `mkSystem` quotient family

This file sidesteps the graded-quotient API gap (documented in
`Geometry/HilbertFunctionCount.lean`, `## Added hypotheses and deviations`)
by reducing it to regularity:
instead of a general graded-quotient API, the graded pieces of the
successive `mkSystem` quotients are defined explicitly as
`R_d / (J_k ∩ R_d)`-style ordinary `K`-module quotients, the `×Q_k` maps are
explicit, injectivity is proved from explicit regularity inputs, and the
cokernel is identified with the next explicit piece by direct
linear-algebra computation (third isomorphism theorem plus homogeneous
division). The per-step data assemble into the exact `hSES`/`hSEC`
consumer shapes of `Appendix_FixedPoint.BezoutChain.length_section_eq_two_pow`
(`Geometry/HilbertFunctionCount.lean`).

All results in this file are fully proved.

## Main results

* `stageIdeal q k`: the `k`-th prefix ideal
  `Ideal.span (Set.image q {j | j.val < k})`, definitionally matching the
  span shape in `RegularityBridge.SuccessiveSMulRegular`.
* `pieceSub J d` / `stagePiece J d`: the explicit graded piece
  `(R/J)_d := R_d / (J ∩ R_d)` as an ordinary `K`-module quotient
  (`R_d = MvPolynomial.homogeneousSubmodule`), with `mem_pieceSub`.
* `Hfun q k d` / `Ffun q ℓ d`: the Hilbert functions (finranks of the
  explicit pieces / section pieces).
* Homogeneous division (`hc_mul_expand`, `hc_mul_factor_high`,
  `hc_mul_factor_low`, `mem_sup_span_decomp`, `mem_sup_span_low`): for
  `g` homogeneous of degree `m`, homogeneous components factor through
  `×g`, so `J' = J ⊔ span{g}` satisfies
  `J' ∩ R_{e+m} = (J ∩ R_{e+m}) + g·R_e` and `J' ∩ R_d = J ∩ R_d` for
  `d < m` (via `Ideal.homogeneous_span` +
  `MvPolynomial.homogeneousComponent_mem_of_mem` — no new API needed).
* `baseMul` / `stepMul`: the explicit `×g` map on pieces (shift `m`),
  via `Submodule.mapQ`.
* `stepMul_injective`: injectivity from the single explicit hypothesis
  `IsSMulRegular (R ⧸ ↑J) g`; `stageReg_of_succ` bridges this to the
  exact `RegularityBridge.SuccessiveSMulRegular` component (hypothesis (1) of
  `MkSystemRegular`) by `Submodule.span_smul_eq` +
  `Submodule.set_smul_top_eq_span`.
* `pieceSub_sup_eq` / `stepCokerEquiv`: the cokernel identification
  `(stagePiece J (e+m) ⧸ range stepMul) ≃ₗ[K] stagePiece (J ⊔ span{g})`
  by the third isomorphism theorem
  (`Submodule.quotientQuotientEquivQuotientSup`).
* `hSES_quadrics`: the exact `hSES` input shape of
  `length_section_eq_two_pow` for `Hfun` (step via
  `hSES_step_of_pieceSES`, low degrees proved, assembled by
  `hSES_of_steps`).
* `hH0_quadrics`: the exact `hH0` input shape (via `hilbertSeries_poly`).
* `hSEC_section`: the exact `hSEC` input shape for `Ffun`/`Hfun`
  (shift-1 mirror, via `graded_piece_ses` directly).
* `mkSystem_hSES_of` / `mkSystem_hSEC_of` / `mkSystem_hH0_of`: the
  above specialized to the `mkSystem` combination family
  `q k = ∑ j, M k j • mkSystem n K F j` (homogeneity re-proved locally,
  so no extra imports are needed).

## Status: hypotheses

The results above assume exactly the following (nothing else):

1. `hsucc : RegularityBridge.SuccessiveSMulRegular q` — the exact hypothesis (1)
   of `MkSystemRegular`; rungs `≥ 2` are the `hunmixed_ge2` input.
2. `hsec : IsSMulRegular (R ⧸ ↑(stageIdeal q (n+1))) ℓ` — section
   regularity for the `hSEC` assembly only.
3. `hF : ∀ i, (F i).IsHomogeneous 2` — input-data homogeneity for the
   `mkSystem` specialization (the analogue of `Statement`'s own `hG`).

Not assumed: per-step `hlow` (proved), `hH0` (proved), any cokernel
identification (constructed), any graded-quotient API. `hfilter` (the
degree-filtration summation for `length_section_eq_two_pow`) stays with
the Elimination/Counting geometry and is out of scope here.

## Dependencies

This file deliberately avoids importing the following modules:

* `Statement/Statement`, `Geometry/Counting`, `BridgeToFixedPoint/FixedPointFromBezout`:
  never imported (import-closure hygiene).
* `Regularity/Avoid/ResultantLemmas`,
  `Regularity/Avoid/TriangularRegularity`: never imported (excluded for
  import-closure hygiene); `gradeMul`-shaped maps and homogeneity facts are
  re-proved here from primary Mathlib API.
* `Regularity/GradeDepthFragment`, `Regularity/HeightDrop`: not imported (no
  grade/depth content is needed).
* `Geometry/HilbertFunctionCount` is `Statement`-free (in-repo closure:
  `Statement/Definitions` + `Geometry/ChartFiltration` +
  `Geometry/Elimination` + `Geometry/LocalMultiplicity` + Mathlib; no
  `Statement/Statement` import)
  and supplies `graded_piece_ses`, `hSES_step_of_pieceSES`,
  `hSES_of_steps`, `hilbertSeries_poly`, `homogeneousPiece_finite`.

## References

Mathlib v4.34.0 exact names (with source locations under
`.lake/packages/mathlib`): see the per-declaration `## References`
subsections.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace MkSystemSESData

open scoped BigOperators

variable (n : ℕ) (K : Type*) [Field K]

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ## Stage ideals and explicit graded pieces -/

/-- The `k`-th prefix ideal of the family `q`: the span of the values before
`k`. Definitionally matches the span shape in
`RegularityBridge.SuccessiveSMulRegular`, so `stageReg_of_succ` below bridges by
rewriting only.

## References

* `Mathlib/RingTheory/Ideal/Span.lean`, `Ideal.span`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Regularity.Avoid.RegularityBridge`,
  `Appendix_FixedPoint.BezoutChain.RegularityBridge.SuccessiveSMulRegular` (shape matched). -/
noncomputable def stageIdeal
    (q : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K) (k : ℕ) :
    Ideal (MvPolynomial (Fin (n + 2)) K) :=
  Ideal.span (Set.image q { j : Fin (n + 1) | j.val < k })

/-- The stage-`0` ideal is empty (`⊥`). -/
theorem stageIdeal_zero (q : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K) :
    stageIdeal n K q 0 = ⊥ := by
  unfold stageIdeal
  have hset : { j : Fin (n + 1) | j.val < 0 } = ∅ := by
    ext j
    simp
  rw [hset, Set.image_empty, Ideal.span_empty]

/-- The stage-`(k+1)` ideal is the stage-`k` ideal plus the next generator.

## References

* `Mathlib/Data/Set/Image.lean`, `Set.image_insert_eq`.
* `Mathlib/RingTheory/Ideal/Span.lean`, `Ideal.span_insert`. -/
theorem stageIdeal_succ (q : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (k : ℕ) (hk : k < n + 1) :
    stageIdeal n K q (k + 1)
      = stageIdeal n K q k ⊔ Ideal.span {q ⟨k, hk⟩} := by
  unfold stageIdeal
  have hset : { j : Fin (n + 1) | j.val < k + 1 }
      = insert ⟨k, hk⟩ { j : Fin (n + 1) | j.val < k } := by
    ext j
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff]
    constructor
    · intro h
      by_cases hj : j.val = k
      · exact Or.inl (Fin.ext hj)
      · exact Or.inr (by omega)
    · rintro (rfl | h)
      · exact Nat.lt_succ_self k
      · omega
  rw [hset, Set.image_insert_eq, Ideal.span_insert]
  exact sup_comm _ _

/-- Stage ideals spanned by quadrics are homogeneous ideals (for the
`homogeneousSubmodule` grading), so homogeneous components preserve them
(`MvPolynomial.homogeneousComponent_mem_of_mem`).

## References

* `Mathlib/RingTheory/GradedAlgebra/Homogeneous/Ideal.lean`,
  `Ideal.homogeneous_span`.
* `Mathlib/Algebra/GradedMonoid.lean`, `SetLike.IsHomogeneousElem`.
* `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`,
  `MvPolynomial.mem_homogeneousSubmodule`. -/
theorem stageIdeal_isHomogeneous
    (q : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hq : ∀ i, (q i).IsHomogeneous 2) (k : ℕ) :
    (stageIdeal n K q k).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (n + 2)) K) := by
  unfold stageIdeal
  refine Ideal.homogeneous_span _ _ ?_
  intro x hx
  obtain ⟨j, _, rfl⟩ := hx
  exact ⟨2, (MvPolynomial.mem_homogeneousSubmodule 2 (q j)).mpr (hq j)⟩

/-- The graded-piece submodule `J ∩ R_d`: elements of the degree-`d`
homogeneous piece lying in `J` (as a `K`-submodule of the piece).

## References

* `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`,
  `MvPolynomial.homogeneousSubmodule`.
* `Mathlib/Algebra/Module/Submodule/RestrictScalars.lean`,
  `Submodule.restrictScalars`. -/
noncomputable def pieceSub (J : Ideal (MvPolynomial (Fin (n + 2)) K))
    (d : ℕ) :
    Submodule K ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 2)) K d) :=
  Submodule.comap
    (MvPolynomial.homogeneousSubmodule (Fin (n + 2)) K d).subtype
    (J.restrictScalars K)

/-- Membership in `pieceSub` is membership in `J` (definitional). -/
theorem mem_pieceSub (J : Ideal (MvPolynomial (Fin (n + 2)) K)) (d : ℕ)
    (x : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 2)) K d)) :
    x ∈ pieceSub n K J d ↔ (x.1 : MvPolynomial (Fin (n + 2)) K) ∈ J :=
  Iff.rfl

/-- The explicit graded piece `(R/J)_d := R_d / (J ∩ R_d)`: an ordinary
`K`-module quotient, no graded-quotient API needed. -/
abbrev stagePiece (J : Ideal (MvPolynomial (Fin (n + 2)) K)) (d : ℕ) : Type _ :=
  ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 2)) K d) ⧸ pieceSub n K J d

/-- Polynomial-ring pieces are finite (instance form of
`homogeneousPiece_finite`, for the quotient instance below).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.homogeneousPiece_finite`. -/
instance rdFinite (d : ℕ) :
    Module.Finite K ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 2)) K d) :=
  homogeneousPiece_finite n K d

/-- Explicit graded pieces are finite (quotients of finite pieces).

## References

* `Mathlib/RingTheory/Finiteness/Basic.lean`, `Module.Finite.of_surjective`.
* `Mathlib/LinearAlgebra/Quotient/Defs.lean`, `Submodule.mkQ_surjective`. -/
instance stagePieceFinite (J : Ideal (MvPolynomial (Fin (n + 2)) K))
    (d : ℕ) : Module.Finite K (stagePiece n K J d) :=
  Module.Finite.of_surjective (pieceSub n K J d).mkQ
    (Submodule.mkQ_surjective _)

/-- The Hilbert function of the explicit stage pieces. -/
noncomputable def Hfun (q : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (k d : ℕ) : ℕ :=
  Module.finrank K (stagePiece n K (stageIdeal n K q k) d)

/-- The section ideal: the full stage ideal plus the section form. -/
noncomputable def secIdeal (q : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : MvPolynomial (Fin (n + 2)) K) : Ideal (MvPolynomial (Fin (n + 2)) K) :=
  stageIdeal n K q (n + 1) ⊔ Ideal.span {ℓ}

/-- The section Hilbert function (finranks of the explicit section pieces). -/
noncomputable def Ffun (q : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : MvPolynomial (Fin (n + 2)) K) (d : ℕ) : ℕ :=
  Module.finrank K (stagePiece n K (secIdeal n K q ℓ) d)

/-! ## Homogeneous division through `×g` (general degree `m`)

For `g` homogeneous of degree `m`, homogeneous components factor through
multiplication by `g`. This is the homogeneous-cofactor technique,
generalized from principal ideals to arbitrary homogeneous
ideals plus one generator — the engine that identifies the abstract
cokernel with the next explicit piece without any graded-quotient API. -/

/-- Expansion of the `t`-th homogeneous component of `g * s` along the
homogeneous-component decomposition of `s`: each summand is homogeneous
of degree `m + i`, so taking the `t`-th component selects `t = m + i`.

## References

* `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`,
  `MvPolynomial.sum_homogeneousComponent`,
  `MvPolynomial.homogeneousComponent_of_mem`,
  `MvPolynomial.homogeneousComponent_isHomogeneous`,
  `MvPolynomial.IsHomogeneous.mul`.
* `Mathlib/Algebra/BigOperators/Ring/Finset.lean`, `Finset.mul_sum`. -/
theorem hc_mul_expand (g s : MvPolynomial (Fin (n + 2)) K) (m t : ℕ)
    (hg : g.IsHomogeneous m) :
    MvPolynomial.homogeneousComponent t (g * s)
      = ∑ i ∈ Finset.range (s.totalDegree + 1),
        (if t = m + i then g * MvPolynomial.homogeneousComponent i s
          else 0) := by
  have hdecomp : s = ∑ i ∈ Finset.range (s.totalDegree + 1),
      MvPolynomial.homogeneousComponent i s :=
    (MvPolynomial.sum_homogeneousComponent s).symm
  have hmul : ∀ i : ℕ,
      (g * MvPolynomial.homogeneousComponent i s).IsHomogeneous (m + i) :=
    fun i => hg.mul (MvPolynomial.homogeneousComponent_isHomogeneous i s)
  have hcomp : ∀ i : ℕ, MvPolynomial.homogeneousComponent t
        (g * MvPolynomial.homogeneousComponent i s)
        = if t = m + i then g * MvPolynomial.homogeneousComponent i s
          else 0 :=
    fun i => MvPolynomial.homogeneousComponent_of_mem
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (hmul i))
  have h1 : MvPolynomial.homogeneousComponent t (g * s)
      = ∑ i ∈ Finset.range (s.totalDegree + 1),
        MvPolynomial.homogeneousComponent t
          (g * MvPolynomial.homogeneousComponent i s) := by
    conv_lhs => rw [hdecomp, Finset.mul_sum, map_sum]
  rw [h1]
  apply Finset.sum_congr rfl
  intro i _
  exact hcomp i

/-- High-component factoring: `hc (e+m) (g*s) = g * hc e s`.

## References

* `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`,
  `Finset.sum_eq_single`, `Finset.sum_eq_zero`.
* `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`,
  `MvPolynomial.homogeneousComponent_eq_zero`. -/
theorem hc_mul_factor_high (g s : MvPolynomial (Fin (n + 2)) K) (m e : ℕ)
    (hg : g.IsHomogeneous m) :
    MvPolynomial.homogeneousComponent (e + m) (g * s)
      = g * MvPolynomial.homogeneousComponent e s := by
  rw [hc_mul_expand n K g s m (e + m) hg]
  by_cases hd : e ≤ s.totalDegree
  · rw [Finset.sum_eq_single e]
    · rw [ite_eq_left (by omega : e + m = m + e)]
    · intro i _ hne
      rw [ite_eq_right (by omega : ¬ e + m = m + i)]
    · intro hcon
      exact absurd
        (Finset.mem_range.mpr (show e < s.totalDegree + 1 from by omega)) hcon
  · have hzero : (∑ i ∈ Finset.range (s.totalDegree + 1),
        (if e + m = m + i then g * MvPolynomial.homogeneousComponent i s
          else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hi' : i < s.totalDegree + 1 := Finset.mem_range.mp hi
      rw [ite_eq_right (by omega : ¬ e + m = m + i)]
    rw [hzero]
    have hs0 : MvPolynomial.homogeneousComponent e s = 0 :=
      MvPolynomial.homogeneousComponent_eq_zero e s (by omega)
    rw [hs0, mul_zero]

/-- Low-component vanishing: `hc d (g*s) = 0` for `d < m` (every summand
has degree `m + i ≥ m > d`). -/
theorem hc_mul_factor_low (g s : MvPolynomial (Fin (n + 2)) K) (m d : ℕ)
    (hg : g.IsHomogeneous m) (hd : d < m) :
    MvPolynomial.homogeneousComponent d (g * s) = 0 := by
  rw [hc_mul_expand n K g s m d hg]
  apply Finset.sum_eq_zero
  intro i _
  rw [ite_eq_right (by omega : ¬ d = m + i)]

/-- Homogeneous division for `J ⊔ span{g}` (high degrees): a homogeneous
degree-`(e+m)` element of `J ⊔ span{g}` is a homogeneous degree-`(e+m)`
element of `J` plus `g` times a homogeneous degree-`e` element. The
`J`-part stays in `J` by homogeneity of `J`; the `g`-part factors by
`hc_mul_factor_high`.

## References

* `Mathlib/Algebra/Module/Submodule/Lattice.lean`, `Submodule.mem_sup`.
* `Mathlib/RingTheory/Ideal/Span.lean`, `Ideal.mem_span_singleton'`.
* `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`,
  `MvPolynomial.homogeneousComponent_mem_of_mem`,
  `MvPolynomial.homogeneousComponent_eq_self`. -/
theorem mem_sup_span_decomp (J : Ideal (MvPolynomial (Fin (n + 2)) K))
    (hJ : J.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (n + 2)) K))
    (g : MvPolynomial (Fin (n + 2)) K) (m e : ℕ) (hg : g.IsHomogeneous m)
    (x : MvPolynomial (Fin (n + 2)) K) (hx : x.IsHomogeneous (e + m))
    (hxJ : x ∈ J ⊔ Ideal.span {g}) :
    ∃ a ∈ J, a.IsHomogeneous (e + m)
      ∧ ∃ s : MvPolynomial (Fin (n + 2)) K,
        s.IsHomogeneous e ∧ x = a + g * s := by
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hxJ
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hb
  have hhab : (a + b).IsHomogeneous (e + m) := by rw [hab]; exact hx
  have h1 : MvPolynomial.homogeneousComponent (e + m) (a + b)
      = MvPolynomial.homogeneousComponent (e + m) a
        + MvPolynomial.homogeneousComponent (e + m) b := map_add _ _ _
  have h2 : MvPolynomial.homogeneousComponent (e + m) b
      = g * MvPolynomial.homogeneousComponent e r := by
    conv_lhs => rw [← hr]
    rw [mul_comm r g]
    exact hc_mul_factor_high n K g r m e hg
  refine ⟨MvPolynomial.homogeneousComponent (e + m) a,
    MvPolynomial.homogeneousComponent_mem_of_mem hJ ha (e + m),
    MvPolynomial.homogeneousComponent_isHomogeneous (e + m) a,
    MvPolynomial.homogeneousComponent e r,
    MvPolynomial.homogeneousComponent_isHomogeneous e r, ?_⟩
  calc x = a + b := hab.symm
    _ = MvPolynomial.homogeneousComponent (e + m) (a + b) :=
        (MvPolynomial.homogeneousComponent_eq_self hhab).symm
    _ = MvPolynomial.homogeneousComponent (e + m) a
          + g * MvPolynomial.homogeneousComponent e r := by rw [h1, h2]

/-- Low-degree stability: a homogeneous degree-`d` element of
`J ⊔ span{g}` with `d < m` already lies in `J` (the `g`-part has no
degree-`d` component, by `hc_mul_factor_low`). -/
theorem mem_sup_span_low (J : Ideal (MvPolynomial (Fin (n + 2)) K))
    (hJ : J.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (n + 2)) K))
    (g : MvPolynomial (Fin (n + 2)) K) (m d : ℕ) (hg : g.IsHomogeneous m)
    (x : MvPolynomial (Fin (n + 2)) K) (hx : x.IsHomogeneous d)
    (hd : d < m) (hxJ : x ∈ J ⊔ Ideal.span {g}) : x ∈ J := by
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hxJ
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hb
  have hhab : (a + b).IsHomogeneous d := by rw [hab]; exact hx
  have h1 : MvPolynomial.homogeneousComponent d (a + b)
      = MvPolynomial.homogeneousComponent d a
        + MvPolynomial.homogeneousComponent d b := map_add _ _ _
  have h2 : MvPolynomial.homogeneousComponent d b = 0 := by
    conv_lhs => rw [← hr]
    rw [mul_comm r g]
    exact hc_mul_factor_low n K g r m d hg hd
  have hxeq : x = MvPolynomial.homogeneousComponent d a := by
    calc x = a + b := hab.symm
      _ = MvPolynomial.homogeneousComponent d (a + b) :=
          (MvPolynomial.homogeneousComponent_eq_self hhab).symm
      _ = MvPolynomial.homogeneousComponent d a
            + MvPolynomial.homogeneousComponent d b := h1
      _ = MvPolynomial.homogeneousComponent d a := by rw [h2, add_zero]
  rw [hxeq]
  exact MvPolynomial.homogeneousComponent_mem_of_mem hJ ha d

/-! ## The explicit `×g` map and its injectivity -/

/-- Multiplication by a homogeneous element, restricted to graded pieces:
`×g` from the degree-`e` piece to the degree-`(e+m)` piece. (The
`gradeMul` construction, proved here from primary Mathlib API.)

## References

* `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`,
  `MvPolynomial.homogeneousSubmodule`,
  `MvPolynomial.mem_homogeneousSubmodule`, `MvPolynomial.IsHomogeneous.mul`.
* `Mathlib/Algebra/Group/Action/Defs.lean`, `mul_smul_comm`. -/
noncomputable def baseMul (g : MvPolynomial (Fin (n + 2)) K) (m e : ℕ)
    (hg : g.IsHomogeneous m) :
    ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 2)) K e) →ₗ[K]
      ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 2)) K (e + m)) where
  toFun x := ⟨g * x.1,
    (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (by
      have h := hg.mul ((MvPolynomial.mem_homogeneousSubmodule _ _).mp x.2)
      rwa [add_comm m e] at h)⟩
  map_add' x y := Subtype.ext (mul_add g x.1 y.1)
  map_smul' r x := Subtype.ext (mul_smul_comm r g x.1)

/-- `×g` preserves the piece submodules (the ideal absorbs `g * ·`).

## References

* `Mathlib/RingTheory/Ideal/Operations.lean`, `Ideal.mul_mem_left`. -/
theorem stepMul_welldef (J : Ideal (MvPolynomial (Fin (n + 2)) K))
    (g : MvPolynomial (Fin (n + 2)) K) (m e : ℕ) (hg : g.IsHomogeneous m) :
    pieceSub n K J e
      ≤ Submodule.comap (baseMul n K g m e hg)
        (pieceSub n K J (e + m)) := by
  intro x hx
  rw [mem_pieceSub] at hx
  rw [Submodule.mem_comap, mem_pieceSub]
  exact Ideal.mul_mem_left _ _ hx

/-- The explicit `×g` map on graded pieces, via `Submodule.mapQ`.

## References

* `Mathlib/LinearAlgebra/Quotient/Basic.lean`, `Submodule.mapQ`. -/
noncomputable def stepMul (J : Ideal (MvPolynomial (Fin (n + 2)) K))
    (g : MvPolynomial (Fin (n + 2)) K) (m e : ℕ) (hg : g.IsHomogeneous m) :
    stagePiece n K J e →ₗ[K] stagePiece n K J (e + m) :=
  Submodule.mapQ _ _ (baseMul n K g m e hg)
    (stepMul_welldef n K J g m e hg)

/-- Injectivity of the explicit `×g` map from the single explicit
regularity hypothesis `IsSMulRegular (R ⧸ ↑J) g`: if `g·(x-y) ∈ J`
then `g • mk(x-y) = 0` in `R ⧸ ↑J`, so `mk(x-y) = 0` and `x-y ∈ J`.

## References

* `Mathlib/Algebra/Regular/SMul.lean`, `IsSMulRegular`.
* `Mathlib/LinearAlgebra/Quotient/Defs.lean`,
  `Submodule.Quotient.mk_eq_zero`, `Submodule.mkQ_surjective`. -/
theorem stepMul_injective (J : Ideal (MvPolynomial (Fin (n + 2)) K))
    (g : MvPolynomial (Fin (n + 2)) K) (m e : ℕ) (hg : g.IsHomogeneous m)
    (hreg : IsSMulRegular
      (MvPolynomial (Fin (n + 2)) K ⧸ (J : Submodule _ _)) g) :
    Function.Injective (stepMul n K J g m e hg) := by
  intro u v huv
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (pieceSub n K J e) u
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (pieceSub n K J e) v
  have e1 : stepMul n K J g m e hg ((pieceSub n K J e).mkQ x)
      = (pieceSub n K J (e + m)).mkQ (baseMul n K g m e hg x) := rfl
  have e2 : stepMul n K J g m e hg ((pieceSub n K J e).mkQ y)
      = (pieceSub n K J (e + m)).mkQ (baseMul n K g m e hg y) := rfl
  have h1 : (pieceSub n K J (e + m)).mkQ (baseMul n K g m e hg x)
      = (pieceSub n K J (e + m)).mkQ (baseMul n K g m e hg y) := by
    rw [← e1, ← e2]; exact huv
  have h0 : (pieceSub n K J (e + m)).mkQ
      (baseMul n K g m e hg x - baseMul n K g m e hg y) = 0 := by
    rw [map_sub, h1, sub_self]
  have hmem0 : baseMul n K g m e hg x - baseMul n K g m e hg y
      ∈ pieceSub n K J (e + m) :=
    (Submodule.Quotient.mk_eq_zero _).mp h0
  have hmem : g * (x.1 - y.1) ∈ (J : Submodule _ _) := by
    have h2 := (mem_pieceSub n K J (e + m) _).mp hmem0
    have hval : g * (x.1 - y.1)
        = (baseMul n K g m e hg x - baseMul n K g m e hg y).1 := by
      rw [mul_sub]; rfl
    rwa [hval]
  have hsmul : g • ((J : Submodule _ _).mkQ (x.1 - y.1))
      = g • ((J : Submodule _ _).mkQ 0) := by
    simp only [← map_smul, smul_eq_mul]
    have hmk : (J : Submodule _ _).mkQ (g * (x.1 - y.1)) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr hmem
    rw [hmk, mul_zero, map_zero]
  have hwinj : (J : Submodule _ _).mkQ (x.1 - y.1)
      = (J : Submodule _ _).mkQ 0 := hreg hsmul
  have hwmem : x.1 - y.1 ∈ (J : Submodule _ _) := by
    have h00 : (J : Submodule _ _).mkQ (x.1 - y.1) = 0 := by
      rw [hwinj, map_zero]
    exact (Submodule.Quotient.mk_eq_zero _).mp h00
  have hxy : x - y ∈ pieceSub n K J e := by
    rw [mem_pieceSub]
    exact hwmem
  have hfin : (pieceSub n K J e).mkQ x
      = (pieceSub n K J e).mkQ y := by
    have h00 : (pieceSub n K J e).mkQ (x - y) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr hxy
    rw [map_sub] at h00
    exact sub_eq_zero.mp h00
  exact hfin

/-- Bridge from the exact `RegularityBridge.SuccessiveSMulRegular` component
(hypothesis (1) of `MkSystemRegular`) to the `stepMul_injective`
hypothesis: `Ideal.span s • ⊤ = Ideal.span s` as `R`-submodules.

## References

* `Mathlib/RingTheory/Ideal/Operations.lean`, `Submodule.span_smul_eq`,
  `Submodule.set_smul_top_eq_span`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Regularity.Avoid.RegularityBridge`,
  `Appendix_FixedPoint.BezoutChain.RegularityBridge.SuccessiveSMulRegular`. -/
theorem stageReg_of_succ (q : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q) (k : ℕ) (hk : k < n + 1) :
    IsSMulRegular (MvPolynomial (Fin (n + 2)) K
      ⧸ ((stageIdeal n K q k : Ideal _) : Submodule _ _)) (q ⟨k, hk⟩) := by
  have h := hsucc ⟨k, hk⟩
  have hval : (⟨k, hk⟩ : Fin (n + 1)).val = k := rfl
  rw [hval] at h
  have hsub : (Ideal.span (Set.image q { j : Fin (n + 1) | j.val < k }) • ⊤ :
        Submodule (MvPolynomial (Fin (n + 2)) K)
          (MvPolynomial (Fin (n + 2)) K))
      = (Ideal.span (Set.image q { j : Fin (n + 1) | j.val < k }) :
        Submodule _ _) := by
    rw [Submodule.span_smul_eq, Submodule.set_smul_top_eq_span]
  change IsSMulRegular (MvPolynomial (Fin (n + 2)) K
    ⧸ (Ideal.span (Set.image q { j : Fin (n + 1) | j.val < k }) :
      Submodule _ _)) (q ⟨k, hk⟩)
  rw [← hsub]
  exact h

/-! ## Cokernel identification by direct linear-algebra computation -/

/-- The submodule-level identification: `(J ∩ R) ⊔ range(×g) = J' ∩ R`
where `J' = J ⊔ span{g}`. The `⊆` direction is ideal absorption; the
`⊇` direction is `mem_sup_span_decomp`.

## References

* `Mathlib/Algebra/Module/Submodule/Lattice.lean`, `Submodule.mem_sup`,
  `Submodule.mem_sup_left`, `Submodule.mem_sup_right`.
* `Mathlib/Algebra/Module/Submodule/Range.lean`, `LinearMap.mem_range`.
* `Mathlib/RingTheory/Ideal/Span.lean`, `Ideal.subset_span`.
* `Mathlib/RingTheory/Ideal/Operations.lean`, `Ideal.mul_mem_left`. -/
theorem pieceSub_sup_eq (J : Ideal (MvPolynomial (Fin (n + 2)) K))
    (hJ : J.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (n + 2)) K))
    (g : MvPolynomial (Fin (n + 2)) K) (m e : ℕ) (hg : g.IsHomogeneous m) :
    pieceSub n K J (e + m) ⊔ LinearMap.range (baseMul n K g m e hg)
      = pieceSub n K (J ⊔ Ideal.span {g}) (e + m) := by
  ext y
  constructor
  · intro hy
    rw [Submodule.mem_sup] at hy
    obtain ⟨a, ha, b, hb, hab⟩ := hy
    rw [mem_pieceSub] at ha
    rw [LinearMap.mem_range] at hb
    obtain ⟨s, hs⟩ := hb
    rw [mem_pieceSub]
    have ha' : (a.1 : MvPolynomial (Fin (n + 2)) K)
        ∈ J ⊔ Ideal.span {g} := Submodule.mem_sup_left ha
    have hgmem : g ∈ J ⊔ Ideal.span {g} :=
      Submodule.mem_sup_right (Ideal.subset_span (Set.mem_singleton g))
    have hb' : (b.1 : MvPolynomial (Fin (n + 2)) K)
        ∈ J ⊔ Ideal.span {g} := by
      have hbs : (b.1 : MvPolynomial (Fin (n + 2)) K) = g * s.1 := by
        rw [← hs]; rfl
      rw [hbs, mul_comm]
      exact Ideal.mul_mem_left _ _ hgmem
    have hval : (y.1 : MvPolynomial (Fin (n + 2)) K) = a.1 + b.1 := by
      rw [← hab]; rfl
    rw [hval]
    exact add_mem ha' hb'
  · intro hy
    rw [mem_pieceSub] at hy
    have hhom : (y.1 : MvPolynomial (Fin (n + 2)) K).IsHomogeneous (e + m) :=
      (MvPolynomial.mem_homogeneousSubmodule _ _).mp y.2
    obtain ⟨a, haJ, hahom, s, hshom, hdeq⟩ :=
      mem_sup_span_decomp n K J hJ g m e hg y.1 hhom hy
    have ha'mem : (⟨a, (MvPolynomial.mem_homogeneousSubmodule _ _).mpr hahom⟩ :
        ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 2)) K (e + m)))
        ∈ pieceSub n K J (e + m) := by
      rw [mem_pieceSub]
      exact haJ
    have hb'mem : baseMul n K g m e hg
          (⟨s, (MvPolynomial.mem_homogeneousSubmodule _ _).mpr hshom⟩ :
            ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 2)) K e))
          ∈ LinearMap.range (baseMul n K g m e hg) :=
      LinearMap.mem_range.mpr
        ⟨⟨s, (MvPolynomial.mem_homogeneousSubmodule _ _).mpr hshom⟩, rfl⟩
    have hab' : (⟨a, (MvPolynomial.mem_homogeneousSubmodule _ _).mpr hahom⟩ :
          ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 2)) K (e + m)))
          + baseMul n K g m e hg
            (⟨s, (MvPolynomial.mem_homogeneousSubmodule _ _).mpr hshom⟩ :
              ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 2)) K e))
          = y := by
      apply Subtype.ext
      exact hdeq.symm
    exact Submodule.mem_sup.mpr
      ⟨⟨a, (MvPolynomial.mem_homogeneousSubmodule _ _).mpr hahom⟩, ha'mem,
        baseMul n K g m e hg
          (⟨s, (MvPolynomial.mem_homogeneousSubmodule _ _).mpr hshom⟩ :
            ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 2)) K e)),
        hb'mem, hab'⟩

/-- The range of the induced map is the projected range of the base map.

## References

* `Mathlib/LinearAlgebra/Quotient/Basic.lean`, `Submodule.range_mapQ`. -/
theorem stepRange_eq (J : Ideal (MvPolynomial (Fin (n + 2)) K))
    (g : MvPolynomial (Fin (n + 2)) K) (m e : ℕ) (hg : g.IsHomogeneous m) :
    LinearMap.range (stepMul n K J g m e hg)
      = Submodule.map (pieceSub n K J (e + m)).mkQ
        (LinearMap.range (baseMul n K g m e hg)) := by
  change LinearMap.range
    (Submodule.mapQ _ _ (baseMul n K g m e hg)
      (stepMul_welldef n K J g m e hg)) = _
  exact Submodule.range_mapQ _ _ _ _

/-- The cokernel identification: the abstract cokernel of `stepMul` is
the next explicit graded piece. By the third isomorphism theorem
(`quotientQuotientEquivQuotientSup`) plus `pieceSub_sup_eq` — direct
linear-algebra computation, no graded-quotient API.

## References

* `Mathlib/LinearAlgebra/Isomorphisms.lean`,
  `Submodule.quotientQuotientEquivQuotientSup`.
* `Mathlib/LinearAlgebra/Quotient/Defs.lean`, `Submodule.quotEquivOfEq`. -/
noncomputable def stepCokerEquiv (J : Ideal (MvPolynomial (Fin (n + 2)) K))
    (hJ : J.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (n + 2)) K))
    (g : MvPolynomial (Fin (n + 2)) K) (m e : ℕ) (hg : g.IsHomogeneous m) :
    ((stagePiece n K J (e + m)) ⧸ LinearMap.range (stepMul n K J g m e hg))
      ≃ₗ[K] stagePiece n K (J ⊔ Ideal.span {g}) (e + m) :=
  (Submodule.quotEquivOfEq _ _ (stepRange_eq n K J g m e hg)).trans
    ((Submodule.quotientQuotientEquivQuotientSup
      (pieceSub n K J (e + m))
      (LinearMap.range (baseMul n K g m e hg))).trans
      (Submodule.quotEquivOfEq _ _
        (pieceSub_sup_eq n K J hJ g m e hg)))

/-! ## The `hSES` assembly in the exact consumer shape -/

/-- Per-`(k,e)` quadric step: `H (k+1) (e+2) + H k e = H k (e+2)`, via
`hSES_step_of_pieceSES` with the explicit `f`/`e`/`hinj` above.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.hSES_step_of_pieceSES`. -/
theorem hstep_of (q : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hq : ∀ i, (q i).IsHomogeneous 2)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q) (k e : ℕ) (hk : k < n + 1) :
    Hfun n K q (k + 1) (e + 2) + Hfun n K q k e
      = Hfun n K q k (e + 2) := by
  have hJ : stageIdeal n K q k ⊔ Ideal.span {q ⟨k, hk⟩}
      = stageIdeal n K q (k + 1) :=
    (stageIdeal_succ n K q k hk).symm
  have hP : pieceSub n K (stageIdeal n K q k ⊔ Ideal.span {q ⟨k, hk⟩}) (e + 2)
      = pieceSub n K (stageIdeal n K q (k + 1)) (e + 2) := by rw [hJ]
  have hgreg : IsSMulRegular (MvPolynomial (Fin (n + 2)) K
      ⧸ ((stageIdeal n K q k : Ideal _) : Submodule _ _)) (q ⟨k, hk⟩) :=
    stageReg_of_succ n K q hsucc k hk
  refine hSES_step_of_pieceSES K (Hfun n K q (k + 1) (e + 2))
    (Hfun n K q k e) (Hfun n K q k (e + 2))
    (stagePiece n K (stageIdeal n K q k) e)
    (stagePiece n K (stageIdeal n K q k) (e + 2))
    (stagePiece n K (stageIdeal n K q (k + 1)) (e + 2))
    (stepMul n K (stageIdeal n K q k) (q ⟨k, hk⟩) 2 e (hq ⟨k, hk⟩))
    ((stepCokerEquiv n K (stageIdeal n K q k)
      (stageIdeal_isHomogeneous n K q hq k) (q ⟨k, hk⟩) 2 e
      (hq ⟨k, hk⟩)).trans (Submodule.quotEquivOfEq _ _ hP))
    (stepMul_injective n K (stageIdeal n K q k) (q ⟨k, hk⟩) 2 e
      (hq ⟨k, hk⟩) hgreg)
    rfl rfl rfl

/-- Per-`(k,d)` quadric step in truncated-subtraction form. -/
theorem hstep_quadric (q : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hq : ∀ i, (q i).IsHomogeneous 2)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q) (k d : ℕ) (hk : k < n + 1)
    (hd : 2 ≤ d) :
    Hfun n K q (k + 1) d + Hfun n K q k (d - 2) = Hfun n K q k d := by
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hd
  have hd2 : d = e + 2 := by omega
  subst hd2
  rw [Nat.add_sub_cancel]
  exact hstep_of n K q hq hsucc k e hk

/-- Low-degree agreement: `H (k+1) d = H k d` for `d < 2` (proved, via
`mem_sup_span_low` — not assumed).

## References

* `Mathlib/LinearAlgebra/Dimension/Finrank.lean`,
  `LinearEquiv.finrank_eq`. -/
theorem hlow_quadric (q : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hq : ∀ i, (q i).IsHomogeneous 2) (k d : ℕ) (hk : k < n + 1)
    (hd : d < 2) :
    Hfun n K q (k + 1) d = Hfun n K q k d := by
  have hsub : pieceSub n K (stageIdeal n K q (k + 1)) d
      = pieceSub n K (stageIdeal n K q k) d := by
    rw [stageIdeal_succ n K q k hk]
    ext y
    rw [mem_pieceSub, mem_pieceSub]
    constructor
    · intro hy
      have hhom : (y.1 : MvPolynomial (Fin (n + 2)) K).IsHomogeneous d :=
        (MvPolynomial.mem_homogeneousSubmodule _ _).mp y.2
      exact mem_sup_span_low n K (stageIdeal n K q k)
        (stageIdeal_isHomogeneous n K q hq k) (q ⟨k, hk⟩) 2 d
        (hq ⟨k, hk⟩) y.1 hhom hd hy
    · exact Submodule.mem_sup_left
  change Module.finrank K (stagePiece n K (stageIdeal n K q (k + 1)) d)
    = Module.finrank K (stagePiece n K (stageIdeal n K q k) d)
  exact LinearEquiv.finrank_eq (Submodule.quotEquivOfEq _ _ hsub)

/-- The exact `hSES` input shape of `length_section_eq_two_pow`
(`Geometry/HilbertFunctionCount.lean`) for `Hfun`.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.hSES_of_steps`. -/
theorem hSES_quadrics (q : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hq : ∀ i, (q i).IsHomogeneous 2)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q) :
    ∀ k, k < n + 1 → ∀ d,
      Hfun n K q (k + 1) d
        + (if 2 ≤ d then Hfun n K q k (d - 2) else 0)
        = Hfun n K q k d :=
  hSES_of_steps n (Hfun n K q)
    (fun k hk d hd => hstep_quadric n K q hq hsucc k d hk hd)
    (fun k hk d hd => hlow_quadric n K q hq k d hk hd)

/-- Quotient by `⊥` is the original module (for the `hH0` base case).

## References

* `Mathlib/Algebra/Module/Submodule/Equiv.lean`,
  `LinearEquiv.ofBijective`.
* `Mathlib/Algebra/Module/Submodule/Ker.lean`, `LinearMap.ker_eq_bot`.
* `Mathlib/LinearAlgebra/Quotient/Basic.lean`, `Submodule.ker_mkQ`. -/
noncomputable def pieceBotEquiv (V : Type*) [AddCommGroup V] [Module K V] :
    (V ⧸ (⊥ : Submodule K V)) ≃ₗ[K] V :=
  (LinearEquiv.ofBijective (⊥ : Submodule K V).mkQ
    ⟨LinearMap.ker_eq_bot.mp (Submodule.ker_mkQ _),
      Submodule.mkQ_surjective _⟩).symm

/-- The exact `hH0` input shape of `length_section_eq_two_pow`
(`Geometry/HilbertFunctionCount.lean`) for `Hfun`: stage `0` is the polynomial
ring itself.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.hilbertSeries_poly`.
* `Mathlib/LinearAlgebra/Dimension/Finrank.lean`,
  `LinearEquiv.finrank_eq`. -/
theorem hH0_quadrics (q : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (d : ℕ) :
    Hfun n K q 0 d = Nat.choose (d + (n + 2) - 1) ((n + 2) - 1) := by
  have hJ : stageIdeal n K q 0 = ⊥ := stageIdeal_zero n K q
  have hP : pieceSub n K (stageIdeal n K q 0) d = ⊥ := by
    rw [hJ]
    ext y
    simp only [mem_pieceSub, Submodule.mem_bot]
    constructor
    · intro hy
      exact Subtype.ext hy
    · intro hy
      exact congrArg Subtype.val hy
  have e1 : stagePiece n K (stageIdeal n K q 0) d
      ≃ₗ[K] ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 2)) K d) :=
    (Submodule.quotEquivOfEq _ _ hP).trans (pieceBotEquiv K _)
  change Module.finrank K (stagePiece n K (stageIdeal n K q 0) d) = _
  rw [LinearEquiv.finrank_eq e1]
  exact hilbertSeries_poly K (n + 2) d (by omega)

/-! ## The `hSEC` assembly in the exact consumer shape (shift-1 mirror) -/

/-- Per-degree section step: `F (e+1) + H e = H (e+1)`, via
`graded_piece_ses` with the explicit shift-1 data.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.graded_piece_ses`. -/
theorem hSECstep_of (q : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hq : ∀ i, (q i).IsHomogeneous 2)
    (ℓ : MvPolynomial (Fin (n + 2)) K) (hℓ : ℓ.IsHomogeneous 1)
    (hsec : IsSMulRegular (MvPolynomial (Fin (n + 2)) K
      ⧸ ((stageIdeal n K q (n + 1) : Ideal _) : Submodule _ _)) ℓ)
    (e : ℕ) :
    Ffun n K q ℓ (e + 1) + Hfun n K q (n + 1) e
      = Hfun n K q (n + 1) (e + 1) := by
  have h := graded_piece_ses K
    (stagePiece n K (stageIdeal n K q (n + 1)) e)
    (stagePiece n K (stageIdeal n K q (n + 1)) (e + 1))
    (stagePiece n K (secIdeal n K q ℓ) (e + 1))
    (stepMul n K (stageIdeal n K q (n + 1)) ℓ 1 e hℓ)
    (stepCokerEquiv n K (stageIdeal n K q (n + 1))
      (stageIdeal_isHomogeneous n K q hq (n + 1)) ℓ 1 e hℓ)
    (stepMul_injective n K (stageIdeal n K q (n + 1)) ℓ 1 e hℓ hsec)
  change Module.finrank K (stagePiece n K (secIdeal n K q ℓ) (e + 1))
    + Module.finrank K (stagePiece n K (stageIdeal n K q (n + 1)) e)
    = Module.finrank K (stagePiece n K (stageIdeal n K q (n + 1)) (e + 1))
  omega

/-- Per-degree section step in truncated-subtraction form. -/
theorem hSECstep (q : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hq : ∀ i, (q i).IsHomogeneous 2)
    (ℓ : MvPolynomial (Fin (n + 2)) K) (hℓ : ℓ.IsHomogeneous 1)
    (hsec : IsSMulRegular (MvPolynomial (Fin (n + 2)) K
      ⧸ ((stageIdeal n K q (n + 1) : Ideal _) : Submodule _ _)) ℓ)
    (d : ℕ) (hd : 1 ≤ d) :
    Ffun n K q ℓ d + Hfun n K q (n + 1) (d - 1)
      = Hfun n K q (n + 1) d := by
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hd
  have hd2 : d = e + 1 := by omega
  subst hd2
  rw [Nat.add_sub_cancel]
  exact hSECstep_of n K q hq ℓ hℓ hsec e

/-- Degree-`0` section agreement: `F 0 = H 0` (proved). -/
theorem hSEClow (q : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hq : ∀ i, (q i).IsHomogeneous 2)
    (ℓ : MvPolynomial (Fin (n + 2)) K) (hℓ : ℓ.IsHomogeneous 1) :
    Ffun n K q ℓ 0 = Hfun n K q (n + 1) 0 := by
  have hsub : pieceSub n K (secIdeal n K q ℓ) 0
      = pieceSub n K (stageIdeal n K q (n + 1)) 0 := by
    change pieceSub n K (stageIdeal n K q (n + 1) ⊔ Ideal.span {ℓ}) 0 = _
    ext y
    rw [mem_pieceSub, mem_pieceSub]
    constructor
    · intro hy
      have hhom : (y.1 : MvPolynomial (Fin (n + 2)) K).IsHomogeneous 0 :=
        (MvPolynomial.mem_homogeneousSubmodule _ _).mp y.2
      exact mem_sup_span_low n K (stageIdeal n K q (n + 1))
        (stageIdeal_isHomogeneous n K q hq (n + 1)) ℓ 1 0 hℓ y.1 hhom
        (by omega) hy
    · exact Submodule.mem_sup_left
  change Module.finrank K (stagePiece n K (secIdeal n K q ℓ) 0)
    = Module.finrank K (stagePiece n K (stageIdeal n K q (n + 1)) 0)
  exact LinearEquiv.finrank_eq (Submodule.quotEquivOfEq _ _ hsub)

/-- The exact `hSEC` input shape of `length_section_eq_two_pow`
(`Geometry/HilbertFunctionCount.lean`) for `Ffun`/`Hfun` (the shift-1
mirror of `hSES_of_steps`, cf. `MkSystemRegular.hSEC_of_steps`,
re-proved here for a minimal dependency surface). -/
theorem hSEC_section (q : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hq : ∀ i, (q i).IsHomogeneous 2)
    (ℓ : MvPolynomial (Fin (n + 2)) K) (hℓ : ℓ.IsHomogeneous 1)
    (hsec : IsSMulRegular (MvPolynomial (Fin (n + 2)) K
      ⧸ ((stageIdeal n K q (n + 1) : Ideal _) : Submodule _ _)) ℓ) :
    ∀ d, Ffun n K q ℓ d
        + (if 1 ≤ d then Hfun n K q (n + 1) (d - 1) else 0)
        = Hfun n K q (n + 1) d := by
  intro d
  by_cases hd : 1 ≤ d
  · simp only [hd, ite_true]
    exact hSECstep n K q hq ℓ hℓ hsec d hd
  · simp only [hd, ite_false, add_zero]
    have hd0 : d = 0 := by omega
    rw [hd0]
    exact hSEClow n K q hq ℓ hℓ

/-! ## `mkSystem` specialization -/

/-- Each `Gᵢ` is homogeneous of degree `2`
(`Statement/Statement.mkSystem_homogeneous`, re-proved here — with the verbatim
proof of `MkSystemRegular.mkSystem_isHomogeneous_of` — to avoid depending
on `Statement`).

## References

* `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`,
  `MvPolynomial.rename_isHomogeneous`, `MvPolynomial.IsHomogeneous.sub`,
  `MvPolynomial.isHomogeneous_X`, `MvPolynomial.IsHomogeneous.mul`. -/
theorem mkSystem_homogeneous_of
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2) (i : Fin (n + 1)) :
    (mkSystem n K F i).IsHomogeneous 2 := by
  simp only [mkSystem]
  exact ((hF i).rename_isHomogeneous).sub
    (by simpa using
      (MvPolynomial.isHomogeneous_X _ _).mul (MvPolynomial.isHomogeneous_X _ _))

/-- `K`-linear combinations of quadrics are quadrics (verbatim
`MkSystemRegular.combo_isHomogeneous`, re-proved here to avoid depending
on `MkSystemRegular`'s import chain).

## References

* `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`,
  `MvPolynomial.IsHomogeneous.sum`, `MvPolynomial.IsHomogeneous.C_mul`.
* `Mathlib/Algebra/MvPolynomial/Basic.lean`,
  `MvPolynomial.smul_eq_C_mul`. -/
theorem combo_homogeneous_of
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hG : ∀ j, (G j).IsHomogeneous 2)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (k : Fin (n + 1)) :
    (∑ j, M k j • G j).IsHomogeneous 2 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro j _
  rw [MvPolynomial.smul_eq_C_mul]
  exact (hG j).C_mul _

/-- The section linear form is homogeneous of degree `1`.

## References

* `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`,
  `MvPolynomial.IsHomogeneous.sum`,
  `MvPolynomial.isHomogeneous_C_mul_X`. -/
theorem mkLin_homogeneous_of (ℓ : Fin (n + 2) → K) :
    (mkLin n K ℓ).IsHomogeneous 1 := by
  simp only [mkLin]
  apply MvPolynomial.IsHomogeneous.sum
  intro j _
  exact MvPolynomial.isHomogeneous_C_mul_X _ _

/-- The `hSES` consumer shape for the `mkSystem` combination family. -/
theorem mkSystem_hSES_of
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2)
    (hsucc : RegularityBridge.SuccessiveSMulRegular
      (fun k => ∑ j, M k j • mkSystem n K F j)) :
    ∀ k, k < n + 1 → ∀ d,
      Hfun n K (fun k => ∑ j, M k j • mkSystem n K F j) (k + 1) d
        + (if 2 ≤ d
          then Hfun n K (fun k => ∑ j, M k j • mkSystem n K F j) k (d - 2)
          else 0)
        = Hfun n K (fun k => ∑ j, M k j • mkSystem n K F j) k d :=
  hSES_quadrics n K _
    (fun i => combo_homogeneous_of n K _
      (fun j => mkSystem_homogeneous_of n K F hF j) M i) hsucc

/-- The `hSEC` consumer shape for the `mkSystem` family sectioned by
`mkLin ℓ`. -/
theorem mkSystem_hSEC_of
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (ℓ : Fin (n + 2) → K)
    (hF : ∀ i, (F i).IsHomogeneous 2)
    (hsec : IsSMulRegular (MvPolynomial (Fin (n + 2)) K ⧸
      ((stageIdeal n K (fun k => ∑ j, M k j • mkSystem n K F j) (n + 1) :
        Ideal _) : Submodule _ _)) (mkLin n K ℓ)) :
    ∀ d, Ffun n K (fun k => ∑ j, M k j • mkSystem n K F j) (mkLin n K ℓ) d
        + (if 1 ≤ d
          then Hfun n K (fun k => ∑ j, M k j • mkSystem n K F j) (n + 1) (d - 1)
          else 0)
        = Hfun n K (fun k => ∑ j, M k j • mkSystem n K F j) (n + 1) d :=
  hSEC_section n K _
    (fun i => combo_homogeneous_of n K _
      (fun j => mkSystem_homogeneous_of n K F hF j) M i)
    _ (mkLin_homogeneous_of n K ℓ) hsec

/-- The `hH0` consumer shape for the `mkSystem` combination family. -/
theorem mkSystem_hH0_of
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (d : ℕ) :
    Hfun n K (fun k => ∑ j, M k j • mkSystem n K F j) 0 d
      = Nat.choose (d + (n + 2) - 1) ((n + 2) - 1) :=
  hH0_quadrics n K _ d

end MkSystemSESData
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
