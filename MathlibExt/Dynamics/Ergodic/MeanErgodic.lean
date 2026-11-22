/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.MeanErgodic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-!
# Von Neumann's mean ergodic theorem for measure-preserving maps

A measure-preserving map `T` of `(α, μ)` acts on `L²(μ)` by its Koopman operator
`U_T f = f ∘ T`, a linear isometry. Von Neumann's mean ergodic theorem says that the ergodic
averages `(1/N) ∑_{k<N} f ∘ T^k` converge in `L²(μ)` to the orthogonal projection of `f` onto
the closed subspace of `U_T`-invariant functions. Pinned Mathlib proves the operator form for
any contraction of a Hilbert space
(`ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection`) and provides the isometry
`MeasureTheory.Lp.compMeasurePreservingₗᵢ`; this module puts them together in the
measure-theoretic form.

## Main results

* `koopman`: the Koopman operator of a measure-preserving map on `L²(μ)`.
* `tendsto_birkhoffAverage_koopman`: von Neumann's mean ergodic theorem (O. Sarig, *Lecture Notes
  on Ergodic Theory*, Theorem 2.1).

## References

* O. Sarig, *Lecture Notes on Ergodic Theory*, §2.1 and Theorem 2.1,
  https://www.weizmann.ac.il/math/sarigo/sites/math.sarigo/files/uploads/ergodicnotes.pdf
-/

@[expose] public section

namespace MathlibExt.Dynamics.Ergodic.MeanErgodic

open MeasureTheory Filter Topology
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {T : α → α}

/-- **Koopman operator.** For a measure-preserving map `T` of `(α, μ)`, the operator
`U_T f = f ∘ T` on `L²(μ)`, a linear isometry, viewed as a continuous linear map. -/
noncomputable def koopman (hT : MeasurePreserving T μ μ) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (Lp.compMeasurePreservingₗᵢ ℝ T hT).toContinuousLinearMap

/-- **The Koopman operator is composition with `T`**, almost everywhere. -/
theorem koopman_apply_ae_eq (hT : MeasurePreserving T μ μ) (f : Lp ℝ 2 μ) :
    koopman hT f =ᵐ[μ] f ∘ T :=
  Lp.coeFn_compMeasurePreserving f hT

/-- **The Koopman operator is a contraction**: `‖U_T‖ ≤ 1`, since `U_T` is an isometry. -/
theorem norm_koopman_le (hT : MeasurePreserving T μ μ) : ‖koopman hT‖ ≤ 1 :=
  LinearIsometry.norm_toContinuousLinearMap_le _

/-- **Von Neumann's mean ergodic theorem.** Let `T` preserve the measure `μ` and let
`f ∈ L²(μ)`. The ergodic averages `(1/N) ∑_{k<N} U_T^k f`, where `U_T^k f = f ∘ T^k` in
`L²(μ)`, converge in `L²(μ)` to the orthogonal projection of `f` onto the closed subspace of
`U_T`-invariant functions (O. Sarig, *Lecture Notes on Ergodic Theory*, Theorem 2.1, stated
there for probability-preserving maps; the limit is identified as this projection in the same
chapter, in the discussion of the nonergodic case). The second statement of that theorem, that
the limit is `∫ f dμ` when `μ` is a probability measure and `T` is ergodic, is not formalized
here. -/
theorem tendsto_birkhoffAverage_koopman (hT : MeasurePreserving T μ μ) (f : Lp ℝ 2 μ) :
    Tendsto (fun N => birkhoffAverage ℝ (koopman hT) _root_.id N f) atTop
      (𝓝 (((koopman hT).eqLocus (1 : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)).orthogonalProjectionOnto f)) :=
  (koopman hT).tendsto_birkhoffAverage_orthogonalProjection (norm_koopman_le hT) f

end MathlibExt.Dynamics.Ergodic.MeanErgodic
