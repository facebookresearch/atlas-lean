/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-
Ported from `TauCeti/Analysis/Normed/Operator/IdempotentRange.lean` in TauCetiProject/TauCeti
(https://github.com/TauCetiProject/TauCeti) at revision
62bbc0596dc3539d488232e4e924a338548ea0a9; the copyright and license notice above are the
source's. Modification: imports of the coupled ports point to `MathlibExt`, and the description
of `isLocallyConstant_finrank_range` notes that `finrank` is the rank only in finite dimension;
declarations and proofs are unchanged.
-/
module

public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Topology.LocallyConstant.Basic
public import MathlibExt.Topology.Algebra.Module.ContinuousLinearMap.IdempotentRange

/-!
# The rank of a continuous family of projections

Let `p : B → F →L[𝕜] F` be a continuous family of idempotent operators on a Banach space `F`.
Near any `x₀`, the operator `p x * p x₀ + (1 - p x) * (1 - p x₀)` is invertible, since it equals
`1` at `x₀` and the units of `F →L[𝕜] F` form an open set. It then carries the range of `p x₀`
isomorphically onto the range of `p x` (`ContinuousLinearMap.IsIdempotentElem.rangeEquiv`), so
the ranges of nearby projections are isomorphic and the rank of the family is locally constant.
No compactness, separation or finite-dimensionality is assumed of the base or the fibres.

## Main results

* `TauCeti.isOpen_setOf_isUnit_intertwiner`: the intertwining operator of a continuous family is
  invertible on an open set, and `TauCeti.continuousOn_inverse_intertwiner`: its inverse is
  continuous there.
* `TauCeti.eventually_nonempty_continuousLinearEquiv_range`: the ranges of nearby projections in
  a continuous family are isomorphic.
* `TauCeti.isLocallyConstant_finrank_range`: the `finrank` of the ranges of a continuous family
  of projections is locally constant (it is the rank when the ranges are finite-dimensional;
  `finrank` is `0` on infinite-dimensional ranges).

## References

* T. Kato, *Perturbation Theory for Linear Operators*, Springer, Chapter I, §4.6.
-/

public section

open Topology Filter
open scoped Ring

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {p : B → F →L[𝕜] F}

/-- The intertwining operator `p x * p x₀ + (1 - p x) * (1 - p x₀)` of a continuous family of
operators depends continuously on `x`. -/
theorem continuous_intertwiner (hp : Continuous p) (x₀ : B) :
    Continuous fun x ↦ p x * p x₀ + (1 - p x) * (1 - p x₀) :=
  (hp.mul continuous_const).add ((continuous_const.sub hp).mul continuous_const)

variable [CompleteSpace F]

/-- The points at which the intertwining operator `p x * p x₀ + (1 - p x) * (1 - p x₀)` of a
continuous family of operators is invertible form an open set. -/
theorem isOpen_setOf_isUnit_intertwiner (hp : Continuous p) (x₀ : B) :
    IsOpen {x | IsUnit (p x * p x₀ + (1 - p x) * (1 - p x₀))} :=
  Units.isOpen.preimage (continuous_intertwiner hp x₀)

/-- The inverse of the intertwining operator `p x * p x₀ + (1 - p x) * (1 - p x₀)` of a
continuous family of operators depends continuously on `x` where that operator is invertible. -/
theorem continuousOn_inverse_intertwiner (hp : Continuous p) (x₀ : B) :
    ContinuousOn (fun x ↦ (p x * p x₀ + (1 - p x) * (1 - p x₀))⁻¹ʳ)
      {x | IsUnit (p x * p x₀ + (1 - p x) * (1 - p x₀))} :=
  fun _ hx ↦ ((NormedRing.inverse_continuousAt hx.unit).comp_of_eq
    (continuous_intertwiner hp x₀).continuousAt hx.unit_spec.symm).continuousWithinAt

/-- The ranges of nearby projections in a continuous family are isomorphic. -/
theorem eventually_nonempty_continuousLinearEquiv_range (hp : Continuous p)
    (hidem : ∀ x, IsIdempotentElem (p x)) (x₀ : B) :
    ∀ᶠ x in 𝓝 x₀, Nonempty ((p x₀).range ≃L[𝕜] (p x).range) := by
  filter_upwards [(isOpen_setOf_isUnit_intertwiner hp x₀).mem_nhds
    (ContinuousLinearMap.IsIdempotentElem.isUnit_mul_self_add_one_sub_mul_one_sub (hidem x₀))]
    with x (hx : IsUnit (p x * p x₀ + (1 - p x) * (1 - p x₀)))
  exact ⟨ContinuousLinearMap.IsIdempotentElem.rangeEquiv (hidem x₀) (hidem x) hx⟩

/-- **The rank of a continuous family of projections is locally constant**, measured by
`Module.finrank`: this is the rank when the ranges are finite-dimensional (`finrank` is `0` on an
infinite-dimensional range; the range equivalences above compare the ranges themselves). -/
theorem isLocallyConstant_finrank_range (hp : Continuous p)
    (hidem : ∀ x, IsIdempotentElem (p x)) :
    IsLocallyConstant fun x ↦ Module.finrank 𝕜 ((p x).range) :=
  (IsLocallyConstant.iff_eventually_eq _).mpr fun x₀ ↦
    (eventually_nonempty_continuousLinearEquiv_range hp hidem x₀).mono fun _ ⟨e⟩ ↦
      e.toLinearEquiv.finrank_eq.symm

end TauCeti
