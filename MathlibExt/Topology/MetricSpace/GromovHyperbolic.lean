/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.GromovProduct

/-!
# Gromov-hyperbolic pseudometric spaces

This file defines Gromov's notion of `δ`-hyperbolicity for a (pseudo)metric space via the
four-point / Gromov-product inequality.

## Main definitions

* `Metric.IsDeltaHyperbolic X δ`: the space `X` is `δ`-hyperbolic, i.e. for all points the Gromov
  product satisfies `(x ∣ z)_w ≥ min (x ∣ y)_w (y ∣ z)_w - δ`, where
  `(x ∣ y)_w = Metric.gromovProduct w x y` (basepoint first, as in Mathlib). The constant
  `δ` is nonnegative by definition.
* `Metric.IsGromovHyperbolic X`: the space `X` is `δ`-hyperbolic for some `δ`.

## Main results

* `Metric.IsDeltaHyperbolic.four_point`: the defining four-point inequality.
* `Metric.IsDeltaHyperbolic.mono`: `δ`-hyperbolicity is monotone in `δ`.
* `Metric.IsDeltaHyperbolic.nonneg`: the constant `δ` is nonnegative.
* `Metric.isDeltaHyperbolic_zero_of_subsingleton`: a subsingleton space is `0`-hyperbolic.

## References

* M. Gromov, *Hyperbolic groups*, in Essays in Group Theory, Math. Sci. Res. Inst. Publ. 8,
  Springer (1987), 75-263. The four-point/Gromov-product formulation of `δ`-hyperbolicity is §1.1.

## Tags

Gromov hyperbolic, hyperbolic metric space, Gromov product
-/

@[expose] public section

namespace Metric

variable {X : Type*} [PseudoMetricSpace X]

/-- A pseudometric space `X` is `δ`-hyperbolic (in the sense of Gromov) if `0 ≤ δ` and the
Gromov product satisfies the four-point inequality
`(x ∣ z)_w ≥ min (x ∣ y)_w (y ∣ z)_w - δ` for all points `w x y z`, where
`(x ∣ y)_w = Metric.gromovProduct w x y` (basepoint first, as in Mathlib). -/
def IsDeltaHyperbolic (X : Type*) [PseudoMetricSpace X] (δ : ℝ) : Prop :=
  0 ≤ δ ∧ ∀ w x y z : X, min (gromovProduct w x y) (gromovProduct w y z) - δ ≤ gromovProduct w x z

/-- A pseudometric space is Gromov-hyperbolic if it is `δ`-hyperbolic for some `δ`. -/
def IsGromovHyperbolic (X : Type*) [PseudoMetricSpace X] : Prop := ∃ δ : ℝ, IsDeltaHyperbolic X δ

/-- The defining four-point inequality of a `δ`-hyperbolic space. -/
theorem IsDeltaHyperbolic.four_point {δ : ℝ} (h : IsDeltaHyperbolic X δ) (w x y z : X) :
    min (gromovProduct w x y) (gromovProduct w y z) - δ ≤ gromovProduct w x z :=
  h.2 w x y z

/-- Enlarging the constant preserves `δ`-hyperbolicity. -/
theorem IsDeltaHyperbolic.mono {δ δ' : ℝ} (h : IsDeltaHyperbolic X δ) (hδ : δ ≤ δ') :
    IsDeltaHyperbolic X δ' :=
  ⟨h.1.trans hδ, fun w x y z => by
    have := h.four_point w x y z
    linarith⟩

/-- The hyperbolicity constant is nonnegative. -/
theorem IsDeltaHyperbolic.nonneg {δ : ℝ} (h : IsDeltaHyperbolic X δ) : 0 ≤ δ :=
  h.1

/-- A subsingleton space (in particular a single point) is `0`-hyperbolic: it is an `ℝ`-tree. -/
theorem isDeltaHyperbolic_zero_of_subsingleton [Subsingleton X] : IsDeltaHyperbolic X 0 := by
  refine ⟨le_refl 0, fun w x y z => ?_⟩
  rw [Subsingleton.elim x w, Subsingleton.elim y w, Subsingleton.elim z w, min_self, sub_zero]

end Metric

/-! ### Examples -/

-- A single point is `0`-hyperbolic (boundary case `δ = 0`).
example : Metric.IsDeltaHyperbolic (PUnit : Type) 0 :=
  Metric.isDeltaHyperbolic_zero_of_subsingleton
