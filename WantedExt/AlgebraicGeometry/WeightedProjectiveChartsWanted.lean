/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.WeightedProjectiveCharts

/-!
# Normalized cyclic weighted-projective chart and graded-module comparison

Source: Dolgachev, *Weighted projective varieties* (1982), §§1.1, 1.3.3, 1.5.1;
Cadman, *Using stacks to impose tangency conditions on curves* (2007), §2.
The chart and twisting spaces, cyclic action and comparison value of every
polynomial are actual constructions in the completed core.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.WeightedProjectiveChartsWanted

open MathlibExt.AlgebraicGeometry.WeightedProjectiveCharts

/-- The standard cyclic quotient chart and character-module comparison,
normalized in the actual weighted homogeneous localization. -/
public def_wanted weighted_chart_comparison (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (n : ℕ) (w : Fin (n + 1) → ℕ) (hw : ∀ j, 0 < w j) (i : Fin (n + 1)) :
    WeightedChartComparison k n w i

end WantedExt.AlgebraicGeometry.WeightedProjectiveChartsWanted
