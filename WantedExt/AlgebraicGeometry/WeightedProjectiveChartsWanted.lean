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

/-- **Cyclic quotient charts of weighted projective space.** For an algebraically closed field $k$
of characteristic zero, positive weights $w_0, …, w_n$ and an index $i$, the ring of invariants of
$k[x_j : j ≠ i]$ under $μ_{w_i}$, acting by $ζ · x_j = ζ^{w_j} x_j$, is isomorphic to the
degree-zero homogeneous localization of $k[x_0, …, x_n]$ at $x_i$ (the chart $D_+(x_i)$ of
$\mathbb P(w_0, …, w_n)$; Dolgachev, §1.3.3), and for every $t ∈ ℤ$ the polynomials of character $t$
are isomorphic to the degree-$t$ part of $k[x_0, …, x_n][x_i^{-1}]$, compatibly with the module
structures; all these maps are given by $x^a ↦ x^a x_i^{(t - \mathrm{wt}(a))/w_i}$
(`WeightedChartComparison`). -/
public def_wanted weighted_chart_comparison (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (n : ℕ) (w : Fin (n + 1) → ℕ) (hw : ∀ j, 0 < w j) (i : Fin (n + 1)) :
    WeightedChartComparison k n w i

end WantedExt.AlgebraicGeometry.WeightedProjectiveChartsWanted
