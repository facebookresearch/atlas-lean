/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Batteries.Util.ProofWanted

namespace MetaMathlibExt

@[expose] public section

/-- **Isoperimetric inequality.** Let $g$ be a continuous, $1$-periodic, Lipschitz map from
$\mathbb{R}$ to the Euclidean plane $\mathbb{R}^2$ that is injective on $[0, 1)$, so that its
image $C = g(\mathbb{R})$ is a simple closed curve, and suppose $C$ has finite
one-dimensional Hausdorff measure. Let $U \subseteq \mathbb{R}^2$ be a bounded, connected open
set whose boundary is $C$. Let $L$ be the one-dimensional Hausdorff measure of $C$ (its
length) and $A$ the Lebesgue measure of $U$ (its area). Then $4 \pi A \le L^2$, and
$4 \pi A = L^2$ if and only if $C$ is a circle, that is, $C = \{x : \lVert x - c \rVert = r\}$
for some point $c \in \mathbb{R}^2$ and some real $r > 0$.

Source: https://en.wikipedia.org/wiki/Isoperimetric_inequality (isoperimetric-s1). -/
theorem_wanted isoperimetric_inequality
    {g : ℝ → EuclideanSpace ℝ (Fin 2)}
    {U : Set (EuclideanSpace ℝ (Fin 2))}
    {L A : ℝ}
    (hg_cont : Continuous g)
    (hg_closed : Function.Periodic g 1)
    (hg_lip : ∃ K, LipschitzWith K g)
    (hg_rect : MeasureTheory.Measure.hausdorffMeasure 1 (Set.range g) ≠ ⊤)
    (hg_simple : Set.InjOn g (Set.Ico (0 : ℝ) 1))
    (hL : L = (MeasureTheory.Measure.hausdorffMeasure 1 (Set.range g)).toReal)
    (hA : A = (MeasureTheory.volume U).toReal)
    (hU_open : IsOpen U)
    (hU_conn : IsConnected U)
    (hU_bdd : Bornology.IsBounded U)
    (hU_front : frontier U = Set.range g) :
    4 * Real.pi * A ≤ L ^ 2 ∧
      (4 * Real.pi * A = L ^ 2 ↔
        ∃ c : EuclideanSpace ℝ (Fin 2), ∃ r : ℝ, 0 < r ∧
          Set.range g = Metric.sphere c r)

end

end MetaMathlibExt