/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Analysis.InnerProductSpace.LinearPMap.ClosedGraphTransform
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Graph transforms of a concrete bounded diagonal operator

The total real operator multiplying by two has graph y = 2x. Projecting
(x,0) onto this graph gives (x/5,2x/5). At x = 5 the transform is (1,2),
which has a nonzero second coordinate, lies in the actual graph, and retains
its inherited l2 product norm.
-/

noncomputable section

open Set
open scoped InnerProductSpace

namespace MathlibExtTest.ClosedGraphDiagonal

private def twice : ℝ →ₗ.[ℝ] ℝ :=
  ((2 : ℝ) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)).toPMap ⊤

private theorem twice_apply (x : twice.domain) : twice x = 2 * (x : ℝ) := by
  rfl

private theorem twice_closed : twice.IsClosed := by
  have hgraph : (twice.graph : Set (ℝ × ℝ)) =
      {p : ℝ × ℝ | p.2 = 2 * p.1} := by
    ext p
    change p ∈ twice.graph ↔ p.2 = 2 * p.1
    rw [LinearPMap.mem_graph_iff]
    constructor
    · rintro ⟨x, hx, hvalue⟩
      rw [← hx, ← hvalue, twice_apply]
    · intro h
      exact ⟨⟨p.1, Submodule.mem_top⟩, rfl, h.symm⟩
  change IsClosed (twice.graph : Set (ℝ × ℝ))
  rw [hgraph]
  exact isClosed_eq continuous_snd (continuous_const.mul continuous_fst)

private theorem coordinate_values (x : ℝ) :
    LinearPMap.closedGraphFirstTransform twice twice_closed x = x / 5 ∧
      LinearPMap.closedGraphSecondTransform twice twice_closed x = 2 * x / 5 := by
  obtain ⟨hx, hvalue⟩ :=
    LinearPMap.closedGraphTransforms_domain_value twice twice_closed x
  have hsecond : LinearPMap.closedGraphSecondTransform twice twice_closed x =
      2 * LinearPMap.closedGraphFirstTransform twice twice_closed x := by
    exact hvalue.symm
  have hinner := LinearPMap.closedGraphTransform_inner_difference
    twice twice_closed x (⟨1, Submodule.mem_top⟩ : twice.domain)
  have hrelation : x - LinearPMap.closedGraphFirstTransform twice twice_closed x =
      2 * LinearPMap.closedGraphSecondTransform twice twice_closed x := by
    have h := hinner
    simp only [twice_apply, Real.inner_apply, mul_one] at h
    linarith
  constructor <;> linarith

example : twice ⟨3, Submodule.mem_top⟩ = 6 ∧ twice.IsClosed := by
  exact ⟨by norm_num [twice_apply], twice_closed⟩

example :
    LinearPMap.closedGraphFirstTransform twice twice_closed 5 = 1 ∧
      LinearPMap.closedGraphSecondTransform twice twice_closed 5 = 2 := by
  simpa using coordinate_values 5

example :
    LinearPMap.closedGraphTransform twice twice_closed 5 = WithLp.toLp 2 ((1 : ℝ), (2 : ℝ)) := by
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).injective
  apply Prod.ext
  · change LinearPMap.closedGraphFirstTransform twice twice_closed 5 = 1
    simpa using (coordinate_values 5).1
  · change LinearPMap.closedGraphSecondTransform twice twice_closed 5 = 2
    simpa using (coordinate_values 5).2

example :
    LinearPMap.closedGraphTransform twice twice_closed 5 ∈ LinearPMap.closedGraphSubmodule twice ∧
      LinearPMap.closedGraphTransform twice twice_closed 5 ≠ 0 := by
  refine ⟨LinearPMap.closedGraphTransform_mem twice twice_closed 5, ?_⟩
  intro h
  have hsecond : LinearPMap.closedGraphSecondTransform twice twice_closed 5 = 2 := by
    simpa using (coordinate_values 5).2
  change WithLp.sndL 2 ℝ ℝ ℝ (LinearPMap.closedGraphTransform twice twice_closed 5) = 2 at hsecond
  rw [h, map_zero] at hsecond
  norm_num at hsecond

example : LinearPMap.closedGraphTransform twice twice_closed 0 = 0 := by
  exact map_zero _

end MathlibExtTest.ClosedGraphDiagonal
