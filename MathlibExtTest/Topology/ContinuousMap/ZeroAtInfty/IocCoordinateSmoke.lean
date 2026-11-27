/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Topology.ContinuousMap.ZeroAtInfty.IocCoordinate
public import Mathlib.Tactic.NormNum

/-!
# The nonzero C0 coordinate on the half-open unit interval

The coordinate on `(0,1]` takes value one at the included endpoint and
one-half at the midpoint. Its norm is one and it tends to zero along the
domain's cocompact filter. Endpoint zero gives the empty-domain zero function.
-/

noncomputable section

open Filter
open scoped ZeroAtInfty Topology

namespace MathlibExtTest.IocCoordinate

open ZeroAtInftyContinuousMap

private def endpoint : Set.Ioc (0 : ℝ) 1 := ⟨1, by norm_num⟩
private def midpoint : Set.Ioc (0 : ℝ) 1 := ⟨1 / 2, by norm_num⟩

example : iocCoordinate 1 endpoint = 1 ∧ ‖iocCoordinate 1‖ = 1 ∧ iocCoordinate 1 ≠ 0 := by
  have he : iocCoordinate 1 endpoint = 1 := by simp [endpoint]
  refine ⟨he, by norm_num, ?_⟩
  intro h
  have hv := congrArg (fun f : C₀(Set.Ioc (0 : ℝ) 1, ℂ) => f endpoint) h
  rw [he] at hv
  norm_num at hv

example : iocCoordinate 1 midpoint = (1 / 2 : ℂ) := by
  norm_num [midpoint]

example :
    Tendsto (iocCoordinate 1 : Set.Ioc (0 : ℝ) 1 → ℂ)
      (cocompact (Set.Ioc (0 : ℝ) 1)) (𝓝 0) := by
  change Tendsto (fun x : Set.Ioc (0 : ℝ) 1 => iocCoordinate 1 x)
    (cocompact (Set.Ioc (0 : ℝ) 1)) (𝓝 0)
  simpa only [iocCoordinate_apply] using iocCoordinate_zero_at_infty 1

example : ‖iocCoordinate 0‖ = 0 ∧ iocCoordinate 0 = 0 := by
  have hn : ‖iocCoordinate 0‖ = 0 := by norm_num
  exact ⟨hn, norm_eq_zero.mp hn⟩

end MathlibExtTest.IocCoordinate
