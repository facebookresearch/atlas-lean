/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Rudin H∞ functions with failing limits on rotated arcs (AMR-022-5076)

Along every rotation of a non-tangential arc at `1`, some bounded analytic
function has no limit at the rotated endpoint, for every rotation angle.

NOTE: the sourced problem is ill-formulated as stated. By Fatou's
angular-limit theorem, every bounded analytic function has non-tangential
limits almost everywhere, so for every non-tangential arc `γ` and every
bounded analytic `g`, the limit along some rotated arc exists (see
`fatouObstruction`). Hayman's update to Problem 5.76 notes the same
obstruction. Registered with `resolved_false` status.
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Order.Basic
public import Batteries.Util.ProofWanted

@[expose] public section

open Topology

namespace MathlibExt.Analysis.RudinHInfinityArcLimitsWanted

/-! Source record `AMR-022-5076`. -/

/-- A non-tangential arc at `1`: the injective continuous image of `[0, 1]`
with endpoint `1`, otherwise in the disc, and contained in some Stolz
angle. -/
def IsNonTangentialArc (γ : Set ℂ) : Prop :=
  (1 : ℂ) ∈ γ ∧ (∃ z ∈ γ, z ≠ 1) ∧ γ \ {1} ⊆ Metric.ball 0 1 ∧
  IsCompact γ ∧ IsConnected γ ∧
  (∃ param : ContinuousMap (Set.Icc (0 : ℝ) 1) ℂ, Function.Injective ⇑param ∧
    Set.range ⇑param = γ ∧
    param ⟨0, Set.left_mem_Icc.mpr zero_le_one⟩ = 1) ∧
  ∃ K : ℝ, 0 < K ∧
    ∀ z ∈ γ, ‖1 - z‖ ≤ K * (1 - ‖z‖)

/-- `g` is bounded and analytic on the unit disc. -/
def IsBoundedAnalytic (g : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ g (Metric.ball 0 1) ∧
  ∃ M : ℝ, ∀ z ∈ Metric.ball 0 1, ‖g z‖ ≤ M

/-- Rotation of a set by angle `θ`. -/
def rotateSet (γ : Set ℂ) (θ : ℝ) : Set ℂ :=
  (fun w => Complex.exp (θ * Complex.I) * w) '' γ

/-- [AMR-022-5076] For every non-tangential arc at `1` there is a bounded
analytic `g` whose limit along each rotated arc at the rotated endpoint fails
to exist, for every rotation angle. -/
def conjecture : Prop :=
  ∀ γ : Set ℂ, IsNonTangentialArc γ →
    ∃ g : ℂ → ℂ, IsBoundedAnalytic g ∧ ∀ θ : ℝ,
      ¬ ∃ l : ℂ, Filter.Tendsto g
        (𝓝[rotateSet γ θ \ {Complex.exp (θ * Complex.I)}]
          (Complex.exp (θ * Complex.I))) (𝓝 l)

/-- The negation of `conjecture` (unregistered companion). -/
def disprovedConjecture : Prop := ¬conjecture

/-- Fatou obstruction (established, external, not machine-checked): for every
non-tangential arc `γ` and every bounded analytic `g`, the limit of `g`
along some rotated arc exists. This follows from Fatou's angular-limit
theorem (see Collingwood–Lohwater and Hayman's update to Problem 5.76),
and it refutes `conjecture`. -/
def fatouObstruction : Prop :=
  ∀ γ : Set ℂ, IsNonTangentialArc γ →
    ∀ g : ℂ → ℂ, IsBoundedAnalytic g →
      ∃ θ : ℝ, ∃ l : ℂ, Filter.Tendsto g
        (𝓝[rotateSet γ θ \ {Complex.exp (θ * Complex.I)}]
          (Complex.exp (θ * Complex.I))) (𝓝 l)

/--
Resolved false: Hayman's update to Problem 5.76 flags the problem as ill-formulated: Fatou's
angular-limit theorem gives non-tangential limits almost everywhere, so for every non-tangential
arc and every bounded analytic g the limit along some rotated arc exists (see
`fatouObstruction`). This target is refuted: For every non-tangential arc and bounded analytic
g, Fatou's angular-limit theorem (Collingwood and Lohwater, p. 21) gives a limit along the arc
rotated to almost every boundary point, so no g fails for every rotation; Hayman-Lingham Update
5.76 notes this obstruction. Source: Collingwood, E. F., Lohwater, A. J., The Theory of Cluster
Sets, Cambridge Univ. Press (1966); W. K. Hayman and E. F. Lingham, Research Problems in
Function Theory (Fiftieth Anniversary Edition), arXiv:1809.07200v2, Update 5.76,
https://arxiv.org/abs/1809.07200v2. Moved from
`OpenConjectures/Analysis/RudinHInfinityArcLimits`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

/--
Resolved false: Hayman's update to Problem 5.76 flags the problem as ill-formulated: Fatou's
angular-limit theorem gives non-tangential limits almost everywhere, so for every non-tangential
arc and every bounded analytic g the limit along some rotated arc exists (see
`fatouObstruction`). This target holds: Fatou's angular-limit theorem (Collingwood and Lohwater,
p. 21): a bounded analytic function on the disc has a limit within every Stolz angle at almost
every point of T, and each rotated non-tangential arc lies in a Stolz angle at its endpoint.
Source: Collingwood, E. F., Lohwater, A. J., The Theory of Cluster Sets, Cambridge Univ. Press
(1966); W. K. Hayman and E. F. Lingham, Research Problems in Function Theory (Fiftieth
Anniversary Edition), arXiv:1809.07200v2, Update 5.76, https://arxiv.org/abs/1809.07200v2. Moved
from `OpenConjectures/Analysis/RudinHInfinityArcLimits`.
-/
public theorem_wanted fatouObstruction_holds : fatouObstruction

end MathlibExt.Analysis.RudinHInfinityArcLimitsWanted
