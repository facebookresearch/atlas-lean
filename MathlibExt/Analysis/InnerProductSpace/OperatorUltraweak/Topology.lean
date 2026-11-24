/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.InnerProductSpace.OperatorUltraweak.Coefficients
public import Mathlib.Topology.Constructions

/-!
# Actual initial operator ultraweak topology

All actual square-summable rank-one coefficient functionals define the
initial topology on bounded operators. Each coefficient is a genuine
convergent bounded complex-linear functional from the previous owner.
This definition uses every such vector pair, including zero and
nonseparable Hilbert spaces. It does not substitute WOT or choose an
unproved trace-dual equivalence. Source least-closed algebra and rational
closure comparison assertions remain whole terminal statements.
-/

@[expose] public section
noncomputable section
open scoped Topology
namespace OperatorUltraweak
universe u v
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Actual evaluation of every original square-summable rank-one coefficient on an operator. -/
def evaluation (T : H →L[ℂ] H) : (VectorSequence H × VectorSequence H) → ℂ :=
  fun p => coefficient p.1 p.2 T

/-- Full actual infinite-series value of the coefficient evaluation map. -/
theorem evaluation_apply (T : H →L[ℂ] H) (x y : VectorSequence H) :
    evaluation T (x, y) = ∑' n : ℕ, inner ℂ (y n) (T (x n)) := coefficient_apply x y T

/-- The actual initial topology induced by all square-summable rank-one operator coefficients. -/
@[instance_reducible]
def topology (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    TopologicalSpace (H →L[ℂ] H) :=
  TopologicalSpace.induced (evaluation (H := H)) inferInstance

/-- Actual ultraweak closedness, retaining the original raw bounded-operator carrier. -/
def IsClosedSet (S : Set (H →L[ℂ] H)) : Prop :=
  @IsClosed (H →L[ℂ] H) (topology H) S

/-- Actual source ultraweak convergence, with every source filter and limit kept explicit. -/
def Tendsto {I : Type*} (T : I → (H →L[ℂ] H)) (l : Filter I) (U : H →L[ℂ] H) : Prop :=
  Filter.Tendsto T l (@nhds (H →L[ℂ] H) (topology H) U)

/-- Convergence in the actual ultraweak topology is equivalent to convergence
of every genuine square-summable coefficient, for every filter and limit. -/
theorem tendsto_iff {I : Type v} (T : I → H →L[ℂ] H) (l : Filter I) (U : H →L[ℂ] H) :
    OperatorUltraweak.Tendsto T l U ↔
      ∀ x y : VectorSequence H,
        Filter.Tendsto (fun i => coefficient x y (T i)) l (𝓝 (coefficient x y U)) := by
  rw [OperatorUltraweak.Tendsto, topology, nhds_induced,
    Filter.tendsto_comap_iff, tendsto_pi_nhds]
  constructor
  · intro h x y
    exact h (x, y)
  · intro h p
    exact h p.1 p.2

/-- Every fixed actual coefficient evaluation is continuous for the defining
ultraweak topology, without any complete-space or trace-dual assumption. -/
theorem continuous_coefficient (x y : VectorSequence H) :
    @Continuous (H →L[ℂ] H) ℂ (topology H) inferInstance (coefficient x y) := by
  letI : TopologicalSpace (H →L[ℂ] H) := topology H
  have he : Continuous (evaluation (H := H)) := continuous_induced_dom
  exact (continuous_apply (x, y)).comp he

/-- Actual closure in the initial ultraweak topology, without a selected closed-subalgebra model. -/
def closure (S : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H) :=
  @_root_.closure (H →L[ℂ] H) (topology H) S

end OperatorUltraweak
