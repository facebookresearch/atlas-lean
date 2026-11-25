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

public import MathlibExt.Analysis.CStarAlgebra.GNS.UniversalRepresentation
public import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Tactic.NormNum

/-!
# Nondegeneracy of the actual all-state GNS Hilbert sum

The original-A cyclic spans and the stock arbitrary-index single-coordinate
sums give dense coefficient span. No faithful representation, desired cyclic
family or nondegeneracy certificate is an input.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace CStarAlgebra

universe uA

variable (A : Type uA) [NonUnitalCStarAlgebra A]

attribute [local instance] universalStateOrder universalStateStarOrder universalStateOperatorCStar

/-- Let `A` be a possibly nonunital complex C*-algebra. Its normalized states are positive
complex-linear functionals whose associated continuous linear functional has operator norm one.

The universal coefficient-range span, on the all-state Hilbert sum. -/
def universalStateCoefficientSpan : Submodule ℂ (UniversalStateGNSpace A) :=
  Submodule.span ℂ (Set.range fun p : A × UniversalStateGNSpace A =>
    universalStateGNSRepresentation A p.1 p.2)

/-- Let `A` be a possibly nonunital complex C*-algebra. Its normalized states are positive
complex-linear functionals whose associated continuous linear functional has operator norm one.

The universal representation is nondegenerate by its state cyclic spans. -/
theorem dense_universalStateCoefficientSpan :
    Dense (universalStateCoefficientSpan A : Set (UniversalStateGNSpace A)) := by
  classical
  let U := (universalStateCoefficientSpan A).topologicalClosure
  have hUclosed : IsClosed (U : Set (UniversalStateGNSpace A)) :=
    (universalStateCoefficientSpan A).isClosed_topologicalClosure
  have hsingle (s : NormalizedStateIndex A) (x : StateGNSpace A s) : lp.single 2 s x ∈ U := by
    let J : StateGNSpace A s →L[ℂ] UniversalStateGNSpace A :=
      lp.singleContinuousLinearMap ℂ (StateGNSpace A) 2 s
    let V : Submodule ℂ (StateGNSpace A s) := U.comap J.toLinearMap
    have hVclosed : IsClosed (V : Set (StateGNSpace A s)) := hUclosed.preimage J.continuous
    have hspan : Submodule.span ℂ (Set.range fun a : A =>
        s.1.gnsNonUnitalStarAlgHom a (universalStateCyclicVector A s)) ≤ V := by
      apply Submodule.span_le.mpr
      rintro _ ⟨a, rfl⟩
      change lp.single 2 s
        (s.1.gnsNonUnitalStarAlgHom a (universalStateCyclicVector A s)) ∈ U
      rw [← universalStateGNSOperator_single A a s]
      apply (universalStateCoefficientSpan A).le_topologicalClosure
      exact Submodule.subset_span ⟨(a, lp.single 2 s (universalStateCyclicVector A s)), rfl⟩
    have hx := closure_mono
      (show (Submodule.span ℂ (Set.range fun a : A =>
        s.1.gnsNonUnitalStarAlgHom a (universalStateCyclicVector A s)) :
          Set (StateGNSpace A s)) ⊆ V from hspan)
      (dense_universalStateCyclicVector_span A s x)
    rw [hVclosed.closure_eq] at hx
    exact hx
  have htop : U = ⊤ := by
    apply Submodule.eq_top_iff'.mpr
    intro x
    exact hUclosed.mem_of_tendsto (lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) x)
      (Filter.Eventually.of_forall fun t : Finset (NormalizedStateIndex A) =>
        U.sum_mem fun s _ => hsingle s (x s))
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr htop

end CStarAlgebra
