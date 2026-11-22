/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Basic
public import CSLibExt.Computability.Complexity.PairProjection

/-!
# Consequences of canonical polynomial-time reductions

A deterministic decider becomes an NP verifier by projecting the input out of the
canonically encoded input/certificate pair; the certificate bound is zero. Polynomial-time
many-one reductions transfer P membership from their target to their source. Together these
facts give the usual consequence that an NP-complete problem in P implies P = NP.

All classes here are the canonical `FinTM2` classes, not declared-cost or multi-tape analogues.
-/

@[expose] public section

namespace Cslib.Complexity

/-- Every polynomial-time decider is an NP verifier that ignores an empty certificate. -/
theorem P_subset_NP : P ⊆ NP := by
  intro L hL
  refine ⟨0, L ∘ Prod.fst, isPolyTime_fst.comp hL, ?_⟩
  intro x
  constructor
  · intro hx
    exact ⟨[], by simp, hx⟩
  · rintro ⟨w, _, hw⟩
    exact hw

/-- P membership transfers from the target of a polynomial-time many-one reduction to its
source. -/
theorem PolyManyOneRed.mem_P {A B : DecisionProblem}
    (h : PolyManyOneRed A B) (hB : B ∈ P) : A ∈ P := by
  obtain ⟨f, hf, he⟩ := h
  have hEq : A = B ∘ f := funext he
  rw [hEq]
  exact MetaMathlibExt.ComplexityTheory.comp_mem_P hB hf

/-- A polynomial-time decider for an NP-hard language decides every language in NP in
polynomial time. -/
theorem NPHard.NP_subset_P {L : DecisionProblem} (h : NPHard L) (hP : L ∈ P) : NP ⊆ P := by
  intro A hA
  exact (h A hA).mem_P hP

/-- If any canonically NP-complete language belongs to P, then canonical P and NP coincide. -/
theorem NPComplete.P_eq_NP {L : DecisionProblem} (h : NPComplete L) (hP : L ∈ P) : P = NP :=
  Set.Subset.antisymm P_subset_NP (h.npHard.NP_subset_P hP)

end Cslib.Complexity
