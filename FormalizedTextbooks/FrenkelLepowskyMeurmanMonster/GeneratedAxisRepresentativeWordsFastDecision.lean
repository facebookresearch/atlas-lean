/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- A bounded full-phase checker using only strictly ordered binary basis pairs. -/
module

public import Mathlib.Algebra.CharP.Two
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWordsPlan

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Explicit diagonal coefficients and ordered pairs suffice for a complete spin edge. -/
def representativeSpinEdgeFast (a b c : RepresentativeSpinModel) : Prop :=
  c.coordinate = b.coordinate * a.coordinate ∧
  (∀ i : Fin 12, a.phase i i + monsterMonomialQuadratic b.phase (a.coordinate.col i) =
    c.phase i i) ∧
  (∀ i j : Fin 12, i < j →
    a.phase i i + a.phase j j + (a.phase i j + a.phase j i) +
      monsterMonomialQuadratic b.phase (a.coordinate.col i + a.coordinate.col j) =
        c.phase i i + c.phase j j + (c.phase i j + c.phase j i))

/-- The cheaper ordered-pair condition is equivalent to the original full edge condition. -/
theorem representativeSpinEdgeFast_iff (a b c : RepresentativeSpinModel) :
    representativeSpinEdgeFast a b c ↔ representativeSpinEdge a b c := by
  constructor
  · rintro ⟨hP, hb, hp⟩
    refine ⟨hP, ?_, ?_⟩
    · intro i
      simpa only [representativeQuadratic_single] using hb i
    · intro i j
      obtain hij | hij | hij := lt_trichotomy i j
      · simpa only [representativeQuadratic_single_add] using hp i j hij
      · subst j
        simp only [monsterMonomialQuadratic, Pi.add_apply, CharTwo.add_self_eq_zero,
          zero_mul, Finset.sum_const_zero]
      · simpa only [representativeQuadratic_single_add, add_comm] using hp j i hij
  · rintro ⟨hP, hb, hp⟩
    refine ⟨hP, ?_, ?_⟩
    · intro i
      simpa only [representativeQuadratic_single] using hb i
    · intro i j _
      simpa only [representativeQuadratic_single_add] using hp i j

/-- A constructive decision procedure computes only the equivalent bounded fast condition.
The proof transfers its result through the proved equivalence, without assuming an edge. -/
def representativeSpinEdgeDecisionFast (a b c : RepresentativeSpinModel) :
    Decidable (representativeSpinEdge a b c) := by
  letI : Decidable (representativeSpinEdgeFast a b c) := by
    unfold representativeSpinEdgeFast
    infer_instance
  exact decidable_of_iff (representativeSpinEdgeFast a b c)
    (representativeSpinEdgeFast_iff a b c)

/-- Plan recursion uses the equivalent fast edge decision at every step. -/
def representativeSpinPlanDecisionFast {ι : Type} (models : ι → RepresentativeSpinModel) :
    (a : RepresentativeSpinModel) → (plan : RepresentativeSpinPlan ι) →
      Decidable (representativeSpinPlanValid models a plan)
  | _, [] => isTrue True.intro
  | a, (letter, next) :: rest => by
      change Decidable (representativeSpinEdge a (models letter) next ∧
        representativeSpinPlanValid models next rest)
      letI := representativeSpinEdgeDecisionFast a (models letter) next
      letI := representativeSpinPlanDecisionFast models next rest
      infer_instance

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
