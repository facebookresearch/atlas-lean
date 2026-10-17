/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.TimeMComplexity

/-!
# `TimeM` declared-polynomial-time predicate public-API and boundary checks

Exact-statement exercises for the `TimeM` declared-time predicates,
`Verifies`, many-one reductions by named functions (identity, doubling,
a two-step composition), the decider-to-verifier construction, the
triviality witness, and axiom audits of the composition and bridge
theorems.
-/

@[expose] public section

namespace TimeMComplexityTests

open Cslib.TimeMComplexity
open MetaMathlibExt.ComplexityTheory (DecisionProblem)

#check DecidesInDeclaredPolyTime
#check ComputesInDeclaredPolyTime
#check VerifierInDeclaredPolyTime
#check Verifies
#check DeclaredPolyManyOneRedVia
#check exists_decidesInDeclaredPolyTime
#check verifierInDeclaredPolyTime_of_decidesInDeclaredPolyTime
#check verifies_of_decides
#check declaredPolyManyOneRedVia_refl
#check declaredPolyManyOneRedVia_trans
#check decidesInDeclaredPolyTime_comp_reduction
#check decides_comp_reduction
#check verifies_comp_reduction
#check mem_P_of_decides
#check mem_NP_of_verifies
#check cookLevinPolyManyOneRed_of_declared

/-- The constantly-true decider runs in polynomial time at zero cost. -/
example : DecidesInDeclaredPolyTime (fun _ => pure true) :=
  ⟨0, fun _ => by simp⟩

/-- The constantly-true decider, ignoring the witness, verifies the
constantly-true problem with bound `0`. -/
example : Verifies (fun xw => (fun _ => pure true) xw.1) (fun _ => true) 0 :=
  verifies_of_decides (f := fun _ => pure true) (fun _ => rfl)

/-- The constantly-true verifier runs in polynomial time, via the
decider-to-verifier construction. -/
example : VerifierInDeclaredPolyTime (fun xw => (fun _ => pure true) xw.1) :=
  verifierInDeclaredPolyTime_of_decidesInDeclaredPolyTime (f := fun _ => pure true)
    ⟨0, fun _ => by simp⟩

/-- The identity function is computable in polynomial time. -/
example : ComputesInDeclaredPolyTime (fun x => pure x) :=
  ⟨Polynomial.X, fun _ => by simp⟩

/-- Every problem reduces to itself by the identity. -/
example (L : DecisionProblem) : DeclaredPolyManyOneRedVia (fun x => pure x) L L :=
  declaredPolyManyOneRedVia_refl L

/-- Doubling the input is computable in polynomial time, with bound
`X + X` for both the declared time and the output length. -/
example : ComputesInDeclaredPolyTime (fun x => ⟨x ++ x, x.length⟩) := by
  refine ⟨Polynomial.X + Polynomial.X, fun x => ⟨?_, ?_⟩⟩
  · show x.length ≤ (Polynomial.X + Polynomial.X).eval x.length
    simp only [Polynomial.eval_add, Polynomial.eval_X]
    omega
  · show (x ++ x).length ≤ (Polynomial.X + Polynomial.X).eval x.length
    simp [List.length_append]

/-- Two identity reductions compose to a reduction. -/
example (L : DecisionProblem) :
    DeclaredPolyManyOneRedVia
      (fun x => (fun y => pure y) x >>= (fun y => pure y)) L L :=
  declaredPolyManyOneRedVia_trans (declaredPolyManyOneRedVia_refl L)
    (declaredPolyManyOneRedVia_refl L)

/-- The triviality witness: an unrestricted `TimeM` decider deciding `L`
in polynomial declared time exists for every `L`. -/
example (L : DecisionProblem) :
    ∃ f, DecidesInDeclaredPolyTime f ∧ ∀ x, (f x).ret = L x :=
  exists_decidesInDeclaredPolyTime L

/-- Behavioral check of verifier composition along a shrinking
reduction. The reduction maps every input to `[true]`; the inner
verifier accepts everything with witness bound `0`. The composed
verifier accepts the empty witness, and rejects the length-`1` witness
through the witness-length guard (`1 ≤ 0` fails at the reduced input),
even though the inner verifier itself would accept. -/
example :
    ∃ p' : Polynomial ℕ,
      VerifierInDeclaredPolyTime (fun xw => (fun _ => pure [true]) xw.1 >>= fun y =>
        (fun b => b && decide (xw.2.length ≤ (0 : Polynomial ℕ).eval y.length)) <$>
          (fun _ => pure true) (y, xw.2)) ∧
      Verifies (fun xw => (fun _ => pure [true]) xw.1 >>= fun y =>
        (fun b => b && decide (xw.2.length ≤ (0 : Polynomial ℕ).eval y.length)) <$>
          (fun _ => pure true) (y, xw.2)) (fun _ => true) p' ∧
      (((fun xw => (fun _ => pure [true]) xw.1 >>= fun y =>
        (fun b => b && decide (xw.2.length ≤ (0 : Polynomial ℕ).eval y.length)) <$>
          (fun _ => pure true) (y, xw.2)) :
          List Bool × List Bool → Cslib.Algorithms.Lean.TimeM Nat Bool)
        ([false, false], [])).ret = true ∧
      (((fun xw => (fun _ => pure [true]) xw.1 >>= fun y =>
        (fun b => b && decide (xw.2.length ≤ (0 : Polynomial ℕ).eval y.length)) <$>
          (fun _ => pure true) (y, xw.2)) :
          List Bool × List Bool → Cslib.Algorithms.Lean.TimeM Nat Bool)
        ([false, false], [true])).ret = false := by
  obtain ⟨p', ht, hv⟩ := verifies_comp_reduction
    (f := fun _ => pure [true]) (V := fun _ => pure true)
    (L₁ := fun _ => true) (L₂ := fun _ => true) (p := 0)
    ⟨⟨1, fun _ => by simp⟩, fun _ => rfl⟩
    ⟨0, fun _ => by simp⟩
    (by
      intro y
      constructor
      · intro _
        exact ⟨[], by simp, rfl⟩
      · intro _
        rfl)
  exact ⟨p', ht, hv, by simp, by simp⟩

/-- A declared reduction upgrades to the canonical `CookLevin`
reduction given canonical polynomial-time evidence for the computed
function. -/
example {f : List Bool → Cslib.Algorithms.Lean.TimeM Nat (List Bool)}
    {L₁ L₂ : DecisionProblem} (hred : DeclaredPolyManyOneRedVia f L₁ L₂)
    (h : MetaMathlibExt.ComplexityTheory.IsPolyTime fun x => (f x).ret) :
    Cslib.CookLevin.PolyManyOneRed L₁ L₂ :=
  cookLevinPolyManyOneRed_of_declared hred h

#print axioms Cslib.TimeMComplexity.verifies_comp_reduction
#print axioms Cslib.TimeMComplexity.mem_NP_of_verifies
#print axioms Cslib.TimeMComplexity.exists_decidesInDeclaredPolyTime

end TimeMComplexityTests
