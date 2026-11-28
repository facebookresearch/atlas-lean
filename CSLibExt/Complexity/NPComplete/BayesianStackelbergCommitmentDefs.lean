/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# OPTIMAL MIXED STRATEGY TO COMMIT TO in two-player Bayesian games: definitions

Source:
V. Conitzer and T. Sandholm, "Computing the optimal strategy to commit to", Proceedings of the
7th ACM Conference on Electronic Commerce (EC 2006), 82-90, doi:10.1145/1134707.1134717,
Sections 2.1, 3.1, Theorem 7 (NP-hardness), and the linear programs in the proofs of Theorems 2
and 8 (adapted below for membership in NP).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BayesianStackelbergCommitment

/-- An instance: the number `m` of leader actions, the number `n` of follower actions, the
prior weights of the follower types, the leader's utility table (`m` rows of `n` entries), one
utility table of the follower per type, and the threshold `((a, b), d)` standing for
`(a - b) / d`. -/
abbrev BayesianStackelbergCommitmentInstance :=
  ℕ × ℕ × List ℕ × List (List (ℕ × ℕ)) × List (List (List (ℕ × ℕ))) × ((ℕ × ℕ) × ℕ)

/-- The integer encoded by a `(positive part, negative part)` pair, as a real number. -/
def intVal (z : ℕ × ℕ) : ℝ := (z.1 : ℝ) - z.2

/-- The prior probability `π θ = w θ / ∑ w` of follower type `θ`. -/
noncomputable def prior (i : BayesianStackelbergCommitmentInstance) (θ : Fin i.2.2.1.length) :
    ℝ :=
  (i.2.2.1.getD θ 0 : ℝ) / (i.2.2.1.sum : ℝ)

/-- The leader's utility `u_l(s, t)`. -/
def leaderUtility (i : BayesianStackelbergCommitmentInstance) (s : Fin i.1) (t : Fin i.2.1) :
    ℝ :=
  intVal ((i.2.2.2.1.getD s []).getD t (0, 0))

/-- The follower's utility `u_f^θ(s, t)` in type `θ`. -/
def followerUtility (i : BayesianStackelbergCommitmentInstance) (θ : Fin i.2.2.1.length)
    (s : Fin i.1) (t : Fin i.2.1) : ℝ :=
  intVal (((i.2.2.2.2.1.getD θ []).getD s []).getD t (0, 0))

/-- The threshold `k = (a - b) / d`. -/
noncomputable def threshold (i : BayesianStackelbergCommitmentInstance) : ℝ :=
  intVal i.2.2.2.2.2.1 / (i.2.2.2.2.2.2 : ℝ)

/-- Well-formedness of an instance: both players have at least one action, the prior weights
have a positive sum, the leader's table and every follower type's table have `m` rows of `n`
entries, and the threshold's denominator is positive. -/
def WellFormed (i : BayesianStackelbergCommitmentInstance) : Prop :=
  0 < i.1 ∧ 0 < i.2.1 ∧ 0 < i.2.2.1.sum ∧
    (i.2.2.2.1.length = i.1 ∧ ∀ row ∈ i.2.2.2.1, row.length = i.2.1) ∧
    i.2.2.2.2.1.length = i.2.2.1.length ∧
    (∀ tab ∈ i.2.2.2.2.1, tab.length = i.1 ∧ ∀ row ∈ tab, row.length = i.2.1) ∧
    0 < i.2.2.2.2.2.2

/-- Some mixed strategy `p` of the leader, with some best response `t θ` of every follower
type `θ` to `p`, gives the leader expected utility at least `k`. -/
def BayesianStackelbergCommitmentFeasible (i : BayesianStackelbergCommitmentInstance) : Prop :=
  ∃ p : Fin i.1 → ℝ, (∀ s, 0 ≤ p s) ∧ ∑ s, p s = 1 ∧
    ∃ t : Fin i.2.2.1.length → Fin i.2.1,
      (∀ θ t', ∑ s, p s * followerUtility i θ s t' ≤ ∑ s, p s * followerUtility i θ s (t θ)) ∧
        threshold i ≤ ∑ θ, prior i θ * ∑ s, p s * leaderUtility i s (t θ)

open Classical in
/-- OPTIMAL MIXED STRATEGY TO COMMIT TO (Bayesian games) as a decision problem over
bitstrings. -/
noncomputable def bayesianStackelbergCommitmentDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BayesianStackelbergCommitmentInstance) x with
  | some i => decide (WellFormed i ∧ BayesianStackelbergCommitmentFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.BayesianStackelbergCommitment
