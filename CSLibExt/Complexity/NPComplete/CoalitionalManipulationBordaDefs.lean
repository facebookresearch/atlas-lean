/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONSTRUCTIVE COALITIONAL WEIGHTED MANIPULATION for Borda with three candidates: definitions

Source:
V. Conitzer, T. Sandholm and J. Lang, "When are elections with few candidates hard to
manipulate?", Journal of the ACM 54(3) (2007), Article 14, doi:10.1145/1236457.1236461,
Definition 1, Theorem 6 and Corollary 1 (reduction from PARTITION).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CoalitionalManipulationBorda

/-- An instance: the nonmanipulators' votes `S` (each a ranking of the candidates `0, 1, 2`,
most preferred first, with its weight), the weights of the manipulators' votes `T`, and the
preferred candidate `p`. -/
abbrev CoalitionalManipulationInstance := List (List ℕ × ℕ) × List ℕ × ℕ

/-- `v` is a vote over the three candidates: it ranks each of `0, 1, 2` exactly once. -/
def IsRanking (v : List ℕ) : Prop := v.Perm [0, 1, 2]

/-- The points that candidate `c` receives from a voter with ranking `v` under the positional
scoring protocol with vector `α`: `α₁` if `c` is ranked first, `α₂` if second, and so on. -/
def points (α : List ℕ) (v : List ℕ) (c : ℕ) : ℕ := α.getD (v.idxOf c) 0

/-- The score `s_α(c)` of candidate `c` under the weighted votes `votes` (ranking, weight): a
vote of weight `w` counts as `w` voters. -/
def score (α : List ℕ) (votes : List (List ℕ × ℕ)) (c : ℕ) : ℕ :=
  (votes.map fun v => v.2 * points α v.1 c).sum

/-- The Borda scoring vector for three candidates, `(2, 1, 0)`. -/
def bordaVector : List ℕ := [2, 1, 0]

/-- Well-formedness of an instance: every vote of `S` ranks the three candidates, and `p` is a
candidate. -/
def WellFormed (i : CoalitionalManipulationInstance) : Prop :=
  (∀ v ∈ i.1, IsRanking v.1) ∧ i.2.2 < 3

/-- Constructive coalitional weighted manipulation under the scoring protocol `α`: the
manipulators can cast votes `T` (one ranking for each manipulator weight) such that, counting
the votes of `S` and `T`, `p` scores strictly more than each other candidate. -/
def ManipulationFeasible (α : List ℕ) (i : CoalitionalManipulationInstance) : Prop :=
  ∃ T : List (List ℕ), T.length = i.2.1.length ∧ (∀ v ∈ T, IsRanking v) ∧
    ∀ c < 3, c ≠ i.2.2 →
      score α (i.1 ++ T.zip i.2.1) c < score α (i.1 ++ T.zip i.2.1) i.2.2

/-- The manipulators can make `p` the unique Borda winner. -/
def CoalitionalManipulationBordaFeasible (i : CoalitionalManipulationInstance) : Prop :=
  ManipulationFeasible bordaVector i

open Classical in
/-- CONSTRUCTIVE COALITIONAL WEIGHTED MANIPULATION for Borda with three candidates as a
decision problem over bitstrings. -/
noncomputable def coalitionalManipulationBordaDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CoalitionalManipulationInstance) x with
  | some i => decide (WellFormed i ∧ CoalitionalManipulationBordaFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.CoalitionalManipulationBorda
