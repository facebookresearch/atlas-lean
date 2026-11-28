/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BALANCED MINIMUM EVOLUTION: definitions

Source:
S. Fiorini and G. Joret, "Approximating the balanced minimum evolution problem", Operations
Research Letters 40 (2012), 31-35, doi:10.1016/j.orl.2011.10.003 (arXiv:1104.1080), Theorem 3.1.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.Tree.WeightedLeafDistance

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BalancedMinimumEvolution

open MathlibExt.Biology.Phylogenetics.BalancedMinimumEvolution (UTree)

/-- An instance: the number `n` of species, the rows of the dissimilarity matrix (entry `(a, b)`
meaning `a / b`), and the bound `L` as a pair `(a, b)` meaning `a / b`. -/
abbrev BalancedMinimumEvolutionInstance := ℕ × List (List (ℕ × ℕ)) × (ℕ × ℕ)

/-- The entry `δᵢⱼ` of the matrix, as a pair `(a, b)` meaning `a / b`. -/
def entry (inst : BalancedMinimumEvolutionInstance) (i j : Fin inst.1) : ℕ × ℕ :=
  (inst.2.1.getD i []).getD j (0, 1)

/-- The dissimilarity `δᵢⱼ = a / b` as a real number. -/
noncomputable def dissim (inst : BalancedMinimumEvolutionInstance) (i j : Fin inst.1) : ℝ :=
  ((entry inst i j).1 : ℝ) / (entry inst i j).2

/-- Well-formedness of an instance: the matrix has `n` rows of `n` entries, every entry has a
positive denominator, the diagonal is zero, the matrix is symmetric (`δᵢⱼ = δⱼᵢ`), and `L` has a
positive denominator. -/
def WellFormed (inst : BalancedMinimumEvolutionInstance) : Prop :=
  inst.2.1.length = inst.1 ∧ (∀ r ∈ inst.2.1, r.length = inst.1 ∧ ∀ q ∈ r, 0 < q.2) ∧
    (∀ i, (entry inst i i).1 = 0) ∧
    (∀ i j, (entry inst i j).1 * (entry inst j i).2 = (entry inst j i).1 * (entry inst i j).2) ∧
    0 < inst.2.2.2

/-- Some cubic tree whose leaves are labelled by the `n` species, each exactly once, has balanced
minimum-evolution length at most `L`. -/
def BalancedMinimumEvolutionFeasible (inst : BalancedMinimumEvolutionInstance) : Prop :=
  ∃ T : UTree (Fin inst.1), T.labels.Perm (List.finRange inst.1) ∧
    T.bmeLength (dissim inst) ≤ (inst.2.2.1 : ℝ) / inst.2.2.2

open Classical in
/-- BALANCED MINIMUM EVOLUTION as a decision problem over bitstrings. -/
noncomputable def balancedMinimumEvolutionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BalancedMinimumEvolutionInstance) x with
  | some i => decide (WellFormed i ∧ BalancedMinimumEvolutionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.BalancedMinimumEvolution
