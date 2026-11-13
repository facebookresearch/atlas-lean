/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Assembly.MergeCost
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# Entropy lower bound for alphabetic merge trees

The PowerSort upper bound is most useful when compared with the best
alphabetic merge tree on the same formed leaves.  This module proves the
standard Shannon lower bound directly for the concrete `MergeTree` cost used
by the project.  It does not assume that an optimum has already been chosen.
-/

namespace CPythonListsort

/-- Entropy multiplied by its total mass, written without normalized list
fractions.  Positivity hypotheses in the lemmas below keep every logarithm on
its intended positive domain. -/
noncomputable def weightedBinaryEntropy (total : Nat)
    (lengths : List Nat) : Real :=
  (lengths.map fun length : Nat =>
    (length : Real) * Real.logb 2 ((total : Real) / (length : Real))).sum

@[simp]
theorem weightedBinaryEntropy_append (total : Nat) (left right : List Nat) :
    weightedBinaryEntropy total (left ++ right) =
      weightedBinaryEntropy total left + weightedBinaryEntropy total right := by
  simp [weightedBinaryEntropy]

private theorem binaryEntropyTerm_add_complement_le_one
    (p : Real) :
    binaryEntropyTerm p + binaryEntropyTerm (1 - p) ≤ 1 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbound := Real.binEntropy_le_log_two (p := p)
  have heq :
      binaryEntropyTerm p + binaryEntropyTerm (1 - p) =
        Real.binEntropy p / Real.log 2 := by
    simp only [binaryEntropyTerm, Real.logb, Real.binEntropy]
    ring
  rw [heq]
  exact (div_le_iff₀ hlog).2 (by simpa using hbound)

/-- Changing the normalization total adds one common logarithmic offset to
every positive length. -/
theorem weightedBinaryEntropy_change_total
    (lengths : List Nat) (oldTotal newTotal : Nat)
    (hold : 0 < oldTotal) (hnew : 0 < newTotal)
    (hpositive : ∀ length ∈ lengths, 0 < length) :
    weightedBinaryEntropy newTotal lengths =
      weightedBinaryEntropy oldTotal lengths +
        (lengths.sum : Real) *
          Real.logb 2 ((newTotal : Real) / (oldTotal : Real)) := by
  induction lengths with
  | nil => simp [weightedBinaryEntropy]
  | cons length rest ih =>
      have hlength : 0 < length := hpositive length (by simp)
      have hrest : ∀ candidate ∈ rest, 0 < candidate := by
        intro candidate hcandidate
        exact hpositive candidate (by simp [hcandidate])
      change
        (length : Real) *
              Real.logb 2 ((newTotal : Real) / (length : Real)) +
            weightedBinaryEntropy newTotal rest =
          (length : Real) *
              Real.logb 2 ((oldTotal : Real) / (length : Real)) +
            weightedBinaryEntropy oldTotal rest +
              ((length + rest.sum : Nat) : Real) *
                Real.logb 2 ((newTotal : Real) / (oldTotal : Real))
      rw [ih hrest]
      have holdReal : (oldTotal : Real) ≠ 0 := by positivity
      have hnewReal : (newTotal : Real) ≠ 0 := by positivity
      have hlengthReal : (length : Real) ≠ 0 := by positivity
      have hfactor :
          (newTotal : Real) / (length : Real) =
            ((newTotal : Real) / (oldTotal : Real)) *
              ((oldTotal : Real) / (length : Real)) := by
        field_simp
      rw [hfactor, Real.logb_mul]
      · push_cast
        ring
      · exact div_ne_zero hnewReal holdReal
      · exact div_ne_zero holdReal hlengthReal

/-- Splitting a positive total into two positive parts contributes at most
one bit of top-level entropy. -/
theorem weightedBinaryEntropy_binary_split_le
    (leftTotal rightTotal : Nat)
    (hleft : 0 < leftTotal) (hright : 0 < rightTotal) :
    (leftTotal : Real) *
          Real.logb 2
            (((leftTotal + rightTotal : Nat) : Real) /
              (leftTotal : Real)) +
        (rightTotal : Real) *
          Real.logb 2
            (((leftTotal + rightTotal : Nat) : Real) /
              (rightTotal : Real)) ≤
      (leftTotal + rightTotal : Nat) := by
  let total : Real := (leftTotal + rightTotal : Nat)
  let p : Real := (leftTotal : Real) / total
  have htotal : 0 < total := by
    dsimp [total]
    positivity
  have htotalNe : total ≠ 0 := htotal.ne'
  have hleftReal : (leftTotal : Real) ≠ 0 := by positivity
  have hrightReal : (rightTotal : Real) ≠ 0 := by positivity
  have hpInv : p⁻¹ = total / (leftTotal : Real) := by
    dsimp [p]
    field_simp
  have hcomp : 1 - p = (rightTotal : Real) / total := by
    dsimp [p, total]
    push_cast
    field_simp
    ring
  have hcompInv : (1 - p)⁻¹ = total / (rightTotal : Real) := by
    rw [hcomp]
    field_simp
  have hscaled :
      (leftTotal : Real) *
            Real.logb 2 (total / (leftTotal : Real)) +
          (rightTotal : Real) *
            Real.logb 2 (total / (rightTotal : Real)) =
        total *
          (binaryEntropyTerm p + binaryEntropyTerm (1 - p)) := by
    rw [binaryEntropyTerm, binaryEntropyTerm, hpInv, hcompInv, hcomp]
    dsimp [p]
    field_simp
  change
    (leftTotal : Real) *
          Real.logb 2 (total / (leftTotal : Real)) +
        (rightTotal : Real) *
          Real.logb 2 (total / (rightTotal : Real)) ≤ total
  rw [hscaled]
  nlinarith [binaryEntropyTerm_add_complement_le_one p]

/-- The unnormalized entropy of the leaves of every positive merge tree is a
lower bound for its merge cost.  Alphabeticity is built into leaf order but
is not otherwise needed for this information-theoretic inequality. -/
private theorem MergeTree.totalLength_pos_of_runLengths_positive
    (tree : MergeTree)
    (hpositive : ∀ length ∈ tree.runLengths, 0 < length) :
    0 < tree.totalLength := by
  induction tree with
  | leaf length =>
      simpa [MergeTree.runLengths, MergeTree.totalLength] using
        hpositive length (by simp [MergeTree.runLengths])
  | merge power left right ihLeft ihRight =>
      have hleft : ∀ length ∈ left.runLengths, 0 < length := by
        intro length hlength
        exact hpositive length (by simp [MergeTree.runLengths, hlength])
      have hright : ∀ length ∈ right.runLengths, 0 < length := by
        intro length hlength
        exact hpositive length (by simp [MergeTree.runLengths, hlength])
      have hleftTotal := ihLeft hleft
      have hrightTotal := ihRight hright
      simp only [MergeTree.totalLength]
      omega

theorem MergeTree.weightedBinaryEntropy_le_mergeCost
    (tree : MergeTree)
    (hpositive : ∀ length ∈ tree.runLengths, 0 < length) :
    weightedBinaryEntropy tree.totalLength tree.runLengths ≤
      (tree.mergeCost : Real) := by
  induction tree with
  | leaf length =>
      have hlength : 0 < length := hpositive length (by simp [MergeTree.runLengths])
      simp [weightedBinaryEntropy, MergeTree.runLengths,
        MergeTree.totalLength, MergeTree.mergeCost, hlength.ne']
  | merge power left right ihLeft ihRight =>
      have hleftPositive : ∀ length ∈ left.runLengths, 0 < length := by
        intro length hlength
        exact hpositive length (by simp [MergeTree.runLengths, hlength])
      have hrightPositive : ∀ length ∈ right.runLengths, 0 < length := by
        intro length hlength
        exact hpositive length (by simp [MergeTree.runLengths, hlength])
      have hleftTotal : 0 < left.totalLength := by
        exact left.totalLength_pos_of_runLengths_positive hleftPositive
      have hrightTotal : 0 < right.totalLength := by
        exact right.totalLength_pos_of_runLengths_positive hrightPositive
      have hleftShift := weightedBinaryEntropy_change_total
        left.runLengths left.totalLength
        (left.totalLength + right.totalLength)
        hleftTotal (by omega) hleftPositive
      have hrightShift := weightedBinaryEntropy_change_total
        right.runLengths right.totalLength
        (left.totalLength + right.totalLength)
        hrightTotal (by omega) hrightPositive
      have hsplit := weightedBinaryEntropy_binary_split_le
        left.totalLength right.totalLength hleftTotal hrightTotal
      simp only [MergeTree.runLengths, MergeTree.totalLength,
        MergeTree.mergeCost, weightedBinaryEntropy_append]
      rw [hleftShift, hrightShift]
      rw [left.sum_runLengths, right.sum_runLengths]
      push_cast at hsplit ⊢
      nlinarith [ihLeft hleftPositive, ihRight hrightPositive]

/-- The normalized binary entropy of a positive run profile is at most the
cost of every merge tree with exactly those leaves. -/
theorem RunProfile.entropy_mul_le_mergeCost
    {n : Nat} (profile : RunProfile n) (tree : MergeTree)
    (hlengths : tree.runLengths = profile.lengths) :
    (n : Real) * profile.entropy ≤ (tree.mergeCost : Real) := by
  by_cases hn : n = 0
  · subst n
    simp
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have htreePositive : ∀ length ∈ tree.runLengths, 0 < length := by
      intro length hlength
      exact profile.positive length (by simpa [hlengths] using hlength)
    have htotal : tree.totalLength = n := by
      rw [← tree.sum_runLengths, hlengths, profile.sum_eq]
    have hscaled :
        (n : Real) * profile.entropy =
          weightedBinaryEntropy n profile.lengths := by
      unfold RunProfile.entropy RunProfile.fractions binaryEntropy
      simp only [List.map_map]
      rw [← List.sum_map_mul_left]
      unfold weightedBinaryEntropy
      apply congrArg List.sum
      apply List.map_congr_left
      intro length hlength
      have hlengthPos := profile.positive length hlength
      have hnReal : (n : Real) ≠ 0 := by positivity
      simp only [Function.comp_apply, binaryEntropyTerm]
      rw [inv_div]
      field_simp
    rw [hscaled, ← hlengths, ← htotal]
    exact tree.weightedBinaryEntropy_le_mergeCost htreePositive

namespace MergeTree

/-- A concrete right-associated alphabetic tree on one nonempty length list.
Its labels are irrelevant to cost and are set to zero. -/
def ofLengths : Nat → List Nat → MergeTree
  | first, [] => .leaf first
  | first, second :: rest =>
      .merge 0 (.leaf first) (ofLengths second rest)

@[simp]
theorem runLengths_ofLengths (first : Nat) (rest : List Nat) :
    (ofLengths first rest).runLengths = first :: rest := by
  induction rest generalizing first with
  | nil => rfl
  | cons second rest ih =>
      simp [ofLengths, MergeTree.runLengths, ih]

end MergeTree

namespace MergePlan

/-- A concrete alphabetic plan for every length list, including the empty
list.  It witnesses that the set minimized below is never empty. -/
def ofLengths : List Nat → MergePlan
  | [] => .empty
  | first :: rest => .tree (MergeTree.ofLengths first rest)

@[simp]
theorem runLengths_ofLengths (lengths : List Nat) :
    (ofLengths lengths).runLengths = lengths := by
  cases lengths with
  | nil => rfl
  | cons first rest =>
      simp [ofLengths, MergePlan.runLengths]

end MergePlan

/-- A natural number occurs as the merge cost of an alphabetic plan with the
given left-to-right leaf lengths. -/
def HasAlphabeticMergeCost (lengths : List Nat) (cost : Nat) : Prop :=
  ∃ plan : MergePlan,
    plan.runLengths = lengths ∧ plan.mergeCost = cost

theorem exists_alphabeticMergeCost (lengths : List Nat) :
    ∃ cost, HasAlphabeticMergeCost lengths cost := by
  let plan := MergePlan.ofLengths lengths
  exact ⟨plan.mergeCost, plan, MergePlan.runLengths_ofLengths lengths, rfl⟩

/-- Minimum merge cost among all alphabetic plans with the displayed leaf
sequence.  `Nat.find` is legitimate because `MergePlan.ofLengths` gives an
explicit witness for every list, including `[]`. -/
noncomputable def optimalAlphabeticMergeCost (lengths : List Nat) : Nat :=
  by
    classical
    exact Nat.find (exists_alphabeticMergeCost lengths)

theorem optimalAlphabeticMergeCost_spec (lengths : List Nat) :
    HasAlphabeticMergeCost lengths
      (optimalAlphabeticMergeCost lengths) := by
  classical
  exact Nat.find_spec (exists_alphabeticMergeCost lengths)

theorem optimalAlphabeticMergeCost_le (lengths : List Nat)
    (plan : MergePlan) (hlengths : plan.runLengths = lengths) :
    optimalAlphabeticMergeCost lengths ≤ plan.mergeCost := by
  classical
  apply Nat.find_min' (exists_alphabeticMergeCost lengths)
  exact ⟨plan, hlengths, rfl⟩

/-- The empty leaf sequence has exact optimal alphabetic merge cost zero. -/
@[simp]
theorem optimalAlphabeticMergeCost_nil :
    optimalAlphabeticMergeCost [] = 0 := by
  apply Nat.eq_zero_of_le_zero
  simpa [MergePlan.runLengths, MergePlan.mergeCost] using
    optimalAlphabeticMergeCost_le [] MergePlan.empty rfl

/-- A singleton leaf needs no merge, so its exact optimal alphabetic cost is
zero for every (including zero) displayed weight. -/
@[simp]
theorem optimalAlphabeticMergeCost_singleton (length : Nat) :
    optimalAlphabeticMergeCost [length] = 0 := by
  apply Nat.eq_zero_of_le_zero
  simpa [MergePlan.runLengths, MergePlan.mergeCost, MergeTree.runLengths,
    MergeTree.mergeCost] using
    optimalAlphabeticMergeCost_le [length]
      (.tree (.leaf length)) rfl

/-- Profile entropy is a lower bound for every empty-or-tree merge plan with
the same positive leaf profile. -/
theorem RunProfile.entropy_mul_le_planMergeCost
    {n : Nat} (profile : RunProfile n) (plan : MergePlan)
    (hlengths : plan.runLengths = profile.lengths) :
    (n : Real) * profile.entropy ≤ (plan.mergeCost : Real) := by
  cases plan with
  | empty =>
      have hnil : profile.lengths = [] := by
        simpa [MergePlan.runLengths] using hlengths.symm
      have hn : n = 0 := by
        rw [← profile.sum_eq, hnil]
        simp
      subst n
      simp
  | tree root =>
      exact profile.entropy_mul_le_mergeCost root
        (by simpa [MergePlan.runLengths] using hlengths)

/-- The optimum itself satisfies the Shannon lower bound. -/
theorem RunProfile.entropy_mul_le_optimalAlphabeticMergeCost
    {n : Nat} (profile : RunProfile n) :
    (n : Real) * profile.entropy ≤
      (optimalAlphabeticMergeCost profile.lengths : Real) := by
  rcases optimalAlphabeticMergeCost_spec profile.lengths with
    ⟨plan, hlengths, hcost⟩
  rw [← hcost]
  exact profile.entropy_mul_le_planMergeCost plan hlengths

/-- Any implementation cost already bounded by `nH + 2n` is therefore within
`2n` of every alphabetic merge tree on the same formed leaves. -/
theorem mergeCost_le_any_alphabetic_add_two
    {n implementationCost : Nat} (profile : RunProfile n)
    (himplementation :
      (implementationCost : Real) ≤
        (n : Real) * profile.entropy + 2 * (n : Real))
    (tree : MergeTree)
    (hlengths : tree.runLengths = profile.lengths) :
    (implementationCost : Real) ≤
      (tree.mergeCost : Real) + 2 * (n : Real) := by
  have hlower := profile.entropy_mul_le_mergeCost tree hlengths
  nlinarith

/-- Named optimum corollary: the same entropy upper bound places the
implementation within `2n` of the best alphabetic merge plan on its actual
formed leaves. -/
theorem mergeCost_le_optimalAlphabetic_add_two
    {n implementationCost : Nat} (profile : RunProfile n)
    (himplementation :
      (implementationCost : Real) ≤
        (n : Real) * profile.entropy + 2 * (n : Real)) :
    (implementationCost : Real) ≤
      (optimalAlphabeticMergeCost profile.lengths : Real) +
        2 * (n : Real) := by
  have hlower := profile.entropy_mul_le_optimalAlphabeticMergeCost
  nlinarith

end CPythonListsort
