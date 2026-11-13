/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Assembly.MergeCost
import Code.Assembly.PowerEntropyBound

/-!
# Entropy bound for a source-faithful PowerSort merge tree

This module is the pure bridge between the transcribed node-power arithmetic
and the implementation-independent merge-cost accounting.  A valid tree has
positive leaves laid out contiguously in source order.  Every internal label is
the actual `powerloop` result for the two aggregate child spans, and internal
labels strictly increase from a parent to each internal child.  The latter is
the min-Cartesian heap property used by Munro--Wild.

No fact about the implementation trace is assumed here.  A later bridge only
has to construct `PowerMergePlanValid` for the tree replayed from that trace.
-/

namespace CPythonListsort

namespace MergeTree

/-- The label at an internal root, if the tree is not a leaf. -/
def rootPower : MergeTree → Option Nat
  | .leaf _ => none
  | .merge power _ _ => some power

/-- Source-faithful validity of a power-labelled ordered merge tree.

`listBase` is the absolute base of the complete input, `listLength` is its
finite-width length, and `base` is the absolute base of this subtree.  The
recursive bases force the leaves to be contiguous and in source order.  At an
internal node, `power` is exactly the transcribed `powerloop` result for the
aggregate left and right spans.  The final two clauses are the strict
min-Cartesian heap condition for internal children; leaves carry no node
power. -/
def PowerValid (listBase : Nat) (listLength : PySSize) :
    Nat → MergeTree → Prop
  | base, .leaf length =>
      listBase ≤ base ∧
        base + length ≤ listBase + listLength.toNat ∧
        0 < length
  | base, .merge power left right =>
      listBase ≤ base ∧
        base + left.totalLength + right.totalLength ≤
          listBase + listLength.toNat ∧
        PowerValid listBase listLength base left ∧
        PowerValid listBase listLength (base + left.totalLength) right ∧
        ValidPowerloopInput
          (BitVec.ofNat 64 (base - listBase))
          (BitVec.ofNat 64 left.totalLength)
          (BitVec.ofNat 64 right.totalLength)
          listLength ∧
        power = powerloop
          (BitVec.ofNat 64 (base - listBase))
          (BitVec.ofNat 64 left.totalLength)
          (BitVec.ofNat 64 right.totalLength)
          listLength ∧
        (∀ childPower, left.rootPower = some childPower → power < childPower) ∧
        (∀ childPower, right.rootPower = some childPower → power < childPower)

/-- Every leaf of a valid power tree has positive length. -/
theorem PowerValid.leaf_positive
    {listBase base : Nat} {listLength : PySSize} {tree : MergeTree}
    (hvalid : tree.PowerValid listBase listLength base) :
    ∀ length ∈ tree.runLengths, 0 < length := by
  induction tree generalizing base with
  | leaf length =>
      intro candidate hcandidate
      simp only [runLengths, List.mem_singleton] at hcandidate
      subst candidate
      exact hvalid.2.2
  | merge power left right ihLeft ihRight =>
      intro length hlength
      simp only [runLengths, List.mem_append] at hlength
      rcases hlength with hleft | hright
      · exact ihLeft hvalid.2.2.1 length hleft
      · exact ihRight hvalid.2.2.2.1 length hright

private theorem ofNat64_toNat_of_lt {x : Nat} (hx : x < 2 ^ 64) :
    (BitVec.ofNat 64 x).toNat = x := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]

/-- The exact power at an internal node is below the logarithmic inverse-size
bound for every positive leaf in that node's span. -/
theorem PowerValid.nodePower_lt_logb
    {listBase base : Nat} {listLength : PySSize}
    {power : Nat} {left right : MergeTree}
    (hvalid : PowerValid listBase listLength base (.merge power left right))
    {leafLength : Nat} (hleaf : 0 < leafLength)
    (hleafSpan : leafLength ≤ left.totalLength + right.totalLength) :
    (power : Real) <
      Real.logb 2
        ((listLength.toNat : Real) / (leafLength : Real)) + 2 := by
  rcases hvalid with
    ⟨hbase, hwithin, _hleft, _hright, hinput, hpower, _⟩
  have hspan : left.totalLength + right.totalLength ≤ listLength.toNat := by
    omega
  have hleft64 : left.totalLength < 2 ^ 64 :=
    lt_of_le_of_lt (le_trans (Nat.le_add_right _ _) hspan) listLength.isLt
  have hright64 : right.totalLength < 2 ^ 64 :=
    lt_of_le_of_lt (le_trans (Nat.le_add_left _ _) hspan) listLength.isLt
  have hleftExact : (BitVec.ofNat 64 left.totalLength).toNat =
      left.totalLength := ofNat64_toNat_of_lt hleft64
  have hrightExact : (BitVec.ofNat 64 right.totalLength).toNat =
      right.totalLength := ofNat64_toNat_of_lt hright64
  rw [hpower]
  apply powerloop_lt_logb_component_add_two
    (BitVec.ofNat 64 (base - listBase))
    (BitVec.ofNat 64 left.totalLength)
    (BitVec.ofNat 64 right.totalLength)
    listLength leafLength hinput hleaf
  simpa only [hleftExact, hrightExact] using hleafSpan

/-- A valid internal tree whose root is at ambient depth `depth` satisfies the
Munro--Wild per-leaf depth bound, provided the root label is at least
`depth + 1`.  Strictly increasing child labels preserve that premise down the
tree. -/
private theorem PowerValid.internal_leaf_depth_bound
    {listBase base : Nat} {listLength : PySSize}
    {tree : MergeTree} {depth : Nat}
    (hvalid : PowerValid listBase listLength base tree)
    (hinternal : tree.rootPower ≠ none)
    (hdepth : ∀ power, tree.rootPower = some power → depth + 1 ≤ power) :
    ∀ leaf ∈ tree.leavesWithDepth depth,
      (leaf.2 : Real) ≤
        Real.logb 2
          ((listLength.toNat : Real) / (leaf.1 : Real)) + 2 := by
  induction tree generalizing base depth with
  | leaf length => simp [rootPower] at hinternal
  | merge power left right ihLeft ihRight =>
      rcases hvalid with
        ⟨hbase, hwithin, hleftValid, hrightValid, hinput, hpower,
          hleftHeap, hrightHeap⟩
      have hrootDepth : depth + 1 ≤ power :=
        hdepth power (by simp [rootPower])
      intro leaf hleaf
      simp only [leavesWithDepth, List.mem_append] at hleaf
      rcases hleaf with hleaf | hleaf
      · by_cases hleftLeaf : left.rootPower = none
        · cases left with
          | leaf length =>
              simp only [leavesWithDepth, List.mem_singleton] at hleaf
              subst leaf
              have hlog := PowerValid.nodePower_lt_logb
                ⟨hbase, hwithin, hleftValid, hrightValid, hinput, hpower,
                  hleftHeap, hrightHeap⟩
                hleftValid.2.2
                (show length ≤ length + right.totalLength by omega)
              norm_num only [Prod.fst, Prod.snd]
              exact le_trans (by exact_mod_cast hrootDepth) hlog.le
          | merge childPower childLeft childRight =>
              simp [rootPower] at hleftLeaf
        · exact ihLeft (depth := depth + 1) hleftValid hleftLeaf
            (fun childPower hchildPower => by
              have hheap : power < childPower :=
                hleftHeap childPower hchildPower
              omega)
            leaf hleaf
      · by_cases hrightLeaf : right.rootPower = none
        · cases right with
          | leaf length =>
              simp only [leavesWithDepth, List.mem_singleton] at hleaf
              subst leaf
              have hlog := PowerValid.nodePower_lt_logb
                ⟨hbase, hwithin, hleftValid, hrightValid, hinput, hpower,
                  hleftHeap, hrightHeap⟩
                hrightValid.2.2
                (show length ≤ left.totalLength + length by omega)
              norm_num only [Prod.fst, Prod.snd]
              exact le_trans (by exact_mod_cast hrootDepth) hlog.le
          | merge childPower childLeft childRight =>
              simp [rootPower] at hrightLeaf
        · exact ihRight (depth := depth + 1) hrightValid hrightLeaf
            (fun childPower hchildPower => by
              have hheap : power < childPower :=
                hrightHeap childPower hchildPower
              omega)
            leaf hleaf

/-- Every leaf of a complete valid PowerSort tree satisfies the exact
per-leaf depth estimate used in the entropy summation.  The singleton case is
included explicitly: its only leaf has depth zero. -/
theorem PowerValid.leaf_depth_bound
    {listBase : Nat} {listLength : PySSize} {tree : MergeTree}
    (hvalid : tree.PowerValid listBase listLength listBase)
    (htotal : tree.totalLength = listLength.toNat) :
    ∀ leaf ∈ tree.leavesWithDepth 0,
      (leaf.2 : Real) ≤
        Real.logb 2
          ((listLength.toNat : Real) / (leaf.1 : Real)) + 2 := by
  cases tree with
  | leaf length =>
      intro leaf hleaf
      simp only [leavesWithDepth, List.mem_singleton] at hleaf
      subst leaf
      simp only [totalLength] at htotal
      have hlength : 0 < length := hvalid.2.2
      have hratio : ((listLength.toNat : Real) / (length : Real)) = 1 := by
        rw [← htotal]
        field_simp
      simp [hratio]
  | merge power left right =>
      have hrootPower : 1 ≤ power := by
        have hrange := powerRange
          (BitVec.ofNat 64 (listBase - listBase))
          (BitVec.ofNat 64 left.totalLength)
          (BitVec.ofNat 64 right.totalLength)
          listLength hvalid.2.2.2.2.1
        simpa only [hvalid.2.2.2.2.2.1] using hrange.1
      apply PowerValid.internal_leaf_depth_bound hvalid
      · simp [rootPower]
      · intro candidatePower hroot
        simp only [rootPower, Option.some.injEq] at hroot
        subst candidatePower
        exact hrootPower

end MergeTree

/-- Validity of a complete PowerSort merge plan.  Empty input is represented
by `MergePlan.empty`; a nonempty input is represented by one complete ordered
tree rooted at the input base. -/
def PowerMergePlanValid (listBase : Nat) (listLength : PySSize) :
    MergePlan → Prop
  | .empty => listLength.toNat = 0
  | .tree root =>
      root.PowerValid listBase listLength listBase ∧
        root.totalLength = listLength.toNat

/-- Exact empty-input case of complete-plan validity. -/
@[simp]
theorem powerMergePlanValid_empty_iff (listBase : Nat)
    (listLength : PySSize) :
    PowerMergePlanValid listBase listLength .empty ↔
      listLength.toNat = 0 := by
  rfl

/-- Exact singleton-input case: the sole positive run covers the whole input
and incurs no internal merge. -/
@[simp]
theorem powerMergePlanValid_singleton_iff (listBase length : Nat)
    (listLength : PySSize) :
    PowerMergePlanValid listBase listLength (.tree (.leaf length)) ↔
      length = listLength.toNat ∧ 0 < length := by
  simp only [PowerMergePlanValid, MergeTree.PowerValid,
    MergeTree.totalLength]
  constructor
  · rintro ⟨⟨_, _, hpositive⟩, hlength⟩
    exact ⟨hlength, hpositive⟩
  · rintro ⟨hlength, hpositive⟩
    subst length
    omega

/-- The run lengths of a valid power plan form a positive profile of the
complete input length. -/
def PowerMergePlanValid.runProfile
    {listBase : Nat} {listLength : PySSize} {plan : MergePlan}
    (hvalid : PowerMergePlanValid listBase listLength plan) :
    RunProfile listLength.toNat where
  lengths := plan.runLengths
  sum_eq := by
    cases plan with
    | empty => simpa [MergePlan.runLengths] using hvalid.symm
    | tree root =>
        simpa [MergePlan.runLengths, MergeTree.sum_runLengths] using hvalid.2
  positive := by
    cases plan with
    | empty => simp [MergePlan.runLengths]
    | tree root =>
        simpa [MergePlan.runLengths] using hvalid.1.leaf_positive

/-- Pure Munro--Wild merge-cost bound for a complete source-faithful
PowerSort tree.  The profile is extracted from the tree itself, so the theorem
also covers the empty and singleton plans without auxiliary premises. -/
theorem PowerMergePlanValid.mergeCost_le_entropy_add_two
    {listBase : Nat} {listLength : PySSize} {plan : MergePlan}
    (hvalid : PowerMergePlanValid listBase listLength plan) :
    (plan.mergeCost : Real) ≤
      (listLength.toNat : Real) * hvalid.runProfile.entropy +
        2 * (listLength.toNat : Real) := by
  apply plan.mergeCost_le_entropy_add_two hvalid.runProfile rfl
  cases plan with
  | empty => simp [MergePlan.leavesWithDepth]
  | tree root =>
      simpa [MergePlan.leavesWithDepth] using
        hvalid.1.leaf_depth_bound hvalid.2

/-- Profile-explicit form used by bridges that already expose the formed-run
profile as a named object. -/
theorem PowerMergePlanValid.mergeCost_le_entropy_add_two_of_profile
    {listBase : Nat} {listLength : PySSize} {plan : MergePlan}
    (hvalid : PowerMergePlanValid listBase listLength plan)
    (profile : RunProfile listLength.toNat)
    (hlengths : plan.runLengths = profile.lengths) :
    (plan.mergeCost : Real) ≤
      (listLength.toNat : Real) * profile.entropy +
        2 * (listLength.toNat : Real) := by
  apply plan.mergeCost_le_entropy_add_two profile hlengths
  cases plan with
  | empty => simp [MergePlan.leavesWithDepth]
  | tree root =>
      simpa [MergePlan.leavesWithDepth] using
        hvalid.1.leaf_depth_bound hvalid.2

/-- Source-order form of the same bound, `M ≤ H₂ · n + 2n`. -/
theorem PowerMergePlanValid.mergeCost_le_entropy_mul_add_two
    {listBase : Nat} {listLength : PySSize} {plan : MergePlan}
    (hvalid : PowerMergePlanValid listBase listLength plan) :
    (plan.mergeCost : Real) ≤
      hvalid.runProfile.entropy * (listLength.toNat : Real) +
        2 * (listLength.toNat : Real) := by
  simpa only [mul_comm] using hvalid.mergeCost_le_entropy_add_two

end CPythonListsort
