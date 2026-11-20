/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Assembly.MergePolicyReplay
import Code.Assembly.PowerTreeEntropy
import Code.Policy.BoundaryPowerGeometry

/-!
# PowerSort policy and cost bridge

This module contains the geometry used to turn the implementation's open
merge forest into the min-Cartesian PowerSort tree.  In particular, absorbing
the subtree on the deeper side of three consecutive spans leaves the
shallower boundary power unchanged.  The statements use the same `RunSpan`
and `replayBoundaryPower` objects as the executable policy replay, so no
paper-level midpoint oracle is introduced at the bridge.
-/

namespace CPythonListsort

namespace RunSpan

/-- A positive source span lying inside a declared input span. -/
def ValidWithin (span input : RunSpan) : Prop :=
  input.base ≤ span.base ∧
    span.endIndex ≤ input.endIndex ∧
    0 < span.len

/-- Merging adjacent valid spans preserves positivity and containment. -/
theorem merge_validWithin {input left right : RunSpan}
    (hleft : left.ValidWithin input) (hright : right.ValidWithin input)
    (hadjacent : left.Adjacent right) :
    (left.merge right).ValidWithin input := by
  rcases hleft with ⟨hleftBase, _hleftEnd, hleftPositive⟩
  rcases hright with ⟨_rightBase, hrightEnd, hrightPositive⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa [RunSpan.merge] using hleftBase
  · simp only [RunSpan.Adjacent, RunSpan.endIndex] at hadjacent
    simp only [RunSpan.endIndex, RunSpan.merge] at hrightEnd ⊢
    omega
  · simp only [RunSpan.merge]
    omega

end RunSpan

/-- For three consecutive positive spans, if the left boundary has smaller
power, absorbing the right two spans leaves that left boundary power exactly
unchanged.  This is the right-absorption clause of the finite-width
`boundaryPowerGeometry` theorem, restated on replay spans. -/
theorem replayBoundaryPower_absorb_right
    (input left middle right : RunSpan)
    (hinputMax : input.len ≤ PY_LIST_MAX)
    (hleft : left.ValidWithin input)
    (hmiddle : middle.ValidWithin input)
    (hright : right.ValidWithin input)
    (hleftMiddle : left.Adjacent middle)
    (hmiddleRight : middle.Adjacent right)
    (hpower : replayBoundaryPower input left middle <
      replayBoundaryPower input middle right) :
    replayBoundaryPower input left (middle.merge right) =
      replayBoundaryPower input left middle := by
  let s := left.base - input.base
  have hleftBase : input.base ≤ left.base := hleft.1
  have hmiddleBase : middle.base - input.base = s + left.len := by
    dsimp [s]
    unfold RunSpan.Adjacent RunSpan.endIndex at hleftMiddle
    omega
  have hfits : s + left.len + middle.len + right.len ≤ input.len := by
    dsimp [s]
    unfold RunSpan.ValidWithin RunSpan.endIndex at hright
    unfold RunSpan.Adjacent RunSpan.endIndex at hleftMiddle hmiddleRight
    omega
  have hgeometry := boundaryPowerGeometry s left.len middle.len right.len
    input.len hleft.2.2 hmiddle.2.2 hright.2.2 hfits hinputMax
  dsimp only at hgeometry
  have hpower' :
      powerloop (BitVec.ofNat 64 s) (BitVec.ofNat 64 left.len)
          (BitVec.ofNat 64 middle.len) (BitVec.ofNat 64 input.len) <
        powerloop (BitVec.ofNat 64 (s + left.len))
          (BitVec.ofNat 64 middle.len) (BitVec.ofNat 64 right.len)
          (BitVec.ofNat 64 input.len) := by
    simpa [replayBoundaryPower, s, hmiddleBase] using hpower
  have habsorb := hgeometry.2.1 hpower'
  simpa [replayBoundaryPower, RunSpan.merge, s] using habsorb

/-- Symmetrically, if the right boundary has smaller power, absorbing the
left two spans leaves the right boundary power exactly unchanged. -/
theorem replayBoundaryPower_absorb_left
    (input left middle right : RunSpan)
    (hinputMax : input.len ≤ PY_LIST_MAX)
    (hleft : left.ValidWithin input)
    (hmiddle : middle.ValidWithin input)
    (hright : right.ValidWithin input)
    (hleftMiddle : left.Adjacent middle)
    (hmiddleRight : middle.Adjacent right)
    (hpower : replayBoundaryPower input middle right <
      replayBoundaryPower input left middle) :
    replayBoundaryPower input (left.merge middle) right =
      replayBoundaryPower input middle right := by
  let s := left.base - input.base
  have hleftBase : input.base ≤ left.base := hleft.1
  have hmiddleBase : middle.base - input.base = s + left.len := by
    dsimp [s]
    unfold RunSpan.Adjacent RunSpan.endIndex at hleftMiddle
    omega
  have hfits : s + left.len + middle.len + right.len ≤ input.len := by
    dsimp [s]
    unfold RunSpan.ValidWithin RunSpan.endIndex at hright
    unfold RunSpan.Adjacent RunSpan.endIndex at hleftMiddle hmiddleRight
    omega
  have hgeometry := boundaryPowerGeometry s left.len middle.len right.len
    input.len hleft.2.2 hmiddle.2.2 hright.2.2 hfits hinputMax
  dsimp only at hgeometry
  have hpower' :
      powerloop (BitVec.ofNat 64 (s + left.len))
          (BitVec.ofNat 64 middle.len) (BitVec.ofNat 64 right.len)
          (BitVec.ofNat 64 input.len) <
        powerloop (BitVec.ofNat 64 s) (BitVec.ofNat 64 left.len)
          (BitVec.ofNat 64 middle.len) (BitVec.ofNat 64 input.len) := by
    simpa [replayBoundaryPower, s, hmiddleBase] using hpower
  have habsorb := hgeometry.2.2 hpower'
  have hmergedBase : (left.merge middle).base - input.base = s := by
    simp [RunSpan.merge, s]
  simpa [replayBoundaryPower, RunSpan.merge, s, hmiddleBase,
    hmergedBase] using habsorb

/-! ## Certified open forests and canonical final completion -/

/-- The span lengths of the roots currently open on the pending stack. -/
def openForestLengths (forest : List SpannedMergeTree) : List Nat :=
  forest.map fun entry => entry.span.len

/-- A forest tiles the suffix from `start` to the end of `input` with positive,
in-bounds spans.  The recursive endpoint is also the next root's base, so this
single relation exposes start, adjacency, containment, and exact suffix
coverage without hiding any of them behind list arithmetic. -/
inductive OpenSpanChain (input : RunSpan) :
    Nat → List SpannedMergeTree → Prop
  | empty {start : Nat} (end_eq : start = input.endIndex) :
      OpenSpanChain input start []
  | cons {start : Nat} (entry : SpannedMergeTree)
      (rest : List SpannedMergeTree)
      (base_eq : entry.span.base = start)
      (valid : entry.span.ValidWithin input)
      (tail : OpenSpanChain input entry.span.endIndex rest) :
      OpenSpanChain input start (entry :: rest)

/-- Exact boundary powers together with the local heap edge from every open
root except the newest one.  The terminal open root is explicitly a leaf,
matching the scan loop's merge-before-push order. -/
inductive OpenBoundaryCertificate (input : RunSpan) :
    List SpannedMergeTree → List Nat → Prop
  | empty : OpenBoundaryCertificate input [] []
  | singleton (entry : SpannedMergeTree) (length : Nat)
      (isLeaf : entry.tree = .leaf length) :
      OpenBoundaryCertificate input [entry] []
  | cons (left right : SpannedMergeTree)
      (rest : List SpannedMergeTree) (power : Nat) (powers : List Nat)
      (power_eq : power = replayBoundaryPower input left.span right.span)
      (below_left_root : ∀ rootPower,
        left.tree.rootPower = some rootPower → power < rootPower)
      (tail : OpenBoundaryCertificate input (right :: rest) powers) :
      OpenBoundaryCertificate input (left :: right :: rest) (power :: powers)

/-- A reviewable certificate for a scan-produced open PowerSort forest.

`powers` is not inferred from a tree built after the fact: `boundaries`
aligns it with every adjacent pair of open roots and records the exact
transcribed boundary power.  `strict` is the pending-stack heap order, while
`below_left_root` inside `OpenBoundaryCertificate` records the remaining
heap edges into already-built subtrees. -/
structure PowerOpenForestCertificate (input : RunSpan) (start : Nat)
    (forest : List SpannedMergeTree) (powers : List Nat) : Prop where
  inputMax : input.len ≤ PY_LIST_MAX
  spans : OpenSpanChain input start forest
  treeValid : ∀ entry ∈ forest,
    entry.Valid ∧
      entry.tree.PowerValid input.base (BitVec.ofNat 64 input.len)
        entry.span.base
  boundaries : OpenBoundaryCertificate input forest powers
  strict : powers.Pairwise (fun earlier later => earlier < later)

/-- The top-level scan certificate starts at the input base. -/
def PowerOpenForestValid (input : RunSpan)
    (forest : List SpannedMergeTree) : Prop :=
  ∃ powers, PowerOpenForestCertificate input input.base forest powers

/-- Right-associated tree obtained by repeatedly merging the top pair of a
nonempty open forest.  Its node label is recomputed from the full aggregate
child spans, rather than copied from certificate metadata. -/
def canonicalTopPairRoot (input : RunSpan) :
    SpannedMergeTree → List SpannedMergeTree → SpannedMergeTree
  | current, [] => current
  | current, next :: rest =>
      let right := canonicalTopPairRoot input next rest
      SpannedMergeTree.merge
        (replayBoundaryPower input current.span right.span) current right

/-- Empty-or-tree normalization of canonical repeated-top-pair completion. -/
def canonicalTopPairCompletion (input : RunSpan) :
    List SpannedMergeTree → MergePlan
  | [] => .empty
  | first :: rest => .tree (canonicalTopPairRoot input first rest).tree

@[simp]
theorem canonicalTopPairCompletion_empty (input : RunSpan) :
    canonicalTopPairCompletion input [] = .empty := rfl

@[simp]
theorem canonicalTopPairCompletion_singleton
    (input : RunSpan) (entry : SpannedMergeTree) :
    canonicalTopPairCompletion input [entry] = .tree entry.tree := rfl

/-- Completion preserves the first root's base. -/
@[simp]
theorem canonicalTopPairRoot_base (input : RunSpan)
    (first : SpannedMergeTree) (rest : List SpannedMergeTree) :
    (canonicalTopPairRoot input first rest).span.base = first.span.base := by
  induction rest generalizing first with
  | nil => rfl
  | cons next rest ih =>
      simp [canonicalTopPairRoot, SpannedMergeTree.merge, RunSpan.merge]

/-- The completed root length is the sum of all open-root span lengths. -/
theorem canonicalTopPairRoot_span_len (input : RunSpan)
    (first : SpannedMergeTree) (rest : List SpannedMergeTree) :
    (canonicalTopPairRoot input first rest).span.len =
      (openForestLengths (first :: rest)).sum := by
  induction rest generalizing first with
  | nil => simp [canonicalTopPairRoot, openForestLengths]
  | cons next rest ih =>
      simp only [canonicalTopPairRoot, SpannedMergeTree.merge, RunSpan.merge,
        openForestLengths, List.map_cons, List.sum_cons]
      rw [ih]
      simp [openForestLengths]

/-- Canonical completion preserves every already-built subtree's leaves in
their exact left-to-right source order. -/
theorem canonicalTopPairRoot_runLengths (input : RunSpan)
    (first : SpannedMergeTree) (rest : List SpannedMergeTree) :
    (canonicalTopPairRoot input first rest).tree.runLengths =
      forestRunLengths (first :: rest) := by
  induction rest generalizing first with
  | nil => simp [canonicalTopPairRoot, forestRunLengths]
  | cons next rest ih =>
      simp only [canonicalTopPairRoot, SpannedMergeTree.merge,
        MergeTree.runLengths, forestRunLengths_cons]
      rw [ih]
      rfl

/-- Plan-level form of canonical leaf-order preservation, including the empty
open forest. -/
theorem canonicalTopPairCompletion_runLengths (input : RunSpan)
    (forest : List SpannedMergeTree) :
    (canonicalTopPairCompletion input forest).runLengths =
      forestRunLengths forest := by
  cases forest with
  | nil => rfl
  | cons first rest =>
      exact canonicalTopPairRoot_runLengths input first rest

/-- Valid spanned roots remain valid under canonical top-pair completion. -/
theorem canonicalTopPairRoot_valid (input : RunSpan)
    (first : SpannedMergeTree) (rest : List SpannedMergeTree)
    (hvalid : ∀ entry ∈ first :: rest, entry.Valid) :
    (canonicalTopPairRoot input first rest).Valid := by
  induction rest generalizing first with
  | nil => exact hvalid first (by simp)
  | cons next rest ih =>
      simp only [canonicalTopPairRoot]
      apply SpannedMergeTree.merge_valid
      · exact hvalid first (by simp)
      · apply ih
        intro entry hentry
        exact hvalid entry (by simp [hentry])

/-- Canonical completion has exactly the forest's already-incurred internal
cost plus Algorithm 2's repeated-top-pair completion cost. -/
theorem canonicalTopPairRoot_mergeCost
    (input : RunSpan) (first : SpannedMergeTree)
    (rest : List SpannedMergeTree)
    (hvalid : ∀ entry ∈ first :: rest, entry.Valid) :
    (canonicalTopPairRoot input first rest).tree.mergeCost =
      forestMergeCost (first :: rest) +
        topPairCompletionCost (openForestLengths (first :: rest)) := by
  induction rest generalizing first with
  | nil => simp [canonicalTopPairRoot, openForestLengths,
      forestMergeCost, topPairCompletionCost]
  | cons next rest ih =>
      have hfirst := hvalid first (by simp)
      have htail : ∀ entry ∈ next :: rest, entry.Valid := by
        intro entry hentry
        exact hvalid entry (by simp [hentry])
      have hrightValid := canonicalTopPairRoot_valid input next rest htail
      have hrightLength := canonicalTopPairRoot_span_len input next rest
      simp only [canonicalTopPairRoot, SpannedMergeTree.merge,
        MergeTree.mergeCost, forestMergeCost,
        openForestLengths, List.map_cons, List.sum_cons]
      rw [ih next htail]
      simp only [SpannedMergeTree.Valid] at hfirst hrightValid
      rw [hfirst, hrightValid, hrightLength]
      cases rest with
      | nil =>
          simp [openForestLengths, forestMergeCost, topPairCompletionCost]
          omega
      | cons third tail =>
          simp [openForestLengths, forestMergeCost, topPairCompletionCost]
          omega

/-- Plan-level exact cost identity for canonical top-pair completion. -/
theorem canonicalTopPairCompletion_mergeCost
    (input : RunSpan) (forest : List SpannedMergeTree)
    (hvalid : ∀ entry ∈ forest, entry.Valid) :
    (canonicalTopPairCompletion input forest).mergeCost =
      forestMergeCost forest +
        topPairCompletionCost (openForestLengths forest) := by
  cases forest with
  | nil => rfl
  | cons first rest =>
      exact canonicalTopPairRoot_mergeCost input first rest hvalid

/-! ## From the open certificate to a valid PowerSort plan -/

/-- Completion of a certified suffix retains its exact source interval and
the expected global `PowerValid` judgment.  The final field identifies the
root label with the first open-boundary power, or with `none` for the terminal
leaf. -/
structure CanonicalTopPairRootPost (input : RunSpan) (start : Nat)
    (powers : List Nat) (root : SpannedMergeTree) : Prop where
  base_eq : root.span.base = start
  end_eq : root.span.endIndex = input.endIndex
  spanValid : root.span.ValidWithin input
  spannedValid : root.Valid
  powerValid : root.tree.PowerValid input.base
    (BitVec.ofNat 64 input.len) start
  rootPower_eq : root.tree.rootPower = powers.head?

/-- Pure span aggregation for a suffix chain. -/
theorem canonicalTopPairRoot_span_of_chain
    {input : RunSpan} {start : Nat}
    {first : SpannedMergeTree} {rest : List SpannedMergeTree}
    (hchain : OpenSpanChain input start (first :: rest)) :
    let root := canonicalTopPairRoot input first rest
    root.span.base = start ∧
      root.span.endIndex = input.endIndex ∧
      root.span.ValidWithin input := by
  induction rest generalizing start first with
  | nil =>
      cases hchain with
      | cons entry rest hbase hvalid htail =>
          cases htail with
          | empty hend =>
              exact ⟨hbase, hend, hvalid⟩
  | cons next rest ih =>
      cases hchain with
      | cons entry tail hbase hvalid htail =>
          have hright := ih htail
          dsimp only at hright ⊢
          have hadjacent : first.span.Adjacent
              (canonicalTopPairRoot input next rest).span := by
            unfold RunSpan.Adjacent
            rw [hright.1]
          have hend :
              (SpannedMergeTree.merge
                (replayBoundaryPower input first.span
                  (canonicalTopPairRoot input next rest).span)
                first (canonicalTopPairRoot input next rest)).span.endIndex =
                input.endIndex := by
            calc
              _ = first.span.endIndex +
                    (canonicalTopPairRoot input next rest).span.len := by
                  simp [SpannedMergeTree.merge, RunSpan.merge,
                    RunSpan.endIndex, Nat.add_assoc]
              _ = (canonicalTopPairRoot input next rest).span.base +
                    (canonicalTopPairRoot input next rest).span.len := by
                  rw [hadjacent]
              _ = (canonicalTopPairRoot input next rest).span.endIndex := rfl
              _ = input.endIndex := hright.2.1
          refine ⟨?_, ?_, ?_⟩
          · simpa [canonicalTopPairRoot, SpannedMergeTree.merge,
              RunSpan.merge] using hbase
          · simpa [canonicalTopPairRoot] using hend
          · apply RunSpan.merge_validWithin hvalid hright.2.2 hadjacent

private theorem inputWord_toNat_of_max {input : RunSpan}
    (hmax : input.len ≤ PY_LIST_MAX) :
    (BitVec.ofNat 64 input.len).toNat = input.len := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  rw [pyListMax_eq] at hmax
  norm_num at hmax ⊢
  omega

/-- Adjacent positive in-bounds aggregate spans supply the exact finite-width
domain required at a newly created completion node. -/
theorem replayBoundaryPower_valid_input
    (input left right : RunSpan)
    (hinputMax : input.len ≤ PY_LIST_MAX)
    (hleft : left.ValidWithin input)
    (hright : right.ValidWithin input)
    (hadjacent : left.Adjacent right) :
    ValidPowerloopInput
      (BitVec.ofNat 64 (left.base - input.base))
      (BitVec.ofNat 64 left.len)
      (BitVec.ofNat 64 right.len)
      (BitVec.ofNat 64 input.len) := by
  apply validPowerloopInput_ofNat hleft.2.2 hright.2.2
  · unfold RunSpan.ValidWithin RunSpan.endIndex at hleft hright
    unfold RunSpan.Adjacent RunSpan.endIndex at hadjacent
    omega
  · exact hinputMax

private theorem canonicalTopPairRoot_of_open_certificate
    {input : RunSpan} {start : Nat}
    {first : SpannedMergeTree} {rest : List SpannedMergeTree}
    {powers : List Nat}
    (hinputMax : input.len ≤ PY_LIST_MAX)
    (hspans : OpenSpanChain input start (first :: rest))
    (htrees : ∀ entry ∈ first :: rest,
      entry.Valid ∧
        entry.tree.PowerValid input.base (BitVec.ofNat 64 input.len)
          entry.span.base)
    (hboundaries : OpenBoundaryCertificate input (first :: rest) powers)
    (hstrict : powers.Pairwise (fun earlier later => earlier < later)) :
    CanonicalTopPairRootPost input start powers
      (canonicalTopPairRoot input first rest) := by
  induction rest generalizing start first powers with
  | nil =>
      cases hboundaries with
      | singleton entry length isLeaf =>
          cases hspans with
          | cons entry rest hbase hspan htail =>
              cases htail with
              | empty hend =>
                  have htree := htrees first (by simp)
                  refine
                    { base_eq := hbase
                      end_eq := hend
                      spanValid := hspan
                      spannedValid := htree.1
                      powerValid := by
                        simpa [canonicalTopPairRoot, hbase] using htree.2
                      rootPower_eq := by
                        simp [canonicalTopPairRoot, isLeaf,
                          MergeTree.rootPower] }
  | cons right rest ih =>
      cases hboundaries with
      | cons left right rest power powers hpower hbelow htail =>
          cases hspans with
          | cons entry tail hleftBase hleftSpan hspanTail =>
              have hleftTree := htrees first (by simp)
              have htailTrees : ∀ entry ∈ right :: rest,
                  entry.Valid ∧
                    entry.tree.PowerValid input.base (BitVec.ofNat 64 input.len)
                      entry.span.base := by
                intro entry hentry
                exact htrees entry (by simp [hentry])
              simp only [List.pairwise_cons] at hstrict
              have hrightPost := ih hspanTail htailTrees htail hstrict.2
              have hleftRight : first.span.Adjacent right.span := by
                cases hspanTail with
                | cons right rest hrightBase hrightSpan hrest =>
                    unfold RunSpan.Adjacent
                    exact hrightBase.symm
              let rightRoot := canonicalTopPairRoot input right rest
              have haggregatePower :
                  replayBoundaryPower input first.span rightRoot.span = power := by
                cases rest with
                | nil =>
                    cases htail with
                    | singleton right length isLeaf =>
                        simpa [rightRoot, canonicalTopPairRoot] using hpower.symm
                | cons next tail =>
                    cases htail with
                    | cons middle next tail nextPower tailPowers
                        hnextPower hnextBelow hnextTail =>
                        cases hspanTail with
                        | cons right rest hrightBase hrightSpan hrestChain =>
                            have hrestPost :=
                              canonicalTopPairRoot_span_of_chain hrestChain
                            dsimp only at hrestPost
                            let restRoot := canonicalTopPairRoot input next tail
                            have hrightRest :
                                right.span.Adjacent restRoot.span := by
                              unfold RunSpan.Adjacent
                              simpa [restRoot] using hrestPost.1.symm
                            have hnextAggregate :
                                replayBoundaryPower input right.span restRoot.span =
                                  nextPower := by
                              have hrootPower := hrightPost.rootPower_eq
                              simpa [rightRoot, restRoot, canonicalTopPairRoot,
                                SpannedMergeTree.merge, MergeTree.rootPower] using
                                  hrootPower
                            have hpowerLt : power < nextPower :=
                              hstrict.1 nextPower (by simp)
                            have habsorb := replayBoundaryPower_absorb_right
                              input first.span right.span restRoot.span hinputMax
                              hleftSpan hrightSpan hrestPost.2.2 hleftRight
                              hrightRest
                              (by simpa [hpower, hnextAggregate] using hpowerLt)
                            simpa [rightRoot, restRoot, canonicalTopPairRoot,
                              SpannedMergeTree.merge, RunSpan.merge, hpower] using
                                habsorb
              have hleftAggregate : first.span.Adjacent rightRoot.span := by
                exact hrightPost.base_eq.symm
              have hnewPowerValid :
                  (SpannedMergeTree.merge
                    (replayBoundaryPower input first.span rightRoot.span)
                    first rightRoot).tree.PowerValid input.base
                      (BitVec.ofNat 64 input.len) start := by
                simp only [SpannedMergeTree.merge, MergeTree.PowerValid]
                have hword := inputWord_toNat_of_max hinputMax
                have hleftLen : first.tree.totalLength = first.span.len :=
                  hleftTree.1
                have hrightLen : rightRoot.tree.totalLength =
                    rightRoot.span.len := hrightPost.spannedValid
                refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                · simpa [hleftBase] using hleftSpan.1
                · rw [hword]
                  have hend : rightRoot.span.endIndex = input.endIndex := by
                    simpa [rightRoot] using hrightPost.end_eq
                  unfold RunSpan.Adjacent RunSpan.endIndex at hleftAggregate
                  unfold RunSpan.ValidWithin RunSpan.endIndex at hleftSpan
                  unfold RunSpan.endIndex at hend
                  rw [hleftLen, hrightLen]
                  omega
                · simpa [hleftBase] using hleftTree.2
                · have hstartRight :
                      start + first.tree.totalLength =
                        first.span.endIndex := by
                    unfold RunSpan.endIndex
                    rw [hleftLen]
                    omega
                  rw [hstartRight]
                  simpa [rightRoot] using hrightPost.powerValid
                · simpa [hleftBase, hleftLen, hrightLen] using
                    replayBoundaryPower_valid_input input first.span
                      rightRoot.span hinputMax hleftSpan
                      hrightPost.spanValid hleftAggregate
                · simp [replayBoundaryPower, hleftBase, hleftLen, hrightLen]
                · intro childPower hchild
                  rw [haggregatePower]
                  exact hbelow childPower hchild
                · intro childPower hchild
                  rw [haggregatePower]
                  cases hpowers : powers with
                  | nil =>
                      have : rightRoot.tree.rootPower = none := by
                        simpa [hpowers] using hrightPost.rootPower_eq
                      rw [this] at hchild
                      contradiction
                  | cons nextPower tailPowers =>
                      have hroot : rightRoot.tree.rootPower = some nextPower := by
                        simpa [hpowers] using hrightPost.rootPower_eq
                      rw [hroot] at hchild
                      cases hchild
                      exact hstrict.1 childPower (by simp [hpowers])
              have hspanPost := canonicalTopPairRoot_span_of_chain
                (OpenSpanChain.cons first (right :: rest) hleftBase hleftSpan
                  hspanTail)
              dsimp only at hspanPost
              refine
                { base_eq := hspanPost.1
                  end_eq := hspanPost.2.1
                  spanValid := hspanPost.2.2
                  spannedValid := canonicalTopPairRoot_valid input first
                    (right :: rest)
                    (fun entry hentry => (htrees entry hentry).1)
                  powerValid := ?_
                  rootPower_eq := ?_ }
              · simpa [rightRoot, canonicalTopPairRoot] using hnewPowerValid
              · simp [rightRoot, canonicalTopPairRoot, SpannedMergeTree.merge,
                  MergeTree.rootPower, haggregatePower]

/-- Canonical repeated-top-pair completion of a certified scan forest is a
complete source-faithful min-Cartesian PowerSort plan. -/
theorem PowerOpenForestCertificate.canonicalCompletion_valid
    {input : RunSpan} {forest : List SpannedMergeTree}
    {powers : List Nat}
    (certificate :
      PowerOpenForestCertificate input input.base forest powers) :
    PowerMergePlanValid input.base (BitVec.ofNat 64 input.len)
      (canonicalTopPairCompletion input forest) := by
  cases forest with
  | nil =>
      cases certificate.spans with
      | empty hend =>
          simp only [canonicalTopPairCompletion, PowerMergePlanValid]
          have hword := inputWord_toNat_of_max certificate.inputMax
          rw [hword]
          unfold RunSpan.endIndex at hend
          omega
  | cons first rest =>
      have hpost := canonicalTopPairRoot_of_open_certificate
        certificate.inputMax certificate.spans certificate.treeValid
        certificate.boundaries certificate.strict
      simp only [canonicalTopPairCompletion, PowerMergePlanValid]
      refine ⟨?_, ?_⟩
      · simpa [hpost.base_eq] using hpost.powerValid
      · have hword := inputWord_toNat_of_max certificate.inputMax
        rw [hword]
        have hvalid := hpost.spannedValid
        simp only [SpannedMergeTree.Valid] at hvalid
        have hbase := hpost.base_eq
        have hend := hpost.end_eq
        unfold RunSpan.endIndex at hend
        rw [hvalid]
        omega

/-- Existential top-level wrapper for the named open-forest predicate. -/
theorem PowerOpenForestValid.canonicalCompletion_valid
    {input : RunSpan} {forest : List SpannedMergeTree}
    (hvalid : PowerOpenForestValid input forest) :
    PowerMergePlanValid input.base (BitVec.ofNat 64 input.len)
      (canonicalTopPairCompletion input forest) := by
  rcases hvalid with ⟨powers, certificate⟩
  exact certificate.canonicalCompletion_valid

/-- Exact cost decomposition specialized to a certified scan forest. -/
theorem PowerOpenForestCertificate.canonicalCompletion_cost
    {input : RunSpan} {forest : List SpannedMergeTree}
    {powers : List Nat}
    (certificate :
      PowerOpenForestCertificate input input.base forest powers) :
    (canonicalTopPairCompletion input forest).mergeCost =
      forestMergeCost forest +
        topPairCompletionCost (openForestLengths forest) :=
  canonicalTopPairCompletion_mergeCost input forest
    (fun entry hentry => (certificate.treeValid entry hentry).1)

/-- The two facts consumed by the paper-facing cost theorem: canonical
completion is a valid power-labelled plan and its cost splits exactly into
the already-incurred forest cost plus repeated-top-pair completion cost. -/
theorem PowerOpenForestCertificate.canonicalCompletion_spec
    {input : RunSpan} {forest : List SpannedMergeTree}
    {powers : List Nat}
    (certificate :
      PowerOpenForestCertificate input input.base forest powers) :
    PowerMergePlanValid input.base (BitVec.ofNat 64 input.len)
        (canonicalTopPairCompletion input forest) ∧
      (canonicalTopPairCompletion input forest).mergeCost =
        forestMergeCost forest +
          topPairCompletionCost (openForestLengths forest) :=
  ⟨certificate.canonicalCompletion_valid,
    certificate.canonicalCompletion_cost⟩

/-- Existential wrapper for the certified canonical cost identity. -/
theorem PowerOpenForestValid.canonicalCompletion_cost
    {input : RunSpan} {forest : List SpannedMergeTree}
    (hvalid : PowerOpenForestValid input forest) :
    (canonicalTopPairCompletion input forest).mergeCost =
      forestMergeCost forest +
        topPairCompletionCost (openForestLengths forest) := by
  rcases hvalid with ⟨powers, certificate⟩
  exact certificate.canonicalCompletion_cost

/-- Existential scan-facing wrapper for canonical validity and exact cost. -/
theorem PowerOpenForestValid.canonicalCompletion_spec
    {input : RunSpan} {forest : List SpannedMergeTree}
    (hvalid : PowerOpenForestValid input forest) :
    PowerMergePlanValid input.base (BitVec.ofNat 64 input.len)
        (canonicalTopPairCompletion input forest) ∧
      (canonicalTopPairCompletion input forest).mergeCost =
        forestMergeCost forest +
          topPairCompletionCost (openForestLengths forest) := by
  rcases hvalid with ⟨powers, certificate⟩
  exact certificate.canonicalCompletion_spec

/-- CPython's source-faithful final-collapse cost is bounded by the canonical
valid PowerSort completion on the same certified open forest. -/
theorem PowerOpenForestCertificate.cpythonForceCollapseCost_le_canonical
    {input : RunSpan} {forest : List SpannedMergeTree}
    {powers : List Nat} {collapseCost : Nat}
    (certificate :
      PowerOpenForestCertificate input input.base forest powers)
    (hcollapse :
      CPythonForceCollapseCost (openForestLengths forest) collapseCost) :
    forestMergeCost forest + collapseCost ≤
      (canonicalTopPairCompletion input forest).mergeCost := by
  rw [canonicalTopPairCompletion_mergeCost input forest
    (fun entry hentry => (certificate.treeValid entry hentry).1)]
  exact Nat.add_le_add_left hcollapse.le_topPairCompletionCost _

/-- Existential wrapper for CPython final-collapse cost dominance.  This
relates the implementation's collapse schedule to, but does not identify it
with, the canonical paper completion. -/
theorem PowerOpenForestValid.cpythonForceCollapseCost_le_canonical
    {input : RunSpan} {forest : List SpannedMergeTree}
    {collapseCost : Nat}
    (hvalid : PowerOpenForestValid input forest)
    (hcollapse :
      CPythonForceCollapseCost (openForestLengths forest) collapseCost) :
    forestMergeCost forest + collapseCost ≤
      (canonicalTopPairCompletion input forest).mergeCost := by
  rcases hvalid with ⟨powers, certificate⟩
  exact certificate.cpythonForceCollapseCost_le_canonical hcollapse

end CPythonListsort
