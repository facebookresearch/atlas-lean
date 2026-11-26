/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.KdTree
public import Cslib.Algorithms.Lean.MergeSort.MergeSort

/-!
# Planar range reporting with two presorted orders

P. K. Agarwal, *Orthogonal Range Searching*, CPS234 Lecture 8 (Duke, 22 September
2005), §§8.3.1–8.3.3, stores the median at its node and removes it from both children.
Here the median starts the right half and remains at a leaf: an internal node stores
only its separator. Unlike `KdTree.build`, this builder never sorts at a recursive split.

Coordinates need only a linear order. Rank `i` is encoded by `2*i`; the separator just
before rank `j` is `2*j-1`. For points with distinct coordinates on each axis, the two
point sets in the original order are `< median` and `≥ median`. Four binary searches
translate a closed query to *even* rank endpoints. Thus the weak split tests of
`KdTree.reportAux` take only the right child for a line query at the median. That reporter
uses split tests, not rectangle classifications: it visits all nodes of a contained
subtree and continues reporting after a hit.

Work is in the unit-cost comparison model: coordinate comparisons, pointers and operations
on word-sized ranks cost constant time. The preprocessing meter charges actual key comparisons,
cell passes and recursive calls. Query work counts probes, visited constructors and output
lookups. These are not bit-complexity or Lean runtime measurements.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.KdTree

/-- **Stored constructors of a kd-tree.** Count one for each split, leaf or empty tree,
including the root of an empty tree. -/
def storedNodes {d : Nat} : KdTree d → Nat
  | .empty | .leaf _ => 1
  | .node _ _ l r => 1 + l.storedNodes + r.storedNodes

/-- **Visited constructors of a kd-tree range report.** Count the root and precisely those
recursive calls made by the split-coordinate tests of the accumulator report. A contained
subtree costs one visit for every one of its constructors, not a single visit. -/
def reportVisits {d : Nat} (lo hi : Fin d → Int) : KdTree d → Nat
  | .empty | .leaf _ => 1
  | .node a s l r => 1 + (if s < lo a then 0 else reportVisits lo hi l) +
      (if hi a < s then 0 else reportVisits lo hi r)

/-- **A range report visits at most the whole kd-tree.** For any tree and corners, even
without a split invariant or ordered endpoints, visits are bounded by stored constructors. -/
theorem reportVisits_le_storedNodes {d : Nat} (lo hi : Fin d → Int) (t : KdTree d) :
    reportVisits lo hi t ≤ t.storedNodes := by
  induction t with
  | empty | leaf => exact Nat.le_refl 1
  | node a s l r hl hr =>
    simp only [reportVisits, storedNodes]
    split <;> split <;> omega

namespace Planar

/-- **Median shape of a planar leaf kd-tree.** The empty and singleton cases are an empty tree
and a leaf. For $n\ge 2$ the current split has $\lfloor n/2\rfloor$ leaves on the left and
the other leaves on the right. Both children use the next axis. -/
inductive MedianShape : Fin 2 → Nat → KdTree 2 → Prop where
  | empty (a) : MedianShape a 0 .empty
  | leaf (a p) : MedianShape a 1 (.leaf p)
  | node {a n s l r} (hn : 2 ≤ n)
      (hl : MedianShape (nextAxis a) (n / 2) l)
      (hr : MedianShape (nextAxis a) (n - n / 2) r) : MedianShape a n (.node a s l r)

/-- **Exact storage of a median-shaped leaf kd-tree.** With $n>0$ points there are $2n-1$
constructors: $n$ leaves and $n-1$ splits. The empty tree has one empty constructor. -/
theorem MedianShape.storedNodes_eq {a n t} (h : MedianShape a n t) :
    t.storedNodes = if n = 0 then 1 else 2 * n - 1 := by
  induction h with
  | empty | leaf => rfl
  | node hn _ _ ihl ihr =>
    simp only [storedNodes, ihl, ihr]
    split <;> split <;> split <;> omega

/-- **Kd-tree construction from two presorted rank lists.** Given the same $n$ even rank
points sorted on the current and opposite axes, split the first list at $\lfloor n/2\rfloor$.
The separator is one less than the first right coordinate. Stably partition the other order
at this separator, then swap the roles of the two lists in each recursive call. Charge one per
call and, at each split, the requested prefix size $\lfloor n/2\rfloor$ plus one per partition
test. For well-formed orders the requested size is the actual prefix length; a shorter first
list still incurs the full requested charge. The size parameter determines the recursion; on
malformed orders an absent singleton gives an empty tree and an absent right head uses the
default coordinate zero. -/
def fromOrders (a : Fin 2) (n : Nat) (xs ys : List (Fin 2 → Int)) : KdTree 2 × Nat :=
  match n with
  | 0 => (.empty, 1)
  | 1 => (match xs with | [] => .empty | p :: _ => .leaf p, 1)
  | m + 2 =>
    let k := (m + 2) / 2
    let (low, high) := xs.splitAt k
    let cut := headCoord a high - 1
    let (yl, yr) := ys.partition (fun p => p a ≤ cut)
    let (l, wl) := fromOrders (nextAxis a) k yl low
    let (r, wr) := fromOrders (nextAxis a) (m + 2 - k) yr high
    (.node a cut l r, 1 + k + ys.length + wl + wr)
termination_by n
decreasing_by all_goals omega

/-- **Rank index for planar range reporting.** The kd-tree stores pairs of even coordinate
ranks. An array of original points in x order decodes the leaves; an array of y coordinates
in y order supplies the second dictionary for translating query endpoints. -/
structure Index (α : Type*) where
  tree : KdTree 2
  byX : Array (α × α)
  byY : Array α

/-- **Preprocessing a planar range index.** Sort by x, attach x ranks, sort the tagged points
by y, then attach y ranks. Scatter the rank pairs into their x order by indexed writes to a
fresh array. Build the tree from the two orders. In addition to tree construction, charge the
key comparisons in both merge sorts, the number of records at their nontrivial splits, ten
linear passes and one setup unit. No sort occurs below the root of the kd-tree. -/
def preprocess {α : Type} [LinearOrder α] (pts : List (α × α)) : Index α × Nat :=
  let sx := pts.mergeSortM (fun p q => (⟨decide (p.1 ≤ q.1), 1⟩ : TimeM Nat Bool))
  let sy := sx.ret.zipIdx.mergeSortM (fun p q => (⟨decide (p.1.2 ≤ q.1.2), 1⟩ : TimeM Nat Bool))
  let n := sx.ret.length
  let ranks : List (Fin 2 → Int) := sy.ret.zipIdx.map fun (p, j) a =>
    if a = 0 then 2 * (p.2 : Int) else 2 * (j : Int)
  let xRanks := ranks.foldl (fun arr p => arr.setIfInBounds ((p 0).toNat / 2) p)
    (Array.replicate n (fun _ => 0))
  let (t, wt) := fromOrders 0 n xRanks.toList ranks
  -- Two enumerations, length, rank map, replicate, scatter, array-to-list,
  -- x dictionary, y projection and y dictionary. The scatter array is used linearly.
  (⟨t, sx.ret.toArray, (sy.ret.map (fun p => p.1.2)).toArray⟩,
    sx.time + sy.time + 2 * TimeM.timeMergeSortRec n + wt + 10 * n + 1)

/-- **Binary search for a rank cut.** Search the slice starting at `start` of length `len`
for the first key failing `pass`, returning its index (or the end) when the slice is in bounds
and the passing keys form a prefix. A missing array entry fails the test. The second result
counts one per midpoint probe and one for the terminal empty slice. -/
def cutRank {β : Type*} (keys : Array β) (pass : β → Bool) (start len : Nat) : Nat × Nat :=
  if len = 0 then (start, 1) else
    let k := len / 2
    let m := start + k
    let (i, w) := if keys[m]?.any pass then cutRank keys pass (m + 1) (len - (k + 1))
      else cutRank keys pass start k
    (i, w + 1)
termination_by len
decreasing_by all_goals omega

/-- **Querying a planar rank index.** For an index built by `preprocess` from points in
general position, four binary searches count the keys strictly below each lower endpoint and
weakly below each upper endpoint. The intervening ranks form a closed integer box, and each
reported leaf decodes to its original point by x rank.

On any index, an empty computed rank interval yields no points. Otherwise the query reports
in the rank tree and looks up the hits in the x dictionary, skipping out-of-bounds lookups.
Unsorted dictionaries need not give endpoint counts, and inconsistent ranks need not decode
to the intended points. Work charges probes and terminal calls, one setup unit, visited tree
constructors, and one lookup per reported rank point. -/
def Index.query {α : Type*} [LinearOrder α] (idx : Index α) (lo hi : α × α) :
    List (α × α) × Nat :=
  let (lx, w₁) := cutRank idx.byX (fun p => p.1 < lo.1) 0 idx.byX.size
  let (ux, w₂) := cutRank idx.byX (fun p => p.1 ≤ hi.1) 0 idx.byX.size
  let (ly, w₃) := cutRank idx.byY (fun y => y < lo.2) 0 idx.byY.size
  let (uy, w₄) := cutRank idx.byY (fun y => y ≤ hi.2) 0 idx.byY.size
  let w := w₁ + w₂ + w₃ + w₄ + 1
  if ux ≤ lx ∨ uy ≤ ly then ([], w) else
    let l (a : Fin 2) : Int := 2 * (if a = 0 then (lx : Int) else ly)
    let u (a : Fin 2) : Int := 2 * (if a = 0 then (ux : Int) else uy) - 2
    let hits := idx.tree.report l u
    (hits.filterMap (fun p => idx.byX[(p 0).toNat / 2]?),
      w + reportVisits l u idx.tree + hits.length)

end Planar
end Cslib.Algorithms.Lean.KdTree
