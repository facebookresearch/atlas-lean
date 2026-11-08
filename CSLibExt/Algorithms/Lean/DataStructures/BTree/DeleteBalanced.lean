/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BTree

/-!
# B-tree deletion by a top-down pass

Top-down deletion for the B-trees of
`CSLibExt.Algorithms.Lean.DataStructures.BTree`, following CLRS
Section 18.3. Unlike `deleteRebuild` in the sibling module
`CSLibExt.Algorithms.Lean.DataStructures.BTree.Delete` (the declaration
`Cslib.Algorithms.Lean.BTree.deleteRebuild`), which erases the key from
the flattening and rebuilds the tree by insertion, `delete` here descends
from the root to a leaf, repairing occupancy along the way. This `delete`
is the primary deletion operation for B-trees; `deleteRebuild` is retained
as a reference implementation with the same set semantics.
Predecessor and successor keys are found by descending a single spine
(`maxKey`/`minKey`), never by flattening a subtree. Deleting a separator
key therefore traverses that spine twice: `maxKey` (dually `minKey`)
first descends the rightmost (leftmost) spine of the child to read the
predecessor (successor), and the recursive deletion then descends the
same spine again to remove it. The total is still `O(t * height)` list
cells, matching the CLRS bound up to the list representation of nodes,
but the separator case is not literally a single root-to-leaf pass.

The descent maintains the CLRS precondition that every node entered (other
than the root) holds at least `t` keys: before descending into a child with
only `t - 1` keys, `delList` either borrows a key for it from an adjacent
sibling with at least `t` keys (`borrowRight`/`borrowLeft`: the separator
moves down into the child and the sibling's nearest key moves up), or merges
the child with the separator and the sibling into one node with `2 * t - 1`
keys (`merge`). A separator key itself is deleted by promoting its
predecessor or successor when the corresponding child has at least `t`
keys, and by merging its two children otherwise. The recursion is indexed
by height (`delH`), so a merged node is deleted from at the children's
height. The public `delete` collapses the root when a root merge leaves
it with no keys and a single child, the only way the height decreases
(`delete_validRoot`).

The specifications are `flatten_delete` (the flattening of the result is
`(flatten tree).erase x`), `IsBTree.delete` (the result is ordered and
root-valid), and the height statement `delete_validRoot` (the result is
root-valid at the height of the input or one less).
-/

set_option autoImplicit false

universe u

@[expose] public section

namespace Cslib.Algorithms.Lean

namespace BTree

variable {α : Type u}

/-- The number of keys stored at the root of a tree. -/
public def keyCount : BTree α → Nat
  | .leaf keys => keys.length
  | .node keys _ => keys.length

/-- Split a nonempty list into all but its last element and its last
element. -/
def splitLast : List α → Option (List α × α)
  | [] => none
  | a :: l => some ((a :: l).dropLast, (a :: l).getLast (by simp))

private theorem splitLast_spec {l : List α} {init : List α} {last : α}
    (h : splitLast l = some (init, last)) : l = init ++ [last] := by
  cases l with
  | nil => simp [splitLast] at h
  | cons a l =>
      simp only [splitLast, Option.some.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [List.dropLast_append_getLast]

private theorem splitLast_length {l : List α} {init : List α} {last : α}
    (h : splitLast l = some (init, last)) : init.length + 1 = l.length := by
  have hspec := congrArg List.length (splitLast_spec h)
  simp at hspec
  omega

private theorem splitLast_of_ne_nil {l : List α} (h : l ≠ []) :
    ∃ init last, splitLast l = some (init, last) := by
  cases l with
  | nil => exact absurd rfl h
  | cons a l => exact ⟨_, _, rfl⟩

/-- The greatest key of a tree, found by descending the rightmost spine:
at each internal node, recurse into the last child only. Each step splits
a child list of length at most `2 * t`, so on a valid tree this costs
`O(t * height)`; it never materializes the flattening. The characterization
as the last key of the flattening is `exists_maxKey_flatten` below. -/
def maxKey : BTree α → Option α
  | .leaf keys => keys.getLast?
  | .node keys children =>
      match h : splitLast children with
      | some (_, last) => maxKey last
      | none => keys.getLast?
termination_by tree => sizeOf tree
decreasing_by
  have hmem : last ∈ children := by
    rw [splitLast_spec h]
    simp
  have hlt := List.sizeOf_lt_of_mem hmem
  rw [BTree.node.sizeOf_spec]
  omega

private theorem maxKey_leaf {keys : List α} :
    maxKey (.leaf keys : BTree α) = keys.getLast? := by
  rw [maxKey]

private theorem maxKey_node_some {keys : List α} {children : List (BTree α)}
    {initC : List (BTree α)} {last : BTree α}
    (h : splitLast children = some (initC, last)) :
    maxKey (.node keys children) = maxKey last := by
  conv_lhs => rw [maxKey]
  rw [h]

/-- The least key of a tree, found by descending the leftmost spine. The
characterization as the first key of the flattening is
`exists_minKey_flatten` below. -/
def minKey : BTree α → Option α
  | .leaf keys => keys.head?
  | .node keys children =>
      match children with
      | child :: _ => minKey child
      | [] => keys.head?

private theorem minKey_leaf {keys : List α} :
    minKey (.leaf keys : BTree α) = keys.head? :=
  rfl

private theorem minKey_node_cons {keys : List α} {child : BTree α}
    {rest : List (BTree α)} :
    minKey (.node keys (child :: rest)) = minKey child :=
  rfl

/-- Merge two trees of the same height and a separator key between them
into a single node: the keys concatenate around the separator and the
children concatenate. Used when both trees hold `t - 1` keys, so the
result holds `2 * t - 1`. -/
def merge (sep : α) : BTree α → BTree α → BTree α
  | .leaf ks1, .leaf ks2 => .leaf (ks1 ++ sep :: ks2)
  | .node ks1 cs1, .node ks2 cs2 => .node (ks1 ++ sep :: ks2) (cs1 ++ cs2)
  | tree, _ => tree

/-- Borrow for `child` from its right sibling: the separator `sep` moves
down as the child's last key (with the sibling's first child), and the
sibling's first key moves up as the new separator. Returns the new child,
separator, and sibling. -/
def borrowRight : BTree α → α → BTree α → BTree α × α × BTree α
  | .leaf ks, sep, .leaf (s0 :: ss) => (.leaf (ks ++ [sep]), s0, .leaf ss)
  | .node ks cs, sep, .node (s0 :: ss) (sc0 :: scs) =>
      (.node (ks ++ [sep]) (cs ++ [sc0]), s0, .node ss scs)
  | child, sep, sib => (child, sep, sib)

/-- Borrow for `child` from its left sibling: the separator `sep` moves
down as the child's first key (with the sibling's last child), and the
sibling's last key moves up as the new separator. Returns the new sibling,
separator, and child. -/
def borrowLeft : BTree α → α → BTree α → BTree α × α × BTree α
  | .leaf ks, sep, .leaf kc =>
      match splitLast ks with
      | some (init, last) => (.leaf init, last, .leaf (sep :: kc))
      | none => (.leaf ks, sep, .leaf kc)
  | .node ks cs, sep, .node kc cc =>
      match splitLast ks, splitLast cs with
      | some (iks, last), some (ics, clast) =>
          (.node iks ics, last, .node (sep :: kc) (clast :: cc))
      | _, _ => (.node ks cs, sep, .node kc cc)
  | sib, sep, child => (sib, sep, child)

/-- Delete a key from the node with the given separator and child lists,
where `delChild` deletes from a child (in `delH`, deletion at the next
height down). Before descending into a child with fewer than `t` keys, the
child is given a key by borrowing from an adjacent sibling or is merged
with the separator and a sibling, so `delChild` is only ever applied to a
tree holding at least `t` keys at its root (or to a merged tree). The walk
goes from the left: a child that is not last borrows or merges on its
right, and the last child borrows or merges on its left, where its left
sibling and separator are in hand. -/
def delList [LinearOrder α] (delChild : α → BTree α → BTree α) (t : Nat)
    (x : α) : List α → List (BTree α) → List α × List (BTree α)
  | [], child :: children => ([], delChild x child :: children)
  | [], [] => ([], [])
  | key :: keys, child :: children =>
      if x < key then
        if t ≤ keyCount child then (key :: keys, delChild x child :: children)
        else
          match children with
          | sib :: rest =>
              if t ≤ keyCount sib then
                let (child', sep', sib') := borrowRight child key sib
                (sep' :: keys, delChild x child' :: sib' :: rest)
              else (keys, delChild x (merge key child sib) :: rest)
          | [] => (key :: keys, delChild x child :: children)
      else if key < x then
        match keys, children with
        | [], [last] =>
            if t ≤ keyCount last then ([key], [child, delChild x last])
            else if t ≤ keyCount child then
              let (child', sep', last') := borrowLeft child key last
              ([sep'], [child', delChild x last'])
            else ([], [delChild x (merge key child last)])
        | _ :: _, _ =>
            let (keys', children') := delList delChild t x keys children
            (key :: keys', child :: children')
        | _, _ => (key :: keys, child :: children)
      else
        match children with
        | rchild :: rest =>
            if t ≤ keyCount child then
              match maxKey child with
              | some p => (p :: keys, delChild p child :: rchild :: rest)
              | none => (key :: keys, child :: children)
            else if t ≤ keyCount rchild then
              match minKey rchild with
              | some s => (s :: keys, child :: delChild s rchild :: rest)
              | none => (key :: keys, child :: children)
            else (keys, delChild x (merge key child rchild) :: rest)
        | [] => (key :: keys, child :: children)
  | keys, children => (keys, children)

/-- Delete a key from a tree of the given height, by a top-down pass
(with the two spine traversals in the separator case described in the
module documentation): at a leaf erase the key, and at an internal node
run `delList` with
deletion at the children's height. Heights that do not match the shape of
the tree fall back to leaf erasure or the identity; the specification
`delH_spec` only covers matching heights. -/
def delH [LinearOrder α] : Nat → Nat → α → BTree α → BTree α
  | 0, _, x, .leaf keys => .leaf (keys.erase x)
  | 0, _, _, .node keys children => .node keys children
  | _ + 1, _, x, .leaf keys => .leaf (keys.erase x)
  | h + 1, t, x, .node keys children =>
      match delList (delH h t) t x keys children with
      | (keys', children') => .node keys' children'

/-- The height of a tree following first children: leaves have height `0`
and an internal node is one taller than its first child. For a valid tree
this is the height index of `Valid`/`ValidRoot`. -/
public def treeHeight : BTree α → Nat
  | .leaf _ => 0
  | .node _ children =>
      match children with
      | [] => 0
      | child :: _ => treeHeight child + 1

/-- Delete a key from a B-tree of minimum degree `t` by a single top-down
pass, collapsing the root when a root merge leaves it keyless with a
single child. See the module documentation for the algorithm and its
specifications. -/
public def delete [LinearOrder α] (t : Nat) (x : α) (tree : BTree α) :
    BTree α :=
  match delH (treeHeight tree) t x tree with
  | .node [] [child] => child
  | other => other

/-- Deprecated alias for `delete`. Kept so existing references to
`BTree.deleteBal` keep elaborating; new code should use `delete`. -/
@[deprecated "use Cslib.Algorithms.Lean.BTree.delete instead"
  (since := "2026-10-12")]
public def deleteBal [LinearOrder α] (t : Nat) (x : α) (tree : BTree α) :
    BTree α :=
  delete t x tree

private theorem flatten_merge_leaf {sep : α} {ks1 ks2 : List α} :
    flatten (merge sep (.leaf ks1) (.leaf ks2)) = ks1 ++ sep :: ks2 := by
  simp [merge]

private theorem flatten_merge_node {sep : α} {ks1 ks2 : List α}
    {cs1 cs2 : List (BTree α)} (hlen : cs1.length = ks1.length + 1) :
    flatten (merge sep (.node ks1 cs1) (.node ks2 cs2)) =
      flatten (.node ks1 cs1) ++ sep :: flatten (.node ks2 cs2) :=
  flatten_node_append_cons hlen

private theorem flatten_borrowRight_leaf {sep s0 : α} {ks ss : List α} :
    flatten (.leaf (ks ++ [sep]) : BTree α) ++
        s0 :: flatten (.leaf ss : BTree α) =
      flatten (.leaf ks : BTree α) ++
        sep :: flatten (.leaf (s0 :: ss) : BTree α) := by
  simp only [flatten_leaf]
  rw [List.append_assoc]
  rfl

private theorem flatten_borrowRight_node {sep s0 : α} {ks ss : List α}
    {cs scs : List (BTree α)} {sc0 : BTree α}
    (hlen : cs.length = ks.length + 1) :
    flatten (.node (ks ++ [sep]) (cs ++ [sc0])) ++
        s0 :: flatten (.node ss scs) =
      flatten (.node ks cs) ++ sep :: flatten (.node (s0 :: ss) (sc0 :: scs)) := by
  rw [flatten_node_append_cons hlen, flatten_node_nil, flatten_node_cons]
  simp [List.append_assoc]

private theorem flatten_borrowLeft_leaf {sep last : α} {ks init kc : List α}
    (hks : ks = init ++ [last]) :
    flatten (.leaf init : BTree α) ++ last :: flatten (.leaf (sep :: kc) : BTree α) =
      flatten (.leaf ks : BTree α) ++ sep :: flatten (.leaf kc : BTree α) := by
  simp only [flatten_leaf]
  rw [hks, List.append_assoc]
  rfl

private theorem flatten_borrowLeft_node {sep last : α} {ks iks kc : List α}
    {cs ics cc : List (BTree α)} {clast : BTree α}
    (hks : ks = iks ++ [last]) (hcs : cs = ics ++ [clast])
    (hlen : ics.length = iks.length + 1) :
    flatten (.node iks ics) ++ last :: flatten (.node (sep :: kc) (clast :: cc)) =
      flatten (.node ks cs) ++ sep :: flatten (.node kc cc) := by
  rw [hks, hcs, flatten_node_append_cons hlen, flatten_node_nil,
    flatten_node_cons]
  simp [List.append_assoc]

private theorem valid_weaken {t mink mink' h : Nat} {tree : BTree α}
    (hv : Valid t mink h tree) (hle : mink' ≤ mink) : Valid t mink' h tree := by
  cases hv with
  | leaf hlo hhi => exact Valid.leaf (Nat.le_trans hle hlo) hhi
  | node hlo hhi hlen hch => exact Valid.node (Nat.le_trans hle hlo) hhi hlen hch

private theorem valid_of_keyCount {t mink mink' h : Nat} {tree : BTree α}
    (hv : Valid t mink h tree) (hle : mink' ≤ keyCount tree) :
    Valid t mink' h tree := by
  cases hv with
  | leaf hlo hhi => exact Valid.leaf hle hhi
  | node hlo hhi hlen hch => exact Valid.node hle hhi hlen hch

private theorem keyCount_pos_of_valid {t h : Nat} {tree : BTree α}
    (hv : Valid t (t - 1) h tree) (ht : 2 ≤ t) : 1 ≤ keyCount tree := by
  cases hv with
  | leaf hlo _ => exact Nat.le_trans (by omega : 1 ≤ t - 1) hlo
  | node hlo _ _ _ => exact Nat.le_trans (by omega : 1 ≤ t - 1) hlo

/-- On a valid tree with a key at its root, the rightmost-spine descent
`maxKey` finds the last key of the flattening. -/
private theorem exists_maxKey_flatten {t : Nat} (ht : 2 ≤ t) :
    ∀ h {mink : Nat} {tree : BTree α}, Valid t mink h tree →
      0 < keyCount tree →
      ∃ init p, maxKey tree = some p ∧ flatten tree = init ++ [p] := by
  intro h
  induction h with
  | zero =>
      intro mink tree hv hkc
      cases hv with
      | @leaf _ keys hlo hhi =>
          have hne : keys ≠ ([] : List α) := by
            simp only [keyCount] at hkc
            exact List.ne_nil_of_length_pos hkc
          refine ⟨keys.dropLast, keys.getLast hne, ?_, ?_⟩
          · rw [maxKey_leaf, List.getLast?_eq_getLast]
          · rw [flatten_leaf]
            exact (List.dropLast_append_getLast hne).symm
  | succ h ih =>
      intro mink tree hv hkc
      cases hv with
      | @node _ _ keys children hlo hhi hlen hch =>
          have hne : children ≠ [] := by
            intro hnil
            rw [hnil] at hlen
            simp at hlen
          obtain ⟨initC, last, hsl⟩ := splitLast_of_ne_nil hne
          have hcs : children = initC ++ [last] := splitLast_spec hsl
          have hvLast : Valid t (t - 1) h last :=
            hch last (by rw [hcs]; simp)
          obtain ⟨init', p, hmk, hflat'⟩ :=
            ih hvLast (keyCount_pos_of_valid hvLast ht)
          have hmkNode : maxKey (.node keys children) = some p := by
            rw [maxKey_node_some hsl, hmk]
          by_cases hkeys : keys = []
          · subst hkeys
            have hinit : initC = [] := by
              have h1 : (initC ++ [last]).length = 1 := by
                rw [← hcs]; simpa using hlen
              simp only [List.length_append, List.length_cons,
                List.length_nil] at h1
              exact List.eq_nil_of_length_eq_zero (by omega)
            refine ⟨init', p, hmkNode, ?_⟩
            rw [hcs, hinit]
            simp only [List.nil_append]
            rw [flatten_node_nil, hflat']
          · obtain ⟨keys₁, median, hslk⟩ := splitLast_of_ne_nil hkeys
            have hks : keys = keys₁ ++ [median] := splitLast_spec hslk
            have hlen1 : initC.length = keys₁.length + 1 := by
              have e1 := congrArg List.length hcs
              have e2 := congrArg List.length hks
              simp only [List.length_append, List.length_cons,
                List.length_nil] at e1 e2
              omega
            refine ⟨flatten (.node keys₁ initC) ++ median :: init', p,
              hmkNode, ?_⟩
            rw [hks, hcs, flatten_node_append_cons hlen1, flatten_node_nil,
              hflat']
            simp [List.append_assoc]

/-- On a valid tree with a key at its root, the leftmost-spine descent
`minKey` finds the first key of the flattening. -/
private theorem exists_minKey_flatten {t : Nat} (ht : 2 ≤ t) :
    ∀ h {mink : Nat} {tree : BTree α}, Valid t mink h tree →
      0 < keyCount tree →
      ∃ s rest, minKey tree = some s ∧ flatten tree = s :: rest := by
  intro h
  induction h with
  | zero =>
      intro mink tree hv hkc
      cases hv with
      | @leaf _ keys hlo hhi =>
          simp only [keyCount] at hkc
          cases keys with
          | nil => simp at hkc
          | cons k ks =>
              exact ⟨k, ks, rfl, by rw [flatten_leaf]⟩
  | succ h ih =>
      intro mink tree hv hkc
      cases hv with
      | @node _ _ keys children hlo hhi hlen hch =>
          cases children with
          | nil => simp at hlen
          | cons first crest =>
              have hvFirst : Valid t (t - 1) h first := hch first (by simp)
              obtain ⟨s, restF, hmk, hflat'⟩ :=
                ih hvFirst (keyCount_pos_of_valid hvFirst ht)
              have hmkNode : minKey (.node keys (first :: crest)) = some s := by
                rw [minKey_node_cons, hmk]
              cases keys with
              | nil =>
                  have hcrest : crest = [] := by
                    simp only [List.length_cons, List.length_nil] at hlen
                    exact List.eq_nil_of_length_eq_zero (by omega)
                  subst hcrest
                  exact ⟨s, restF, hmkNode, by
                    rw [flatten_node_nil, hflat']⟩
              | cons k ks =>
                  refine ⟨s, restF ++ k :: flatten (.node ks crest),
                    hmkNode, ?_⟩
                  rw [flatten_node_cons, hflat']
                  rfl

private theorem flatten_ne_nil_of_keyCount_pos {tree : BTree α}
    (h : 0 < keyCount tree) : flatten tree ≠ [] := by
  cases tree with
  | leaf keys =>
      simp only [keyCount] at h
      cases keys with
      | nil => simp at h
      | cons k ks => simp [flatten_leaf]
  | node keys children =>
      simp only [keyCount] at h
      cases keys with
      | nil => simp at h
      | cons k ks =>
          intro hflat
          have hmem : k ∈ flatten (.node (k :: ks) children : BTree α) := by
            have hm := mem_node (x := k) (keys := k :: ks) (children := children)
            exact hm.mpr (Or.inl (by simp))
          rw [hflat] at hmem
          simp at hmem

private theorem merge_valid {t h : Nat} (ht : 2 ≤ t) {sep : α} {a b : BTree α}
    (ha : Valid t (t - 1) h a) (hb : Valid t (t - 1) h b)
    (hka : keyCount a ≤ t - 1) (hkb : keyCount b ≤ t - 1) :
    Valid t t h (merge sep a b) := by
  cases a with
  | leaf ksa =>
      cases b with
      | leaf ksb =>
          cases ha with
          | leaf hloA hhiA =>
              cases hb with
              | leaf hloB hhiB =>
                  have hka' : ksa.length ≤ t - 1 := hka
                  have hkb' : ksb.length ≤ t - 1 := hkb
                  refine Valid.leaf ?_ ?_ <;> simp [List.length_append] <;> omega
      | node ksb csb =>
          cases ha
          cases hb
  | node ksa csa =>
      cases b with
      | leaf ksb =>
          cases ha
          cases hb
      | node ksb csb =>
          cases ha with
          | node hloA hhiA hlenA hchA =>
              cases hb with
              | node hloB hhiB hlenB hchB =>
                  have hka' : ksa.length ≤ t - 1 := hka
                  have hkb' : ksb.length ≤ t - 1 := hkb
                  refine Valid.node ?_ ?_ ?_ ?_
                  · simp [List.length_append]; omega
                  · simp [List.length_append]; omega
                  · simp [List.length_append]; omega
                  · intro c hc
                    rw [List.mem_append] at hc
                    rcases hc with hc | hc
                    · exact hchA c hc
                    · exact hchB c hc

private theorem borrowRight_valid {t h : Nat} (ht : 2 ≤ t) {child : BTree α}
    {sep : α} {sib : BTree α}
    (hchild : Valid t (t - 1) h child) (hsib : Valid t (t - 1) h sib)
    (hkc : keyCount child = t - 1) (hks : t ≤ keyCount sib) :
    Valid t t h (borrowRight child sep sib).1 ∧
      Valid t (t - 1) h (borrowRight child sep sib).2.2 := by
  cases child with
  | leaf ksc =>
      cases sib with
      | leaf kss =>
          cases kss with
          | nil =>
              have hks' : t ≤ ([] : List α).length := hks
              simp at hks'
              omega
          | cons s0 ss =>
              cases hchild with
              | leaf hloC hhiC =>
                  cases hsib with
                  | leaf hloS hhiS =>
                      have hkc' : ksc.length = t - 1 := hkc
                      have hks' : t ≤ (s0 :: ss).length := hks
                      have hlen1 : (ksc ++ [sep]).length = ksc.length + 1 := by
                        simp
                      have hlen2 : (s0 :: ss).length = ss.length + 1 := rfl
                      refine ⟨Valid.leaf ?_ ?_, Valid.leaf ?_ ?_⟩ <;> omega
      | node kss css =>
          cases hchild
          cases hsib
  | node ksc csc =>
      cases sib with
      | leaf kss =>
          cases hchild
          cases hsib
      | node kss css =>
          cases kss with
          | nil =>
              have hks' : t ≤ ([] : List α).length := hks
              simp at hks'
              omega
          | cons s0 ss =>
              cases css with
              | nil =>
                  cases hsib with
                  | node _ _ hlenS _ => simp at hlenS
              | cons sc0 scs =>
                  cases hchild with
                  | node hloC hhiC hlenC hchC =>
                      cases hsib with
                      | node hloS hhiS hlenS hchS =>
                          have hkc' : ksc.length = t - 1 := hkc
                          have hks' : t ≤ (s0 :: ss).length := hks
                          have hlenSS : (s0 :: ss).length = ss.length + 1 := rfl
                          have hlenSC : (sc0 :: scs).length = scs.length + 1 := rfl
                          refine ⟨Valid.node ?_ ?_ ?_ ?_, Valid.node ?_ ?_ ?_ ?_⟩
                          · simp [List.length_append]; omega
                          · simp [List.length_append]; omega
                          · simp [List.length_append]; omega
                          · intro c hc
                            rw [List.mem_append] at hc
                            rcases hc with hc | hc
                            · exact hchC c hc
                            · rw [List.mem_singleton] at hc
                              rw [hc]
                              exact hchS sc0 (by simp)
                          · omega
                          · omega
                          · omega
                          · intro c hc
                            exact hchS c (List.mem_cons_of_mem sc0 hc)

private theorem borrowLeft_valid {t h : Nat} (ht : 2 ≤ t) {sib : BTree α}
    {sep : α} {child : BTree α}
    (hsib : Valid t (t - 1) h sib) (hchild : Valid t (t - 1) h child)
    (hks : t ≤ keyCount sib) (hkc : keyCount child = t - 1) :
    Valid t (t - 1) h (borrowLeft sib sep child).1 ∧
      Valid t t h (borrowLeft sib sep child).2.2 := by
  cases sib with
  | leaf kss =>
      cases child with
      | leaf ksc =>
          cases hsib with
          | leaf hloS hhiS =>
              cases hchild with
              | leaf hloC hhiC =>
                  have hks' : t ≤ kss.length := hks
                  have hkc' : ksc.length = t - 1 := hkc
                  have hne : kss ≠ [] := fun hh => by
                    rw [hh] at hks'
                    simp at hks'
                    omega
                  obtain ⟨init, last, hsl⟩ := splitLast_of_ne_nil hne
                  have hform : borrowLeft (.leaf kss) sep (.leaf ksc) =
                      (.leaf init, last, .leaf (sep :: ksc)) := by
                    simp [borrowLeft, hsl]
                  have hlen : init.length + 1 = kss.length := splitLast_length hsl
                  have hlenSep : (sep :: ksc).length = ksc.length + 1 := rfl
                  rw [hform]
                  refine ⟨Valid.leaf ?_ ?_, Valid.leaf ?_ ?_⟩ <;> omega
      | node ksc csc =>
          cases hsib
          cases hchild
  | node kss css =>
      cases child with
      | leaf ksc =>
          cases hsib
          cases hchild
      | node ksc csc =>
          cases hsib with
          | node hloS hhiS hlenS hchS =>
              cases hchild with
              | node hloC hhiC hlenC hchC =>
                  have hks' : t ≤ kss.length := hks
                  have hkc' : ksc.length = t - 1 := hkc
                  have hneK : kss ≠ [] := fun hh => by
                    rw [hh] at hks'
                    simp at hks'
                    omega
                  have hneC : css ≠ [] := fun hh => by
                    rw [hh] at hlenS
                    simp at hlenS
                  obtain ⟨iks, last, hslK⟩ := splitLast_of_ne_nil hneK
                  obtain ⟨ics, clast, hslC⟩ := splitLast_of_ne_nil hneC
                  have hform : borrowLeft (.node kss css) sep (.node ksc csc) =
                      (.node iks ics, last, .node (sep :: ksc) (clast :: csc)) := by
                    simp [borrowLeft, hslK, hslC]
                  have hlenK : iks.length + 1 = kss.length :=
                    splitLast_length hslK
                  have hlenCK : ics.length + 1 = css.length :=
                    splitLast_length hslC
                  have hdecompK : kss = iks ++ [last] := splitLast_spec hslK
                  have hdecompC : css = ics ++ [clast] := splitLast_spec hslC
                  have hlenSep : (sep :: ksc).length = ksc.length + 1 := rfl
                  have hlenCl : (clast :: csc).length = csc.length + 1 := rfl
                  rw [hform]
                  refine ⟨Valid.node ?_ ?_ ?_ ?_, Valid.node ?_ ?_ ?_ ?_⟩
                  · omega
                  · omega
                  · omega
                  · intro c hc
                    apply hchS
                    rw [hdecompC, List.mem_append]
                    exact Or.inl hc
                  · omega
                  · omega
                  · omega
                  · intro c hc
                    rw [List.mem_cons] at hc
                    rcases hc with rfl | hc
                    · apply hchS
                      rw [hdecompC, List.mem_append]
                      exact Or.inr (by simp)
                    · exact hchC c hc

private theorem flatten_borrowRight {t h : Nat} (ht : 2 ≤ t) {child : BTree α}
    {sep : α} {sib : BTree α}
    (hchild : Valid t (t - 1) h child) (hsib : Valid t (t - 1) h sib)
    (hkc : keyCount child = t - 1) (hks : t ≤ keyCount sib) :
    flatten (borrowRight child sep sib).1 ++
        (borrowRight child sep sib).2.1 :: flatten (borrowRight child sep sib).2.2 =
      flatten child ++ sep :: flatten sib := by
  cases child with
  | leaf ksc =>
      cases sib with
      | leaf kss =>
          cases kss with
          | nil =>
              have hks' : t ≤ ([] : List α).length := hks
              simp at hks'
              omega
          | cons s0 ss =>
              change flatten (.leaf (ksc ++ [sep])) ++ s0 :: flatten (.leaf ss) =
                flatten (.leaf ksc) ++ sep :: flatten (.leaf (s0 :: ss))
              exact flatten_borrowRight_leaf
      | node kss css =>
          cases hchild
          cases hsib
  | node ksc csc =>
      cases sib with
      | leaf kss =>
          cases hchild
          cases hsib
      | node kss css =>
          cases kss with
          | nil =>
              have hks' : t ≤ ([] : List α).length := hks
              simp at hks'
              omega
          | cons s0 ss =>
              cases css with
              | nil =>
                  cases hsib with
                  | node _ _ hlenS _ => simp at hlenS
              | cons sc0 scs =>
                  cases hchild with
                  | node _ _ hlenC _ =>
                      change flatten (.node (ksc ++ [sep]) (csc ++ [sc0])) ++
                          s0 :: flatten (.node ss scs) =
                        flatten (.node ksc csc) ++
                          sep :: flatten (.node (s0 :: ss) (sc0 :: scs))
                      exact flatten_borrowRight_node hlenC

private theorem flatten_borrowLeft {t h : Nat} (ht : 2 ≤ t) {sib : BTree α}
    {sep : α} {child : BTree α}
    (hsib : Valid t (t - 1) h sib) (hchild : Valid t (t - 1) h child)
    (hks : t ≤ keyCount sib) (hkc : keyCount child = t - 1) :
    flatten (borrowLeft sib sep child).1 ++
        (borrowLeft sib sep child).2.1 :: flatten (borrowLeft sib sep child).2.2 =
      flatten sib ++ sep :: flatten child := by
  cases sib with
  | leaf kss =>
      cases child with
      | leaf ksc =>
          cases hsib with
          | leaf hloS hhiS =>
              have hks' : t ≤ kss.length := hks
              have hne : kss ≠ [] := fun hh => by
                rw [hh] at hks'
                simp at hks'
                omega
              obtain ⟨init, last, hsl⟩ := splitLast_of_ne_nil hne
              have hform : borrowLeft (.leaf kss) sep (.leaf ksc) =
                  (.leaf init, last, .leaf (sep :: ksc)) := by
                simp [borrowLeft, hsl]
              rw [hform]
              exact flatten_borrowLeft_leaf (splitLast_spec hsl)
      | node ksc csc =>
          cases hsib
          cases hchild
  | node kss css =>
      cases child with
      | leaf ksc =>
          cases hsib
          cases hchild
      | node ksc csc =>
          cases hsib with
          | node hloS hhiS hlenS hchS =>
              have hks' : t ≤ kss.length := hks
              have hneK : kss ≠ [] := fun hh => by
                rw [hh] at hks'
                simp at hks'
                omega
              have hneC : css ≠ [] := fun hh => by
                rw [hh] at hlenS
                simp at hlenS
              obtain ⟨iks, last, hslK⟩ := splitLast_of_ne_nil hneK
              obtain ⟨ics, clast, hslC⟩ := splitLast_of_ne_nil hneC
              have hform : borrowLeft (.node kss css) sep (.node ksc csc) =
                  (.node iks ics, last, .node (sep :: ksc) (clast :: csc)) := by
                simp [borrowLeft, hslK, hslC]
              have hlenK : iks.length + 1 = kss.length := splitLast_length hslK
              have hlenCK : ics.length + 1 = css.length := splitLast_length hslC
              have hlenI : ics.length = iks.length + 1 := by omega
              rw [hform]
              exact flatten_borrowLeft_node (splitLast_spec hslK)
                (splitLast_spec hslC) hlenI

private theorem pairwise_flatten_of_mem_bal [LT α] {child : BTree α} :
    ∀ {keys : List α} {children : List (BTree α)},
      child ∈ children →
      (flatten (.node keys children)).Pairwise (· < ·) →
      (flatten child).Pairwise (· < ·) := by
  intro keys
  induction keys with
  | nil =>
      intro children hmem hpair
      induction children with
      | nil => exact absurd hmem (by simp)
      | cons head children ih =>
          rw [List.mem_cons] at hmem
          rw [flatten_node_nil_cons] at hpair
          rw [List.pairwise_append] at hpair
          rcases hmem with rfl | hmem
          · exact hpair.1
          · exact ih hmem hpair.2.1
  | cons key keys ih =>
      intro children hmem hpair
      cases children with
      | nil => exact absurd hmem (by simp)
      | cons head children =>
          rw [List.mem_cons] at hmem
          rw [flatten_node_cons] at hpair
          rw [List.pairwise_append] at hpair
          rcases hmem with rfl | hmem
          · exact hpair.1
          · exact ih hmem (List.pairwise_cons.mp hpair.2.1).2

private theorem ordered_child_of_node [LT α] {keys : List α}
    {children : List (BTree α)} {child : BTree α} (hmem : child ∈ children)
    (h : Ordered (.node keys children)) : Ordered child := by
  have hpair : (flatten (.node keys children)).Pairwise (· < ·) := h
  exact pairwise_flatten_of_mem_bal hmem hpair

private theorem ordered_node_cons_parts [LT α] {key : α} {keys : List α}
    {child : BTree α} {children : List (BTree α)}
    (h : Ordered (.node (key :: keys) (child :: children))) :
    (flatten child).Pairwise (· < ·) ∧ (∀ y ∈ flatten child, y < key) ∧
      (∀ y ∈ flatten (.node keys children), key < y) ∧
      Ordered (.node keys children) := by
  have hpair : (flatten child ++
      key :: flatten (.node keys children)).Pairwise (· < ·) := by
    have h' : (flatten (.node (key :: keys) (child :: children))).Pairwise
        (· < ·) := h
    rwa [flatten_node_cons] at h'
  rw [List.pairwise_append] at hpair
  obtain ⟨hpC, hpRest, hcross⟩ := hpair
  rw [List.pairwise_cons] at hpRest
  exact ⟨hpC, fun y hy => hcross y hy key List.mem_cons_self, hpRest.1,
    hpRest.2⟩

private theorem exists_flatten_tail {keys : List α} {cs : List (BTree α)}
    (hlen : cs.length = keys.length) :
    ∃ T : List α, ∀ (c : BTree α),
      flatten (.node keys (c :: cs)) = flatten c ++ T := by
  cases keys with
  | nil =>
      cases cs with
      | nil => exact ⟨[], fun c => by simp [flatten_node_nil]⟩
      | cons _ _ => simp at hlen
  | cons k ks =>
      exact ⟨k :: flatten (.node ks cs), fun c => flatten_node_cons⟩

private theorem erase_cons_tail_of_ne {a b : α} [LinearOrder α]
    {l : List α} (h : b ≠ a) : (b :: l).erase a = b :: l.erase a :=
  List.erase_cons_tail (fun hb => h (beq_iff_eq.mp hb))

private theorem erase_append_of_not_mem_left [LinearOrder α] {x : α}
    {left right : List α} (hx : x ∉ left) :
    (left ++ right).erase x = left ++ right.erase x := by
  rw [List.erase_append, ite_eq_right hx]

private theorem erase_append_of_not_mem_right [LinearOrder α] {x : α}
    {left right : List α} (hx : x ∉ right) :
    (left ++ right).erase x = left.erase x ++ right := by
  by_cases hxLeft : x ∈ left
  · rw [List.erase_append, ite_eq_left hxLeft]
  · rw [List.erase_append, ite_eq_right hxLeft, List.erase_of_not_mem hx,
      List.erase_of_not_mem hxLeft]

private theorem treeHeight_of_valid (h : Nat) :
    ∀ {t mink : Nat} {tree : BTree α}, Valid t mink h tree →
    treeHeight tree = h := by
  induction h with
  | zero =>
      intro t mink tree hv
      cases tree with
      | leaf _ => rfl
      | node _ _ => cases hv
  | succ h ih =>
      intro t mink tree hv
      cases tree with
      | leaf _ => cases hv
      | node keys children =>
          cases hv with
          | node _ _ hlen hch =>
              cases children with
              | nil => simp at hlen
              | cons c cs =>
                  have heq : treeHeight (.node keys (c :: cs) : BTree α) =
                      treeHeight c + 1 := rfl
                  rw [heq, ih (hch c (by simp))]

private theorem treeHeight_of_validRoot {t h : Nat} {tree : BTree α}
    (hv : ValidRoot t h tree) : treeHeight tree = h := by
  obtain ⟨mink, hv'⟩ := hv.valid
  exact treeHeight_of_valid h hv'

private theorem keyCount_ge_of_valid {t mink h : Nat} {tree : BTree α}
    (hv : Valid t mink h tree) : mink ≤ keyCount tree := by
  cases hv with
  | leaf hlo _ => exact hlo
  | node hlo _ _ _ => exact hlo

private theorem flatten_merge_eq {t h : Nat} {sep : α} {a b : BTree α}
    (ha : Valid t (t - 1) h a) (hb : Valid t (t - 1) h b) :
    flatten (merge sep a b) = flatten a ++ sep :: flatten b := by
  cases a with
  | leaf ksa =>
      cases b with
      | leaf ksb => rw [flatten_merge_leaf, flatten_leaf, flatten_leaf]
      | node ksb csb =>
          cases ha
          cases hb
  | node ksa csa =>
      cases b with
      | leaf ksb =>
          cases ha
          cases hb
      | node ksb csb =>
          cases ha with
          | node _ _ hlenA _ => exact flatten_merge_node hlenA

private theorem borrowRight_sep_mem {t h : Nat} (ht : 2 ≤ t) {child : BTree α}
    {sep : α} {sib : BTree α}
    (hchild : Valid t (t - 1) h child) (hsib : Valid t (t - 1) h sib)
    (hks : t ≤ keyCount sib) :
    (borrowRight child sep sib).2.1 ∈ flatten sib := by
  cases child with
  | leaf ksc =>
      cases sib with
      | leaf kss =>
          cases kss with
          | nil =>
              have hks' : t ≤ ([] : List α).length := hks
              simp at hks'
              omega
          | cons s0 ss =>
              change s0 ∈ flatten (.leaf (s0 :: ss) : BTree α)
              simp [flatten_leaf]
      | node kss css =>
          cases hchild
          cases hsib
  | node ksc csc =>
      cases sib with
      | leaf kss =>
          cases hchild
          cases hsib
      | node kss css =>
          cases kss with
          | nil =>
              have hks' : t ≤ ([] : List α).length := hks
              simp at hks'
              omega
          | cons s0 ss =>
              cases css with
              | nil =>
                  cases hsib with
                  | node _ _ hlenS _ => simp at hlenS
              | cons sc0 scs =>
                  change s0 ∈ flatten (.node (s0 :: ss) (sc0 :: scs))
                  rw [flatten_node_cons]
                  exact List.mem_append_right _ List.mem_cons_self

private theorem borrowRight_sib'_mem {t h : Nat} (ht : 2 ≤ t) {child : BTree α}
    {sep : α} {sib : BTree α} {y : α}
    (hchild : Valid t (t - 1) h child) (hsib : Valid t (t - 1) h sib)
    (hks : t ≤ keyCount sib)
    (hy : y ∈ flatten (borrowRight child sep sib).2.2) : y ∈ flatten sib := by
  cases child with
  | leaf ksc =>
      cases sib with
      | leaf kss =>
          cases kss with
          | nil =>
              have hks' : t ≤ ([] : List α).length := hks
              simp at hks'
              omega
          | cons s0 ss =>
              have hy' : y ∈ flatten (.leaf ss : BTree α) := hy
              change y ∈ flatten (.leaf (s0 :: ss) : BTree α)
              simp only [flatten_leaf] at hy' ⊢
              exact List.mem_cons_of_mem s0 hy'
      | node kss css =>
          cases hchild
          cases hsib
  | node ksc csc =>
      cases sib with
      | leaf kss =>
          cases hchild
          cases hsib
      | node kss css =>
          cases kss with
          | nil =>
              have hks' : t ≤ ([] : List α).length := hks
              simp at hks'
              omega
          | cons s0 ss =>
              cases css with
              | nil =>
                  cases hsib with
                  | node _ _ hlenS _ => simp at hlenS
              | cons sc0 scs =>
                  have hy' : y ∈ flatten (.node ss scs) := hy
                  change y ∈ flatten (.node (s0 :: ss) (sc0 :: scs))
                  rw [flatten_node_cons]
                  exact List.mem_append_right _ (List.mem_cons_of_mem s0 hy')

private theorem borrowLeft_sep_mem {t h : Nat} (ht : 2 ≤ t) {sib : BTree α}
    {sep : α} {child : BTree α}
    (hsib : Valid t (t - 1) h sib) (hchild : Valid t (t - 1) h child)
    (hks : t ≤ keyCount sib) :
    (borrowLeft sib sep child).2.1 ∈ flatten sib := by
  cases sib with
  | leaf kss =>
      cases child with
      | leaf ksc =>
          have hks' : t ≤ kss.length := hks
          have hne : kss ≠ [] := fun hh => by
            rw [hh] at hks'
            simp at hks'
            omega
          obtain ⟨init, last, hsl⟩ := splitLast_of_ne_nil hne
          have hform : borrowLeft (.leaf kss) sep (.leaf ksc) =
              (.leaf init, last, .leaf (sep :: ksc)) := by
            simp [borrowLeft, hsl]
          rw [hform]
          change last ∈ flatten (.leaf kss : BTree α)
          rw [flatten_leaf, splitLast_spec hsl]
          simp
      | node ksc csc =>
          cases hsib
          cases hchild
  | node kss css =>
      cases child with
      | leaf ksc =>
          cases hsib
          cases hchild
      | node ksc csc =>
          cases hsib with
          | node hloS hhiS hlenS hchS =>
              have hks' : t ≤ kss.length := hks
              have hneK : kss ≠ [] := fun hh => by
                rw [hh] at hks'
                simp at hks'
                omega
              have hneC : css ≠ [] := fun hh => by
                rw [hh] at hlenS
                simp at hlenS
              obtain ⟨iks, last, hslK⟩ := splitLast_of_ne_nil hneK
              obtain ⟨ics, clast, hslC⟩ := splitLast_of_ne_nil hneC
              have hform : borrowLeft (.node kss css) sep (.node ksc csc) =
                  (.node iks ics, last, .node (sep :: ksc) (clast :: csc)) := by
                simp [borrowLeft, hslK, hslC]
              rw [hform]
              change last ∈ flatten (.node kss css)
              have hm := mem_node (x := last) (keys := kss) (children := css)
              apply hm.mpr
              refine Or.inl ?_
              rw [splitLast_spec hslK]
              simp

private theorem borrowLeft_sib'_mem {t h : Nat} (ht : 2 ≤ t) {sib : BTree α}
    {sep : α} {child : BTree α} {y : α}
    (hsib : Valid t (t - 1) h sib) (hchild : Valid t (t - 1) h child)
    (hks : t ≤ keyCount sib)
    (hy : y ∈ flatten (borrowLeft sib sep child).1) : y ∈ flatten sib := by
  cases sib with
  | leaf kss =>
      cases child with
      | leaf ksc =>
          have hks' : t ≤ kss.length := hks
          have hne : kss ≠ [] := fun hh => by
            rw [hh] at hks'
            simp at hks'
            omega
          obtain ⟨init, last, hsl⟩ := splitLast_of_ne_nil hne
          have hform : borrowLeft (.leaf kss) sep (.leaf ksc) =
              (.leaf init, last, .leaf (sep :: ksc)) := by
            simp [borrowLeft, hsl]
          rw [hform] at hy
          have hy' : y ∈ flatten (.leaf init : BTree α) := hy
          change y ∈ flatten (.leaf kss : BTree α)
          rw [flatten_leaf, splitLast_spec hsl]
          simp only [flatten_leaf] at hy'
          exact List.mem_append_left _ hy'
      | node ksc csc =>
          cases hsib
          cases hchild
  | node kss css =>
      cases child with
      | leaf ksc =>
          cases hsib
          cases hchild
      | node ksc csc =>
          cases hsib with
          | node hloS hhiS hlenS hchS =>
              have hks' : t ≤ kss.length := hks
              have hneK : kss ≠ [] := fun hh => by
                rw [hh] at hks'
                simp at hks'
                omega
              have hneC : css ≠ [] := fun hh => by
                rw [hh] at hlenS
                simp at hlenS
              obtain ⟨iks, last, hslK⟩ := splitLast_of_ne_nil hneK
              obtain ⟨ics, clast, hslC⟩ := splitLast_of_ne_nil hneC
              have hform : borrowLeft (.node kss css) sep (.node ksc csc) =
                  (.node iks ics, last, .node (sep :: ksc) (clast :: csc)) := by
                simp [borrowLeft, hslK, hslC]
              have hlenK2 : iks.length + 1 = kss.length :=
                splitLast_length hslK
              have hlenCK : ics.length + 1 = css.length :=
                splitLast_length hslC
              have hlenI : ics.length = iks.length + 1 := by omega
              rw [hform] at hy
              have hy' : y ∈ flatten (.node iks ics) := hy
              have hflat : flatten (.node kss css) =
                  flatten (.node iks ics) ++ last :: flatten clast := by
                rw [splitLast_spec hslK, splitLast_spec hslC,
                  flatten_node_append_cons hlenI, flatten_node_nil]
              rw [hflat]
              exact List.mem_append_left _ hy'

/-- The specification required of child deletion in `delList`: applied to a
tree of height `h` holding at least `t` keys at its root, it erases the key
from the flattening and returns a tree whose root may drop to `t - 1` keys. -/
private def DelChildSpec [LinearOrder α] (t h : Nat)
    (delChild : α → BTree α → BTree α) : Prop :=
  ∀ (tree : BTree α), Valid t t h tree → Ordered tree → ∀ (y : α),
    flatten (delChild y tree) = (flatten tree).erase y ∧
      Valid t (t - 1) h (delChild y tree)

private theorem delList_spec [LinearOrder α] {t h : Nat} (ht : 2 ≤ t)
    {delChild : α → BTree α → BTree α} {x : α}
    (hdel : DelChildSpec t h delChild) :
    ∀ {keys : List α} {children : List (BTree α)},
      children.length = keys.length + 1 →
      (∀ child ∈ children, Valid t (t - 1) h child) →
      Ordered (.node keys children) →
      keys ≠ [] →
      ∀ p, p = delList delChild t x keys children →
        p.2.length = p.1.length + 1 ∧ keys.length - 1 ≤ p.1.length ∧
          p.1.length ≤ keys.length ∧
          (∀ child ∈ p.2, Valid t (t - 1) h child) ∧
          flatten (.node p.1 p.2) = (flatten (.node keys children)).erase x := by
  intro keys
  induction keys with
  | nil =>
      intro children _ _ _ hne p _
      exact absurd rfl hne
  | cons key keys ih =>
      intro children hlen hvalid hOrd _ p hp
      cases children with
      | nil => simp at hlen
      | cons child children =>
          have hlen' : children.length = keys.length + 1 := by simpa using hlen
          have hvChild : Valid t (t - 1) h child := hvalid child (by simp)
          have hvTail : ∀ c ∈ children, Valid t (t - 1) h c :=
            fun c hc => hvalid c (List.mem_cons_of_mem child hc)
          obtain ⟨hpChild, hltB, hgtB, hOrdTail⟩ := ordered_node_cons_parts hOrd
          have hOrdChild : Ordered child := ordered_child_of_node (by simp) hOrd
          have hgeChild : t - 1 ≤ keyCount child :=
            keyCount_ge_of_valid hvChild
          by_cases h1 : x < key
          · by_cases hEns : t ≤ keyCount child
            · have hspec := hdel child (valid_of_keyCount hvChild hEns)
                hOrdChild x
              have e : delList delChild t x (key :: keys) (child :: children) =
                  (key :: keys, delChild x child :: children) := by
                simp [delList, h1, hEns]
              rw [e] at hp
              subst hp
              have hnot : x ∉ key :: flatten (.node keys children) := by
                intro hx
                rw [List.mem_cons] at hx
                rcases hx with hx | hx
                · exact ne_of_lt h1 hx
                · exact lt_asymm h1 (hgtB x hx)
              refine ⟨?_, ?_, ?_, ?_, ?_⟩
              · show (delChild x child :: children).length =
                  (key :: keys).length + 1
                simp only [List.length_cons]
                omega
              · simp only [List.length_cons]; omega
              · simp only [List.length_cons]; omega
              · intro c hc
                change c ∈ delChild x child :: children at hc
                rw [List.mem_cons] at hc
                rcases hc with rfl | hc
                · exact hspec.2
                · exact hvTail c hc
              · simp only [flatten_node_cons]
                rw [hspec.1]
                exact (erase_append_of_not_mem_right hnot).symm
            · have hkcEq : keyCount child = t - 1 := by omega
              cases children with
              | nil => simp at hlen'
              | cons sib rest =>
                  have hlen'' : rest.length = keys.length := by simpa using hlen'
                  have hvSib : Valid t (t - 1) h sib := hvTail sib (by simp)
                  have hvRest : ∀ c ∈ rest, Valid t (t - 1) h c :=
                    fun c hc => hvTail c (List.mem_cons_of_mem sib hc)
                  have hOrdSib : Ordered sib :=
                    ordered_child_of_node (by simp) hOrd
                  obtain ⟨T, hT⟩ := exists_flatten_tail hlen''
                  have hflatOrig : flatten
                      (.node (key :: keys) (child :: sib :: rest)) =
                      flatten child ++ key :: (flatten sib ++ T) := by
                    rw [flatten_node_cons, hT sib]
                  have hpSeg : (flatten child ++
                      key :: (flatten sib ++ T)).Pairwise (· < ·) := by
                    have hp : (flatten
                        (.node (key :: keys) (child :: sib :: rest))).Pairwise
                        (· < ·) := hOrd
                    rwa [hflatOrig] at hp
                  have hsegEq : flatten child ++ key :: (flatten sib ++ T) =
                      (flatten child ++ key :: flatten sib) ++ T := by
                    simp [List.append_assoc]
                  have hpSeg2 : (flatten child ++
                      key :: flatten sib).Pairwise (· < ·) := by
                    rw [hsegEq] at hpSeg
                    exact (List.pairwise_append.mp hpSeg).1
                  have hgtSib : ∀ y ∈ flatten sib, key < y :=
                    fun y hy => hgtB y (by
                      rw [hT sib]
                      exact List.mem_append_left T hy)
                  have hgtT : ∀ y ∈ T, key < y :=
                    fun y hy => hgtB y (by
                      rw [hT sib]
                      exact List.mem_append_right _ hy)
                  have hgeSib : t - 1 ≤ keyCount sib :=
                    keyCount_ge_of_valid hvSib
                  by_cases hSib : t ≤ keyCount sib
                  · obtain ⟨child', sep', sib', hb⟩ :
                        ∃ a b c, borrowRight child key sib = (a, b, c) :=
                      ⟨_, _, _, rfl⟩
                    have e : delList delChild t x (key :: keys)
                        (child :: sib :: rest) =
                        (sep' :: keys, delChild x child' :: sib' :: rest) := by
                      simp [delList, h1, hEns, hSib, hb]
                    have hbValid := borrowRight_valid (sep := key) ht hvChild hvSib hkcEq hSib
                    rw [hb] at hbValid
                    have hbFlat : flatten child' ++ sep' :: flatten sib' =
                        flatten child ++ key :: flatten sib := by
                      have hh := flatten_borrowRight (sep := key) ht hvChild hvSib hkcEq hSib
                      rwa [hb] at hh
                    have hpBorrow : (flatten child' ++
                        sep' :: flatten sib').Pairwise (· < ·) := by
                      rwa [← hbFlat] at hpSeg2
                    have hOrdChild' : Ordered child' :=
                      (List.pairwise_append.mp hpBorrow).1
                    have hspec := hdel child' hbValid.1 hOrdChild' x
                    have hsepMem : sep' ∈ flatten sib := by
                      have hh := borrowRight_sep_mem (sep := key) ht hvChild hvSib hSib
                      rwa [hb] at hh
                    have hsib'Mem : ∀ y ∈ flatten sib', y ∈ flatten sib := by
                      intro y hy
                      have hy2 : y ∈ flatten (borrowRight child key sib).2.2 := by
                        rw [hb]
                        exact hy
                      exact borrowRight_sib'_mem (sep := key) ht hvChild hvSib hSib hy2
                    have hxNotSeg : x ∉ sep' :: flatten sib' := by
                      intro hx
                      rw [List.mem_cons] at hx
                      rcases hx with hx | hx
                      · have hksep : key < sep' := hgtSib sep' hsepMem
                        subst hx
                        exact lt_asymm h1 hksep
                      · exact lt_asymm h1 (hgtSib x (hsib'Mem x hx))
                    have hxNotKeySeg : x ∉ key :: flatten sib := by
                      intro hx
                      rw [List.mem_cons] at hx
                      rcases hx with hx | hx
                      · exact ne_of_lt h1 hx
                      · exact lt_asymm h1 (hgtSib x hx)
                    have hxNotRest : x ∉ key :: (flatten sib ++ T) := by
                      intro hx
                      rw [List.mem_cons] at hx
                      rcases hx with hx | hx
                      · exact ne_of_lt h1 hx
                      · rw [List.mem_append] at hx
                        rcases hx with hx | hx
                        · exact lt_asymm h1 (hgtSib x hx)
                        · exact lt_asymm h1 (hgtT x hx)
                    rw [e] at hp
                    subst hp
                    refine ⟨?_, ?_, ?_, ?_, ?_⟩
                    · simp only [List.length_cons]; omega
                    · simp only [List.length_cons]; omega
                    · simp only [List.length_cons]; omega
                    · intro c hc
                      change c ∈ delChild x child' :: sib' :: rest at hc
                      rw [List.mem_cons] at hc
                      rcases hc with rfl | hc
                      · exact hspec.2
                      · rw [List.mem_cons] at hc
                        rcases hc with rfl | hc
                        · exact hbValid.2
                        · exact hvRest c hc
                    · rw [flatten_node_cons, hT sib', hspec.1, hflatOrig,
                        erase_append_of_not_mem_right hxNotRest]
                      have step1 : (flatten child').erase x ++
                          sep' :: (flatten sib' ++ T) =
                          ((flatten child' ++ sep' :: flatten sib').erase x) ++
                            T := by
                        rw [erase_append_of_not_mem_right hxNotSeg,
                          List.append_assoc, List.cons_append]
                      rw [step1, hbFlat,
                        erase_append_of_not_mem_right hxNotKeySeg,
                        List.append_assoc, List.cons_append]
                  · have hksEq : keyCount sib = t - 1 := by omega
                    have e : delList delChild t x (key :: keys)
                        (child :: sib :: rest) =
                        (keys, delChild x (merge key child sib) :: rest) := by
                      simp [delList, h1, hEns, hSib]
                    have hvMerge : Valid t t h (merge key child sib) :=
                      merge_valid ht hvChild hvSib (by omega) (by omega)
                    have hfMerge : flatten (merge key child sib) =
                        flatten child ++ key :: flatten sib :=
                      flatten_merge_eq hvChild hvSib
                    have hOrdMerge : Ordered (merge key child sib) := by
                      change (flatten (merge key child sib)).Pairwise (· < ·)
                      rw [hfMerge]
                      exact hpSeg2
                    have hspec := hdel (merge key child sib) hvMerge hOrdMerge x
                    have hxNotKeySeg : x ∉ key :: flatten sib := by
                      intro hx
                      rw [List.mem_cons] at hx
                      rcases hx with hx | hx
                      · exact ne_of_lt h1 hx
                      · exact lt_asymm h1 (hgtSib x hx)
                    have hxNotRest : x ∉ key :: (flatten sib ++ T) := by
                      intro hx
                      rw [List.mem_cons] at hx
                      rcases hx with hx | hx
                      · exact ne_of_lt h1 hx
                      · rw [List.mem_append] at hx
                        rcases hx with hx | hx
                        · exact lt_asymm h1 (hgtSib x hx)
                        · exact lt_asymm h1 (hgtT x hx)
                    rw [e] at hp
                    subst hp
                    refine ⟨?_, ?_, ?_, ?_, ?_⟩
                    · simp only [List.length_cons]; omega
                    · simp only [List.length_cons]; omega
                    · simp only [List.length_cons]; omega
                    · intro c hc
                      change c ∈ delChild x (merge key child sib) :: rest at hc
                      rw [List.mem_cons] at hc
                      rcases hc with rfl | hc
                      · exact hspec.2
                      · exact hvRest c hc
                    · rw [hT (delChild x (merge key child sib)), hspec.1,
                        hfMerge, hflatOrig,
                        erase_append_of_not_mem_right hxNotRest,
                        erase_append_of_not_mem_right hxNotKeySeg,
                        List.append_assoc, List.cons_append]
          · by_cases hgt : key < x
            · cases keys with
              | nil =>
                  cases children with
                  | nil => simp at hlen'
                  | cons last rest =>
                      cases rest with
                      | cons _ _ => simp at hlen'
                      | nil =>
                          have hvLast : Valid t (t - 1) h last :=
                            hvTail last (by simp)
                          have hOrdLast : Ordered last :=
                            ordered_child_of_node (by simp) hOrd
                          have hgeLast : t - 1 ≤ keyCount last :=
                            keyCount_ge_of_valid hvLast
                          have hgtLast : ∀ y ∈ flatten last, key < y := by
                            intro y hy
                            apply hgtB
                            have hfl : flatten (.node [] [last] : BTree α) =
                                flatten last := flatten_node_nil
                            rwa [hfl]
                          by_cases hEns : t ≤ keyCount last
                          · have hspec := hdel last
                                (valid_of_keyCount hvLast hEns) hOrdLast x
                            have e : delList delChild t x (key :: []) (child :: [last]) =
                                ([key], [child, delChild x last]) := by
                              simp [delList, h1, hgt, hEns]
                            have hxChild : x ∉ flatten child := by
                              intro hx
                              exact lt_asymm hgt (hltB x hx)
                            rw [e] at hp
                            subst hp
                            refine ⟨?_, ?_, ?_, ?_, ?_⟩
                            · simp
                            · simp
                            · simp
                            · intro c hc
                              change c ∈ [child, delChild x last] at hc
                              rw [List.mem_cons] at hc
                              rcases hc with rfl | hc
                              · exact hvChild
                              · rw [List.mem_singleton] at hc
                                rw [hc]
                                exact hspec.2
                            · simp only [flatten_node_pair]
                              rw [hspec.1,
                                erase_append_of_not_mem_left hxChild,
                                erase_cons_tail_of_ne (ne_of_lt hgt)]
                          · have hkLastEq : keyCount last = t - 1 := by omega
                            by_cases hSib : t ≤ keyCount child
                            · obtain ⟨l', sep', r', hbL⟩ :
                                  ∃ a b c, borrowLeft child key last = (a, b, c) :=
                                ⟨_, _, _, rfl⟩
                              have e : delList delChild t x (key :: [])
                                  (child :: [last]) =
                                  ([sep'], [l', delChild x r']) := by
                                simp [delList, h1, hgt, hEns, hSib, hbL]
                              have hbValid := borrowLeft_valid (sep := key) ht hvChild hvLast
                                hSib hkLastEq
                              rw [hbL] at hbValid
                              have hbFlat : flatten l' ++ sep' :: flatten r' =
                                  flatten child ++ key :: flatten last := by
                                have hh := flatten_borrowLeft (sep := key) ht hvChild hvLast
                                  hSib hkLastEq
                                rwa [hbL] at hh
                              have hpOrig : (flatten child ++
                                  key :: flatten last).Pairwise (· < ·) := by
                                have hp : (flatten
                                    (.node [key] [child, last])).Pairwise
                                    (· < ·) := hOrd
                                rwa [flatten_node_pair] at hp
                              have hpBorrow : (flatten l' ++
                                  sep' :: flatten r').Pairwise (· < ·) := by
                                rwa [← hbFlat] at hpOrig
                              have hOrdR' : Ordered r' := by
                                have h2 := (List.pairwise_append.mp hpBorrow).2.1
                                exact (List.pairwise_cons.mp h2).2
                              have hspec := hdel r' hbValid.2 hOrdR' x
                              have hsepMem : sep' ∈ flatten child := by
                                have hh := borrowLeft_sep_mem (sep := key) ht hvChild hvLast hSib
                                rwa [hbL] at hh
                              have hxNotL' : x ∉ flatten l' := by
                                intro hx
                                have hx2 : x ∈ flatten (borrowLeft child key last).1 := by
                                  rw [hbL]
                                  exact hx
                                have hx3 := borrowLeft_sib'_mem (sep := key) ht hvChild hvLast
                                  hSib hx2
                                exact lt_asymm hgt (hltB x hx3)
                              have hsepNe : sep' ≠ x :=
                                ne_of_lt (lt_trans (hltB sep' hsepMem) hgt)
                              have hxChild : x ∉ flatten child := by
                                intro hx
                                exact lt_asymm hgt (hltB x hx)
                              rw [e] at hp
                              subst hp
                              refine ⟨?_, ?_, ?_, ?_, ?_⟩
                              · simp
                              · simp
                              · simp
                              · intro c hc
                                change c ∈ [l', delChild x r'] at hc
                                rw [List.mem_cons] at hc
                                rcases hc with rfl | hc
                                · exact hbValid.1
                                · rw [List.mem_singleton] at hc
                                  rw [hc]
                                  exact hspec.2
                              · simp only [flatten_node_pair]
                                rw [hspec.1]
                                have step1 : flatten l' ++
                                    sep' :: (flatten r').erase x =
                                    (flatten child ++ key :: flatten last).erase x := by
                                  rw [← hbFlat,
                                    erase_append_of_not_mem_left hxNotL',
                                    erase_cons_tail_of_ne hsepNe]
                                rw [step1,
                                  erase_append_of_not_mem_left hxChild,
                                  erase_cons_tail_of_ne (ne_of_lt hgt)]
                            · have hkChildEq : keyCount child = t - 1 := by omega
                              have e : delList delChild t x (key :: [])
                                  (child :: [last]) =
                                  ([], [delChild x (merge key child last)]) := by
                                simp [delList, h1, hgt, hEns, hSib]
                              have hvMerge : Valid t t h (merge key child last) :=
                                merge_valid ht hvChild hvLast (by omega)
                                  (by omega)
                              have hfMerge : flatten (merge key child last) =
                                  flatten child ++ key :: flatten last :=
                                flatten_merge_eq hvChild hvLast
                              have hpOrig : (flatten child ++
                                  key :: flatten last).Pairwise (· < ·) := by
                                have hp : (flatten
                                    (.node [key] [child, last])).Pairwise
                                    (· < ·) := hOrd
                                rwa [flatten_node_pair] at hp
                              have hOrdMerge : Ordered (merge key child last) := by
                                change (flatten (merge key child last)).Pairwise
                                  (· < ·)
                                rw [hfMerge]
                                exact hpOrig
                              have hspec := hdel (merge key child last) hvMerge
                                hOrdMerge x
                              rw [e] at hp
                              subst hp
                              refine ⟨?_, ?_, ?_, ?_, ?_⟩
                              · simp
                              · simp
                              · simp
                              · intro c hc
                                change c ∈ [delChild x (merge key child last)] at hc
                                rw [List.mem_singleton] at hc
                                rw [hc]
                                exact hspec.2
                              · rw [flatten_node_nil, hspec.1, hfMerge,
                                  flatten_node_pair]
              | cons k2 ks2 =>
                  cases hq : delList delChild t x (k2 :: ks2) children with
                  | mk qk qc =>
                      have hqspec := ih hlen' hvTail hOrdTail (by simp) (qk, qc)
                        hq.symm
                      obtain ⟨hqLen, hqGe, hqLe, hqValid, hqFlat⟩ := hqspec
                      have hqLen' : qc.length = qk.length + 1 := hqLen
                      have hqGe' : (k2 :: ks2).length - 1 ≤ qk.length := hqGe
                      have hqLe' : qk.length ≤ (k2 :: ks2).length := hqLe
                      have hlenK2 : (k2 :: ks2).length = ks2.length + 1 := rfl
                      have hlenKey : (key :: k2 :: ks2).length =
                          (k2 :: ks2).length + 1 := rfl
                      have e : delList delChild t x (key :: k2 :: ks2)
                          (child :: children) = (key :: qk, child :: qc) := by
                        simp [delList, h1, hgt, hq]
                      have hxChild : x ∉ flatten child := by
                        intro hx
                        exact lt_asymm hgt (hltB x hx)
                      rw [e] at hp
                      subst hp
                      refine ⟨?_, ?_, ?_, ?_, ?_⟩
                      · simp only [List.length_cons]; omega
                      · simp only [List.length_cons]; omega
                      · simp only [List.length_cons]; omega
                      · intro c hc
                        change c ∈ child :: qc at hc
                        rw [List.mem_cons] at hc
                        rcases hc with rfl | hc
                        · exact hvChild
                        · exact hqValid c hc
                      · simp only [flatten_node_cons]
                        rw [hqFlat, erase_append_of_not_mem_left hxChild,
                          erase_cons_tail_of_ne (ne_of_lt hgt)]
            · have hxEq : key = x :=
                (le_antisymm (le_of_not_gt hgt) (le_of_not_gt h1)).symm
              subst hxEq
              cases children with
              | nil => simp at hlen'
              | cons rchild rest =>
                  have hlen'' : rest.length = keys.length := by simpa using hlen'
                  have hvR : Valid t (t - 1) h rchild := hvTail rchild (by simp)
                  have hvRest : ∀ c ∈ rest, Valid t (t - 1) h c :=
                    fun c hc => hvTail c (List.mem_cons_of_mem rchild hc)
                  have hOrdR : Ordered rchild :=
                    ordered_child_of_node (by simp) hOrd
                  obtain ⟨T, hT⟩ := exists_flatten_tail hlen''
                  have hflatOrig : flatten
                      (.node (key :: keys) (child :: rchild :: rest)) =
                      flatten child ++ key :: (flatten rchild ++ T) := by
                    rw [flatten_node_cons, hT rchild]
                  have hpSeg : (flatten child ++
                      key :: (flatten rchild ++ T)).Pairwise (· < ·) := by
                    have hp : (flatten
                        (.node (key :: keys) (child :: rchild :: rest))).Pairwise
                        (· < ·) := hOrd
                    rwa [hflatOrig] at hp
                  have hsegEq : flatten child ++ key :: (flatten rchild ++ T) =
                      (flatten child ++ key :: flatten rchild) ++ T := by
                    simp [List.append_assoc]
                  have hpSeg2 : (flatten child ++
                      key :: flatten rchild).Pairwise (· < ·) := by
                    rw [hsegEq] at hpSeg
                    exact (List.pairwise_append.mp hpSeg).1
                  have hgeR : t - 1 ≤ keyCount rchild :=
                    keyCount_ge_of_valid hvR
                  have hkeyNotLeft : key ∉ flatten child := by
                    intro hx
                    exact lt_irrefl key (hltB key hx)
                  by_cases hEnsL : t ≤ keyCount child
                  · obtain ⟨init, pp, hmk, hsplitEq⟩ :=
                      exists_maxKey_flatten ht h hvChild (by omega)
                    have e : delList delChild t key (key :: keys)
                        (child :: rchild :: rest) =
                        (pp :: keys, delChild pp child :: rchild :: rest) := by
                      simp [delList, h1, hEnsL, hmk]
                    have hspec := hdel child (valid_of_keyCount hvChild hEnsL)
                      hOrdChild pp
                    have hpNotInit : pp ∉ init := by
                      intro hpp
                      have hp2 : (init ++ [pp]).Pairwise (· < ·) := by
                        rw [← hsplitEq]
                        exact hpChild
                      have hltpp := (List.pairwise_append.mp hp2).2.2 pp hpp pp
                        (by simp)
                      exact lt_irrefl pp hltpp
                    have hEraseP : (flatten child).erase pp = init := by
                      rw [hsplitEq, erase_append_of_not_mem_left hpNotInit]
                      simp [List.erase_cons_head]
                    rw [e] at hp
                    subst hp
                    refine ⟨?_, ?_, ?_, ?_, ?_⟩
                    · simp only [List.length_cons]; omega
                    · simp only [List.length_cons]; omega
                    · simp only [List.length_cons]; omega
                    · intro c hc
                      change c ∈ delChild pp child :: rchild :: rest at hc
                      rw [List.mem_cons] at hc
                      rcases hc with rfl | hc
                      · exact hspec.2
                      · rw [List.mem_cons] at hc
                        rcases hc with rfl | hc
                        · exact hvR
                        · exact hvRest c hc
                    · rw [flatten_node_cons, hT rchild, hspec.1, hEraseP,
                        hflatOrig, erase_append_of_not_mem_left hkeyNotLeft,
                        List.erase_cons_head, hsplitEq]
                      simp [List.append_assoc]
                  · have hkcEq : keyCount child = t - 1 := by omega
                    by_cases hEnsR : t ≤ keyCount rchild
                    · obtain ⟨s, restF, hmk, hfr⟩ :=
                        exists_minKey_flatten ht h hvR (by omega)
                      have e : delList delChild t key (key :: keys)
                          (child :: rchild :: rest) =
                          (s :: keys, child :: delChild s rchild :: rest) := by
                        simp [delList, h1, hEnsL, hEnsR, hmk]
                      have hspec := hdel rchild
                        (valid_of_keyCount hvR hEnsR) hOrdR s
                      have hEraseS : (flatten rchild).erase s = restF := by
                        rw [hfr, List.erase_cons_head]
                      rw [e] at hp
                      subst hp
                      refine ⟨?_, ?_, ?_, ?_, ?_⟩
                      · simp only [List.length_cons]; omega
                      · simp only [List.length_cons]; omega
                      · simp only [List.length_cons]; omega
                      · intro c hc
                        change c ∈ child :: delChild s rchild :: rest at hc
                        rw [List.mem_cons] at hc
                        rcases hc with rfl | hc
                        · exact hvChild
                        · rw [List.mem_cons] at hc
                          rcases hc with rfl | hc
                          · exact hspec.2
                          · exact hvRest c hc
                      · rw [flatten_node_cons, hT (delChild s rchild),
                          hspec.1, hEraseS, hflatOrig,
                          erase_append_of_not_mem_left hkeyNotLeft,
                          List.erase_cons_head, hfr, List.cons_append]
                    · have hkREq : keyCount rchild = t - 1 := by omega
                      have e : delList delChild t key (key :: keys)
                          (child :: rchild :: rest) =
                          (keys, delChild key (merge key child rchild) ::
                            rest) := by
                        simp [delList, h1, hEnsL, hEnsR]
                      have hvMerge : Valid t t h (merge key child rchild) :=
                        merge_valid ht hvChild hvR (by omega) (by omega)
                      have hfMerge : flatten (merge key child rchild) =
                          flatten child ++ key :: flatten rchild :=
                        flatten_merge_eq hvChild hvR
                      have hOrdMerge : Ordered (merge key child rchild) := by
                        change (flatten (merge key child rchild)).Pairwise (· < ·)
                        rw [hfMerge]
                        exact hpSeg2
                      have hspec := hdel (merge key child rchild) hvMerge
                        hOrdMerge key
                      rw [e] at hp
                      subst hp
                      refine ⟨?_, ?_, ?_, ?_, ?_⟩
                      · simp only [List.length_cons]; omega
                      · simp only [List.length_cons]; omega
                      · simp only [List.length_cons]; omega
                      · intro c hc
                        change c ∈ delChild key (merge key child rchild) ::
                          rest at hc
                        rw [List.mem_cons] at hc
                        rcases hc with rfl | hc
                        · exact hspec.2
                        · exact hvRest c hc
                      · rw [hT (delChild key (merge key child rchild)),
                          hspec.1, hfMerge,
                          erase_append_of_not_mem_left hkeyNotLeft,
                          List.erase_cons_head, hflatOrig,
                          erase_append_of_not_mem_left hkeyNotLeft,
                          List.erase_cons_head]
                        simp [List.append_assoc]

private theorem delH_spec [LinearOrder α] {t : Nat} (ht : 2 ≤ t) (h : Nat) :
    ∀ {mink : Nat} {tree : BTree α}, Valid t mink h tree → Ordered tree →
      (∀ ks cs, tree = .node ks cs → 1 ≤ mink) → ∀ (x : α),
      flatten (delH h t x tree) = (flatten tree).erase x ∧
        Valid t (mink - 1) h (delH h t x tree) := by
  induction h with
  | zero =>
      intro mink tree hv _ _ x
      cases tree with
      | node _ _ => cases hv
      | leaf keys =>
          cases hv with
          | leaf hlo hhi =>
              have e : delH 0 t x (.leaf keys) = .leaf (keys.erase x) := by
                simp [delH]
              have hle : (keys.erase x).length ≤ keys.length :=
                List.erase_sublist.length_le
              have hge : keys.length - 1 ≤ (keys.erase x).length := by
                by_cases hm : x ∈ keys
                · have hhh := List.length_erase_of_mem hm
                  omega
                · have hhh : (keys.erase x).length = keys.length := by
                    rw [List.erase_of_not_mem hm]
                  omega
              rw [e]
              refine ⟨by simp, Valid.leaf ?_ ?_⟩ <;> omega
  | succ h ih =>
      intro mink tree hv hOrd hmink x
      cases tree with
      | leaf _ => cases hv
      | node keys children =>
          cases hv with
          | node hlo hhi hlen hch =>
              have hm1 : 1 ≤ mink := hmink keys children rfl
              have hdel : DelChildSpec t h (delH (α := α) h t) := by
                intro tr hvtr hOrdtr y
                exact ih hvtr hOrdtr (fun _ _ _ => by omega) y
              have hkeys : keys ≠ [] := by
                intro hk
                rw [hk] at hlo
                simp at hlo
                omega
              cases hq : delList (delH h t) t x keys children with
              | mk ks' cs' =>
                  have hspec := delList_spec ht hdel hlen hch hOrd hkeys
                    (ks', cs') hq.symm
                  obtain ⟨hlen', hge, hle, hch', hflat⟩ := hspec
                  have hlen'' : cs'.length = ks'.length + 1 := hlen'
                  have hge' : keys.length - 1 ≤ ks'.length := hge
                  have hle' : ks'.length ≤ keys.length := hle
                  have e : delH (h + 1) t x (.node keys children) =
                      .node ks' cs' := by
                    simp [delH, hq]
                  rw [e]
                  refine ⟨hflat, Valid.node ?_ ?_ hlen'' hch'⟩ <;> omega

private theorem delete_eq [LinearOrder α] {t : Nat} {x : α} {tree : BTree α}
    {res : BTree α} (h : delH (treeHeight tree) t x tree = res) :
    delete t x tree =
      (match res with
       | .node [] [c] => c
       | other => other) := by
  cases res with
  | leaf ks => simp [delete, h]
  | node keys children =>
      cases keys with
      | cons _ _ => simp [delete, h]
      | nil =>
          cases children with
          | nil => simp [delete, h]
          | cons c cs =>
              cases cs with
              | cons _ _ => simp [delete, h]
              | nil => simp [delete, h]

private theorem flatten_delete_delH [LinearOrder α] {t : Nat} {x : α}
    {tree : BTree α} :
    flatten (delete t x tree) =
      flatten (delH (treeHeight tree) t x tree) := by
  cases hdel : delH (treeHeight tree) t x tree with
  | leaf ks =>
      have e : delete t x tree = .leaf ks := delete_eq hdel
      rw [e]
  | node keys children =>
      cases keys with
      | cons k ks =>
          have e : delete t x tree = .node (k :: ks) children :=
            delete_eq hdel
          rw [e]
      | nil =>
          cases children with
          | nil =>
              have e : delete t x tree = .node [] ([] : List (BTree α)) :=
                delete_eq hdel
              rw [e]
          | cons c cs =>
              cases cs with
              | cons _ _ =>
                  have e : delete t x tree =
                      .node [] (c :: _ :: _) := delete_eq hdel
                  rw [e]
              | nil =>
                  have e : delete t x tree = c := delete_eq hdel
                  rw [e]
                  exact flatten_node_nil.symm

/-- The flattening of a deletion from a B-tree is the erasure of the key
from the flattening of the original tree. -/
public theorem flatten_delete [LinearOrder α] {t : Nat} (ht : 2 ≤ t) {x : α}
    {tree : BTree α} (h : IsBTree t tree) :
    flatten (delete t x tree) = (flatten tree).erase x := by
  obtain ⟨-, hOrd, height, hroot⟩ := h
  have hheight : treeHeight tree = height := treeHeight_of_validRoot hroot
  rw [flatten_delete_delH]
  cases hroot with
  | @leaf keys hhi =>
      exact (delH_spec ht (treeHeight (.leaf keys))
        (Valid.leaf (Nat.zero_le _) hhi) hOrd (fun _ _ hEq => by cases hEq) x).1
  | @node height keys children hlo hhi hlen hch =>
      have hv' : Valid t 1 (treeHeight (.node keys children))
          (.node keys children) := by
        rw [hheight]
        exact Valid.node hlo hhi hlen hch
      exact (delH_spec ht _ hv' hOrd (fun _ _ _ => by omega) x).1

/-- The result of a deletion from a root-valid tree is root-valid at the
same height, or one less when a root merge collapsed the root. -/
public theorem delete_validRoot [LinearOrder α] {t height : Nat} (ht : 2 ≤ t)
    {x : α} {tree : BTree α} (hOrd : Ordered tree)
    (hv : ValidRoot t height tree) :
    ValidRoot t height (delete t x tree) ∨
      ValidRoot t (height - 1) (delete t x tree) := by
  have hheight : treeHeight tree = height := treeHeight_of_validRoot hv
  cases hv with
  | @leaf keys hhi =>
      have hv' : Valid t 0 (treeHeight (.leaf keys)) (.leaf keys) :=
        Valid.leaf (Nat.zero_le _) hhi
      have hspec := delH_spec ht (treeHeight (.leaf keys)) hv' hOrd
        (fun _ _ hEq => by cases hEq) x
      cases hdel : delH (treeHeight (.leaf keys)) t x (.leaf keys) with
      | leaf ksr =>
          have hvRes := hspec.2
          rw [hdel, show treeHeight (.leaf keys : BTree α) = 0 from rfl] at hvRes
          cases hvRes with
          | leaf _ hhi' =>
              have eDB : delete t x (.leaf keys) = .leaf ksr :=
                delete_eq hdel
              refine Or.inl ?_
              rw [eDB]
              exact ValidRoot.leaf hhi'
      | node _ _ =>
          have hvRes := hspec.2
          rw [hdel, show treeHeight (.leaf keys : BTree α) = 0 from rfl] at hvRes
          cases hvRes
  | @node height keys children hlo hhi hlen hch =>
      have hv' : Valid t 1 (treeHeight (.node keys children))
          (.node keys children) := by
        rw [hheight]
        exact Valid.node hlo hhi hlen hch
      have hspec := delH_spec ht _ hv' hOrd (fun _ _ _ => by omega) x
      cases hdel : delH (treeHeight (.node keys children)) t x
          (.node keys children) with
      | leaf ks =>
          have hvRes := hspec.2
          rw [hdel, hheight] at hvRes
          cases hvRes
      | node ks' cs' =>
          have hvRes := hspec.2
          rw [hdel, hheight] at hvRes
          cases hvRes with
          | node hlo' hhi' hlen' hch' =>
              cases ks' with
              | cons k ks'' =>
                  have eDB : delete t x (.node keys children) =
                      .node (k :: ks'') cs' := delete_eq hdel
                  refine Or.inl ?_
                  rw [eDB]
                  exact ValidRoot.node (by simp) hhi' hlen' hch'
              | nil =>
                  cases cs' with
                  | nil => simp at hlen'
                  | cons child cs'' =>
                      cases cs'' with
                      | cons _ _ =>
                          simp only [List.length_cons, List.length_nil] at hlen'
                          omega
                      | nil =>
                          have eDB : delete t x (.node keys children) =
                              child := delete_eq hdel
                          have hvChild : Valid t (t - 1) height child :=
                            hch' child (by simp)
                          refine Or.inr ?_
                          rw [eDB]
                          cases hvChild with
                          | leaf _ hhi1 => exact ValidRoot.leaf hhi1
                          | node hlo1 hhi1 hlen1 hch1 =>
                              refine ValidRoot.node ?_ hhi1 hlen1 hch1
                              omega

/-- The result of a deletion from a B-tree is a B-tree. -/
public theorem IsBTree.delete [LinearOrder α] {t : Nat} (ht : 2 ≤ t) {x : α}
    {tree : BTree α} (h : IsBTree t tree) : IsBTree t (delete t x tree) := by
  obtain ⟨-, hOrd, height, hroot⟩ := h
  refine ⟨ht, ?_, ?_⟩
  · simp only [Ordered]
    rw [flatten_delete ht ⟨ht, hOrd, height, hroot⟩]
    have hp : (flatten tree).Pairwise (· < ·) := hOrd
    exact hp.sublist List.erase_sublist
  · rcases delete_validRoot ht hOrd hroot with hv | hv
    · exact ⟨height, hv⟩
    · exact ⟨height - 1, hv⟩

/-- Deletion preserves orderedness of the result. -/
public theorem ordered_delete [LinearOrder α] {t : Nat} (ht : 2 ≤ t) {x : α}
    {tree : BTree α} (h : IsBTree t tree) : Ordered (delete t x tree) :=
  (IsBTree.delete ht h).ordered

/-- The result of a deletion is root-valid at some height: the height of
the input or one less (see `delete_validRoot`). -/
public theorem delete_validRoot_exists [LinearOrder α] {t : Nat} (ht : 2 ≤ t)
    {x : α} {tree : BTree α} (h : IsBTree t tree) :
    ∃ height, ValidRoot t height (delete t x tree) :=
  (IsBTree.delete ht h).exists_validRoot

/-- A key is in the result of a deletion exactly when it was in the
original tree and is not the deleted key. -/
public theorem mem_delete [LinearOrder α] {t : Nat} (ht : 2 ≤ t) {x y : α}
    {tree : BTree α} (h : IsBTree t tree) :
    y ∈ delete t x tree ↔ y ≠ x ∧ y ∈ tree := by
  change y ∈ flatten (delete t x tree) ↔ y ≠ x ∧ y ∈ flatten tree
  rw [flatten_delete ht h]
  constructor
  · intro hy
    refine ⟨fun hyx => ?_, List.mem_of_mem_erase hy⟩
    subst hyx
    exact h.ordered.flatten_nodup.not_mem_erase hy
  · intro hy
    exact (List.mem_erase_of_ne hy.1).mpr hy.2

/-- The deleted key is absent from the result. -/
public theorem not_mem_delete [LinearOrder α] {t : Nat} (ht : 2 ≤ t) {x : α}
    {tree : BTree α} (h : IsBTree t tree) : x ∉ delete t x tree := by
  rw [mem_delete ht h]
  exact fun hcon => hcon.1 rfl

/-- Search in the result of a deletion agrees with membership in the
original tree minus the deleted key. -/
public theorem contains_delete_iff [LinearOrder α] {t : Nat} (ht : 2 ≤ t)
    {x y : α} {tree : BTree α} (h : IsBTree t tree) :
    contains y (delete t x tree) = true ↔ y ≠ x ∧ y ∈ tree := by
  rw [contains_eq_true_iff (IsBTree.delete ht h), mem_delete ht h]

/-- Deleting a key decreases the number of stored keys by one when the key
was present, and leaves it unchanged otherwise. -/
public theorem flatten_length_delete [LinearOrder α] {t : Nat} (ht : 2 ≤ t)
    {x : α} {tree : BTree α} (h : IsBTree t tree) :
    (flatten (delete t x tree)).length =
      if x ∈ flatten tree then (flatten tree).length - 1
      else (flatten tree).length := by
  rw [flatten_delete ht h]
  by_cases hx : x ∈ flatten tree
  · rw [ite_eq_left hx, List.length_erase_of_mem hx]
  · rw [ite_eq_right hx, List.erase_of_not_mem hx]

/-- Deleting the same key twice has the same flattening as deleting it
once. -/
public theorem flatten_delete_delete [LinearOrder α] {t : Nat} (ht : 2 ≤ t)
    {x : α} {tree : BTree α} (h : IsBTree t tree) :
    flatten (delete t x (delete t x tree)) =
      flatten (delete t x tree) := by
  rw [flatten_delete ht (IsBTree.delete ht h), flatten_delete ht h]
  exact List.erase_of_not_mem h.ordered.flatten_nodup.not_mem_erase

end BTree

end Cslib.Algorithms.Lean
