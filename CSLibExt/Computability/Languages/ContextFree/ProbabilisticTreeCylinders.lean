/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.ContextFree.BinaryTreeAddressLaw
public import CSLibExt.Computability.Languages.ContextFree.Probabilistic

/-!
# Finite-tree cylinders

Each finite tree determines its exact branch and leaf addresses. Its
cylinder in the binary address law fixes exactly those active
addresses (descendants of leaves are unrestricted), its measure is
the existing `p`/`1 - p` tree weight, and distinct finite trees have
disjoint cylinders.
-/

@[expose] public section

namespace Cslib.Language

/-! ## exact branch/leaf addresses of a finite tree

The three address sets are defined by recursion on the existing
trees, carrying the absolute root prefix `u`. No new tree type: the
values are plain `Finset (List Bool)`, the address type of the binary address law. -/

/-- branch (internal-node) addresses of `t` rooted at prefix `u`:
the root of every internal node; leaves contribute none. -/
def CGTree.branchAddresses : CGTree → List Bool → Finset (List Bool)
  | .leaf, _ => ∅
  | .node l r, u =>
      insert u (l.branchAddresses (u ++ [false]) ∪ r.branchAddresses (u ++ [true]))

/-- leaf addresses of `t` rooted at prefix `u`: the root of every
tree leaf; internal nodes contribute none directly. -/
def CGTree.leafAddresses : CGTree → List Bool → Finset (List Bool)
  | .leaf, u => {u}
  | .node l r, u =>
      l.leafAddresses (u ++ [false]) ∪ r.leafAddresses (u ++ [true])

/-- active addresses of `t` rooted at prefix `u`: every node of
the tree. Descendants of leaves (non-empty continuations of a leaf
address) are never active; see `not_mem_activeAddresses_of_leaf`. -/
def CGTree.activeAddresses : CGTree → List Bool → Finset (List Bool)
  | .leaf, u => {u}
  | .node l r, u =>
      insert u (l.activeAddresses (u ++ [false]) ∪ r.activeAddresses (u ++ [true]))

/-- the Bool assignment the tree imposes at prefix `u`: `true`
(branch) exactly on its branch addresses, `false` elsewhere. On the
active set `false` is exactly the leaf addresses
(`branchAssignment_eq_false_of_mem_active`). -/
def CGTree.branchAssignment (t : CGTree) (u : List Bool) : List Bool → Bool :=
  fun a => decide (a ∈ t.branchAddresses u)

/-- the shape of a derivation tree as an existing `CGTree`
(projection, not a new tree type). Address sets of `t` are those of
`t.shape`; see `PDerivTree.addresses_shape`. -/
def PDerivTree.shape {NT T : Type*} : PDerivTree NT T → CGTree
  | .leaf _ _ => .leaf
  | .node _ _ _ l r => .node l.shape r.shape

/-- branch addresses of a derivation tree rooted at prefix `u`:
those of its `CGTree` shape. -/
def PDerivTree.branchAddresses {NT T : Type*} (t : PDerivTree NT T) (u : List Bool) :
    Finset (List Bool) :=
  t.shape.branchAddresses u

/-- leaf addresses of a derivation tree rooted at prefix `u`. -/
def PDerivTree.leafAddresses {NT T : Type*} (t : PDerivTree NT T) (u : List Bool) :
    Finset (List Bool) :=
  t.shape.leafAddresses u

/-- active addresses of a derivation tree rooted at prefix `u`. -/
def PDerivTree.activeAddresses {NT T : Type*} (t : PDerivTree NT T) (u : List Bool) :
    Finset (List Bool) :=
  t.shape.activeAddresses u

/-- the Bool assignment a derivation tree imposes at prefix `u`. -/
def PDerivTree.branchAssignment {NT T : Type*} (t : PDerivTree NT T) (u : List Bool) :
    List Bool → Bool :=
  t.shape.branchAssignment u

/-! ## the cylinder of a finite tree -/

/-- the cylinder of a finite one-nonterminal tree: the
finite-address cylinder of the binary address law on exactly its active
addresses, with its branch assignment. It constrains only active
nodes; every address outside the active set, in particular every
descendant of a leaf, is unrestricted. -/
def treeCylinder (t : CGTree) : Set BinaryTreeAddressLaw.Ω :=
  BinaryTreeAddressLaw.cylinder (t.activeAddresses []) (t.branchAssignment [])

/-- the cylinder of a finite derivation tree: the cylinder of its
shape. Same-shape derivation trees (different labels or terminals)
have the same cylinder; disjointness below is therefore stated for
distinct shapes, not distinct labelled trees. -/
def PDerivTree.treeCylinder {NT T : Type*} (t : PDerivTree NT T) :
    Set BinaryTreeAddressLaw.Ω :=
  Cslib.Language.treeCylinder t.shape

theorem CGTree.branchAddresses_leaf (u : List Bool) :
    CGTree.leaf.branchAddresses u = ∅ := by
  rfl

theorem CGTree.branchAddresses_node (l r : CGTree) (u : List Bool) :
    (CGTree.node l r).branchAddresses u =
      insert u (l.branchAddresses (u ++ [false]) ∪ r.branchAddresses (u ++ [true])) := by
  rfl

theorem CGTree.leafAddresses_leaf (u : List Bool) :
    CGTree.leaf.leafAddresses u = {u} := by
  rfl

theorem CGTree.leafAddresses_node (l r : CGTree) (u : List Bool) :
    (CGTree.node l r).leafAddresses u =
      l.leafAddresses (u ++ [false]) ∪ r.leafAddresses (u ++ [true]) := by
  rfl

theorem CGTree.activeAddresses_leaf (u : List Bool) :
    CGTree.leaf.activeAddresses u = {u} := by
  rfl

theorem CGTree.activeAddresses_node (l r : CGTree) (u : List Bool) :
    (CGTree.node l r).activeAddresses u =
      insert u (l.activeAddresses (u ++ [false]) ∪ r.activeAddresses (u ++ [true])) := by
  rfl

/-- A child-prefix address is never the parent prefix. -/
theorem root_ne_child_append (u : List Bool) (d : Bool) (b : List Bool) :
    u ≠ (u ++ [d]) ++ b := by
  intro h
  have hL := congrArg List.length h
  have hd : ([d]).length = 1 := rfl
  simp only [List.length_append] at hL
  omega

/-- Addresses under different child directions never coincide. -/
theorem left_right_append_ne_of_ne (d₁ d₂ : Bool) (h : d₁ ≠ d₂) (u b₁ b₂ : List Bool) :
    (u ++ [d₁]) ++ b₁ ≠ (u ++ [d₂]) ++ b₂ := by
  intro hcon
  rw [List.append_assoc, List.append_assoc] at hcon
  have h2 := List.append_cancel_left hcon
  simp only [List.cons_append, List.nil_append] at h2
  have hcon2 : d₁ = d₂ ∧ b₁ = b₂ := by simpa using h2
  exact h hcon2.1

/-- Left- and right-subtree addresses never coincide. -/
theorem left_right_append_ne (u b₁ b₂ : List Bool) :
    (u ++ [false]) ++ b₁ ≠ (u ++ [true]) ++ b₂ :=
  left_right_append_ne_of_ne false true (by decide) u b₁ b₂

/-- Branch addresses translate along the root prefix. -/
theorem mem_branchAddresses_iff (t : CGTree) (u a : List Bool) :
    a ∈ t.branchAddresses u ↔ ∃ b ∈ t.branchAddresses [], a = u ++ b := by
  revert u a
  induction t with
  | leaf =>
      intro u a
      simp only [CGTree.branchAddresses_leaf]
      constructor
      · intro h
        exact absurd h (Finset.notMem_empty a)
      · rintro ⟨b, hb, -⟩
        exact absurd hb (Finset.notMem_empty b)
  | node l r ihl ihr =>
      intro u a
      simp only [CGTree.branchAddresses_node, Finset.mem_insert, Finset.mem_union]
      constructor
      · rintro (rfl | hl | hr)
        · exact ⟨[], by simp [CGTree.branchAddresses_node], by simp⟩
        · obtain ⟨c, hc, hac⟩ := (ihl (u ++ [false]) a).mp hl
          refine ⟨[false] ++ c, ?_, by rw [hac, List.append_assoc]⟩
          exact Or.inr (Or.inl ((ihl ([] ++ [false]) ([false] ++ c)).mpr ⟨c, hc, by simp⟩))
        · obtain ⟨c, hc, hac⟩ := (ihr (u ++ [true]) a).mp hr
          refine ⟨[true] ++ c, ?_, by rw [hac, List.append_assoc]⟩
          exact Or.inr (Or.inr ((ihr ([] ++ [true]) ([true] ++ c)).mpr ⟨c, hc, by simp⟩))
      · rintro ⟨b, hb, rfl⟩
        rcases hb with (rfl | hb | hb)
        · exact Or.inl (by simp)
        · obtain ⟨c, hc, hbc⟩ := (ihl ([] ++ [false]) b).mp hb
          exact Or.inr (Or.inl ((ihl (u ++ [false]) (u ++ b)).mpr
            ⟨c, hc, by simp [hbc, List.append_assoc]⟩))
        · obtain ⟨c, hc, hbc⟩ := (ihr ([] ++ [true]) b).mp hb
          exact Or.inr (Or.inr ((ihr (u ++ [true]) (u ++ b)).mpr
            ⟨c, hc, by simp [hbc, List.append_assoc]⟩))

/-- Leaf addresses translate along the root prefix. -/
theorem mem_leafAddresses_iff (t : CGTree) (u a : List Bool) :
    a ∈ t.leafAddresses u ↔ ∃ b ∈ t.leafAddresses [], a = u ++ b := by
  revert u a
  induction t with
  | leaf =>
      intro u a
      simp only [CGTree.leafAddresses_leaf, Finset.mem_singleton]
      constructor
      · intro h
        exact ⟨[], rfl, by simp [h]⟩
      · rintro ⟨b, rfl, ha⟩
        simpa using ha
  | node l r ihl ihr =>
      intro u a
      simp only [CGTree.leafAddresses_node, Finset.mem_union]
      constructor
      · rintro (hl | hr)
        · obtain ⟨c, hc, hac⟩ := (ihl (u ++ [false]) a).mp hl
          refine ⟨[false] ++ c, ?_, by rw [hac, List.append_assoc]⟩
          exact Or.inl ((ihl ([] ++ [false]) ([false] ++ c)).mpr ⟨c, hc, by simp⟩)
        · obtain ⟨c, hc, hac⟩ := (ihr (u ++ [true]) a).mp hr
          refine ⟨[true] ++ c, ?_, by rw [hac, List.append_assoc]⟩
          exact Or.inr ((ihr ([] ++ [true]) ([true] ++ c)).mpr ⟨c, hc, by simp⟩)
      · rintro ⟨b, hb, rfl⟩
        rcases hb with (hb | hb)
        · obtain ⟨c, hc, hbc⟩ := (ihl ([] ++ [false]) b).mp hb
          exact Or.inl ((ihl (u ++ [false]) (u ++ b)).mpr
            ⟨c, hc, by simp [hbc, List.append_assoc]⟩)
        · obtain ⟨c, hc, hbc⟩ := (ihr ([] ++ [true]) b).mp hb
          exact Or.inr ((ihr (u ++ [true]) (u ++ b)).mpr
            ⟨c, hc, by simp [hbc, List.append_assoc]⟩)

/-- Active addresses translate along the root prefix. -/
theorem mem_activeAddresses_iff (t : CGTree) (u a : List Bool) :
    a ∈ t.activeAddresses u ↔ ∃ b ∈ t.activeAddresses [], a = u ++ b := by
  revert u a
  induction t with
  | leaf =>
      intro u a
      simp only [CGTree.activeAddresses_leaf, Finset.mem_singleton]
      constructor
      · intro h
        exact ⟨[], rfl, by simp [h]⟩
      · rintro ⟨b, rfl, ha⟩
        simpa using ha
  | node l r ihl ihr =>
      intro u a
      simp only [CGTree.activeAddresses_node, Finset.mem_insert, Finset.mem_union]
      constructor
      · rintro (rfl | hl | hr)
        · exact ⟨[], by simp [CGTree.activeAddresses_node], by simp⟩
        · obtain ⟨c, hc, hac⟩ := (ihl (u ++ [false]) a).mp hl
          refine ⟨[false] ++ c, ?_, by rw [hac, List.append_assoc]⟩
          exact Or.inr (Or.inl ((ihl ([] ++ [false]) ([false] ++ c)).mpr ⟨c, hc, by simp⟩))
        · obtain ⟨c, hc, hac⟩ := (ihr (u ++ [true]) a).mp hr
          refine ⟨[true] ++ c, ?_, by rw [hac, List.append_assoc]⟩
          exact Or.inr (Or.inr ((ihr ([] ++ [true]) ([true] ++ c)).mpr ⟨c, hc, by simp⟩))
      · rintro ⟨b, hb, rfl⟩
        rcases hb with (rfl | hb | hb)
        · exact Or.inl (by simp)
        · obtain ⟨c, hc, hbc⟩ := (ihl ([] ++ [false]) b).mp hb
          exact Or.inr (Or.inl ((ihl (u ++ [false]) (u ++ b)).mpr
            ⟨c, hc, by simp [hbc, List.append_assoc]⟩))
        · obtain ⟨c, hc, hbc⟩ := (ihr ([] ++ [true]) b).mp hb
          exact Or.inr (Or.inr ((ihr (u ++ [true]) (u ++ b)).mpr
            ⟨c, hc, by simp [hbc, List.append_assoc]⟩))

/-- The parent prefix is never a branch address of a child subtree. -/
theorem not_mem_branch_child (t : CGTree) (u : List Bool) (d : Bool) :
    u ∉ t.branchAddresses (u ++ [d]) := by
  intro h
  obtain ⟨b, -, hb⟩ := (mem_branchAddresses_iff t (u ++ [d]) u).mp h
  exact root_ne_child_append u d b hb

/-- The parent prefix is never a leaf address of a child subtree. -/
theorem not_mem_leaf_child (t : CGTree) (u : List Bool) (d : Bool) :
    u ∉ t.leafAddresses (u ++ [d]) := by
  intro h
  obtain ⟨b, -, hb⟩ := (mem_leafAddresses_iff t (u ++ [d]) u).mp h
  exact root_ne_child_append u d b hb

/-- The parent prefix is never an active address of a child subtree. -/
theorem not_mem_active_child (t : CGTree) (u : List Bool) (d : Bool) :
    u ∉ t.activeAddresses (u ++ [d]) := by
  intro h
  obtain ⟨b, -, hb⟩ := (mem_activeAddresses_iff t (u ++ [d]) u).mp h
  exact root_ne_child_append u d b hb

/-- Active addresses under different child directions are disjoint. -/
theorem disjoint_active_child (l r : CGTree) (u : List Bool) (d₁ d₂ : Bool) (h : d₁ ≠ d₂) :
    Disjoint (l.activeAddresses (u ++ [d₁])) (r.activeAddresses (u ++ [d₂])) := by
  rw [Finset.disjoint_left]
  intro a ha1 ha2
  obtain ⟨b₁, -, hb₁⟩ := (mem_activeAddresses_iff l (u ++ [d₁]) a).mp ha1
  obtain ⟨b₂, -, hb₂⟩ := (mem_activeAddresses_iff r (u ++ [d₂]) a).mp ha2
  exact left_right_append_ne_of_ne d₁ d₂ h u b₁ b₂ (hb₁.symm.trans hb₂)

/-- Branch addresses under one direction are disjoint from leaf addresses under another. -/
theorem disjoint_branch_leaf (l r : CGTree) (u : List Bool) (d₁ d₂ : Bool) (h : d₁ ≠ d₂) :
    Disjoint (l.branchAddresses (u ++ [d₁])) (r.leafAddresses (u ++ [d₂])) := by
  rw [Finset.disjoint_left]
  intro a ha1 ha2
  obtain ⟨b₁, -, hb₁⟩ := (mem_branchAddresses_iff l (u ++ [d₁]) a).mp ha1
  obtain ⟨b₂, -, hb₂⟩ := (mem_leafAddresses_iff r (u ++ [d₂]) a).mp ha2
  exact left_right_append_ne_of_ne d₁ d₂ h u b₁ b₂ (hb₁.symm.trans hb₂)

/-- Active addresses under one direction are disjoint from branch addresses under another. -/
theorem disjoint_active_branch (l r : CGTree) (u : List Bool) (d₁ d₂ : Bool) (h : d₁ ≠ d₂) :
    Disjoint (l.activeAddresses (u ++ [d₁])) (r.branchAddresses (u ++ [d₂])) := by
  rw [Finset.disjoint_left]
  intro a ha1 ha2
  obtain ⟨b₁, -, hb₁⟩ := (mem_activeAddresses_iff l (u ++ [d₁]) a).mp ha1
  obtain ⟨b₂, -, hb₂⟩ := (mem_branchAddresses_iff r (u ++ [d₂]) a).mp ha2
  exact left_right_append_ne_of_ne d₁ d₂ h u b₁ b₂ (hb₁.symm.trans hb₂)

/-- On a left-subtree address, the node assignment agrees with the left assignment. -/
theorem branchAssignment_node_left (l r : CGTree) (u a : List Bool)
    (ha : a ∈ l.activeAddresses (u ++ [false])) :
    (CGTree.node l r).branchAssignment u a = l.branchAssignment (u ++ [false]) a := by
  have hau : a ≠ u := by
    intro hcon
    rw [hcon] at ha
    exact not_mem_active_child l u false ha
  have hbr : a ∉ r.branchAddresses (u ++ [true]) :=
    Finset.disjoint_left.mp (disjoint_active_branch l r u false true (by decide)) ha
  have hiff : (a ∈ (CGTree.node l r).branchAddresses u) ↔
      (a ∈ l.branchAddresses (u ++ [false])) := by
    rw [CGTree.branchAddresses_node]
    simp only [Finset.mem_insert, Finset.mem_union]
    constructor
    · rintro (rfl | h | h)
      · exact absurd rfl hau
      · exact h
      · exact absurd h hbr
    · intro h
      exact Or.inr (Or.inl h)
  show decide (a ∈ (CGTree.node l r).branchAddresses u) =
    decide (a ∈ l.branchAddresses (u ++ [false]))
  simp only [hiff]

/-- On a right-subtree address, the node assignment agrees with the right assignment. -/
theorem branchAssignment_node_right (l r : CGTree) (u a : List Bool)
    (ha : a ∈ r.activeAddresses (u ++ [true])) :
    (CGTree.node l r).branchAssignment u a = r.branchAssignment (u ++ [true]) a := by
  have hau : a ≠ u := by
    intro hcon
    rw [hcon] at ha
    exact not_mem_active_child r u true ha
  have hbr : a ∉ l.branchAddresses (u ++ [false]) :=
    Finset.disjoint_left.mp (disjoint_active_branch r l u true false (by decide)) ha
  have hiff : (a ∈ (CGTree.node l r).branchAddresses u) ↔
      (a ∈ r.branchAddresses (u ++ [true])) := by
    rw [CGTree.branchAddresses_node]
    simp only [Finset.mem_insert, Finset.mem_union]
    constructor
    · rintro (rfl | h | h)
      · exact absurd rfl hau
      · exact absurd h hbr
      · exact h
    · intro h
      exact Or.inr (Or.inr h)
  show decide (a ∈ (CGTree.node l r).branchAddresses u) =
    decide (a ∈ r.branchAddresses (u ++ [true]))
  simp only [hiff]

/-- The branch assignment translates along the root prefix. -/
theorem branchAssignment_append (t : CGTree) (u b : List Bool) :
    t.branchAssignment u (u ++ b) = t.branchAssignment [] b := by
  have hiff : (u ++ b ∈ t.branchAddresses u) ↔ (b ∈ t.branchAddresses []) := by
    constructor
    · intro h
      obtain ⟨c, hc, hcb⟩ := (mem_branchAddresses_iff t u (u ++ b)).mp h
      have hbc : b = c := List.append_cancel_left hcb
      rw [hbc]
      exact hc
    · intro h
      exact (mem_branchAddresses_iff t u (u ++ b)).mpr ⟨b, h, rfl⟩
  show decide (u ++ b ∈ t.branchAddresses u) = decide (b ∈ t.branchAddresses [])
  simp only [hiff]

/-- No non-empty continuation of a leaf address is active. -/
private theorem not_mem_active_of_leaf_helper (t : CGTree) :
    ∀ (a b : List Bool), a ∈ t.leafAddresses [] → b ≠ [] → a ++ b ∉ t.activeAddresses [] := by
  induction t with
  | leaf =>
      intro a b ha hb
      simp only [CGTree.leafAddresses_leaf, Finset.mem_singleton] at ha
      subst ha
      simp only [CGTree.activeAddresses_leaf, Finset.mem_singleton]
      intro hcon
      simp only [List.nil_append] at hcon
      exact hb hcon
  | node l r ihl ihr =>
      intro a b ha hb
      simp only [CGTree.leafAddresses_node, Finset.mem_union] at ha
      simp only [CGTree.activeAddresses_node, Finset.mem_insert, Finset.mem_union]
      intro hcon
      rcases ha with ha | ha
      · obtain ⟨c, hc, hac⟩ := (mem_leafAddresses_iff l ([] ++ [false]) a).mp ha
        rcases hcon with hcon | hcon | hcon
        · simp [hac, List.append_assoc] at hcon
        · obtain ⟨d, hd, had⟩ := (mem_activeAddresses_iff l ([] ++ [false]) (a ++ b)).mp hcon
          rw [hac] at had
          have had2 : ([] ++ [false]) ++ (c ++ b) = ([] ++ [false]) ++ d := by
            rw [← List.append_assoc]
            exact had
          have hcb : c ++ b = d :=
            List.append_cancel_left had2
          have hd' : c ++ b ∈ l.activeAddresses [] := by
            rw [hcb]
            exact hd
          exact ihl c b hc hb hd'
        · obtain ⟨d, hd, had⟩ := (mem_activeAddresses_iff r ([] ++ [true]) (a ++ b)).mp hcon
          rw [hac] at had
          have had2 : ([] ++ [false]) ++ (c ++ b) = ([] ++ [true]) ++ d := by
            rw [← List.append_assoc]
            exact had
          exact left_right_append_ne [] (c ++ b) d had2
      · obtain ⟨c, hc, hac⟩ := (mem_leafAddresses_iff r ([] ++ [true]) a).mp ha
        rcases hcon with hcon | hcon | hcon
        · simp [hac, List.append_assoc] at hcon
        · obtain ⟨d, hd, had⟩ := (mem_activeAddresses_iff l ([] ++ [false]) (a ++ b)).mp hcon
          rw [hac] at had
          have had2 : ([] ++ [true]) ++ (c ++ b) = ([] ++ [false]) ++ d := by
            rw [← List.append_assoc]
            exact had
          exact left_right_append_ne_of_ne true false (by decide) [] (c ++ b) d had2
        · obtain ⟨d, hd, had⟩ := (mem_activeAddresses_iff r ([] ++ [true]) (a ++ b)).mp hcon
          rw [hac] at had
          have had2 : ([] ++ [true]) ++ (c ++ b) = ([] ++ [true]) ++ d := by
            rw [← List.append_assoc]
            exact had
          have hcb : c ++ b = d :=
            List.append_cancel_left had2
          have hd' : c ++ b ∈ r.activeAddresses [] := by
            rw [hcb]
            exact hd
          exact ihr c b hc hb hd'

/-- the active addresses are exactly the branch and leaf
addresses, and the two kinds are disjoint. -/
theorem CGTree.activeAddresses_eq_union (t : CGTree) (u : List Bool) :
    t.activeAddresses u = t.branchAddresses u ∪ t.leafAddresses u ∧
      Disjoint (t.branchAddresses u) (t.leafAddresses u) := by
  revert u
  induction t with
  | leaf =>
      intro u
      constructor
      · simp [CGTree.activeAddresses_leaf, CGTree.branchAddresses_leaf, CGTree.leafAddresses_leaf]
      · rw [CGTree.branchAddresses_leaf, Finset.disjoint_left]
        intro a ha _
        exact Finset.notMem_empty a ha
  | node l r ihl ihr =>
      intro u
      obtain ⟨ehl, dhl⟩ := ihl (u ++ [false])
      obtain ⟨ehr, dhr⟩ := ihr (u ++ [true])
      constructor
      · rw [CGTree.activeAddresses_node, CGTree.branchAddresses_node, CGTree.leafAddresses_node, ehl, ehr]
        ext a
        simp only [Finset.mem_insert, Finset.mem_union]
        tauto
      · rw [CGTree.branchAddresses_node, CGTree.leafAddresses_node, Finset.disjoint_left]
        intro a ha1 ha2
        simp only [Finset.mem_insert, Finset.mem_union] at ha1 ha2
        rcases ha1 with (rfl | ha1 | ha1)
        · rcases ha2 with ha2 | ha2
          · exact not_mem_leaf_child l a false ha2
          · exact not_mem_leaf_child r a true ha2
        · rcases ha2 with ha2 | ha2
          · exact Finset.disjoint_left.mp dhl ha1 ha2
          · exact Finset.disjoint_left.mp (disjoint_branch_leaf l r u false true (by decide)) ha1 ha2
        · rcases ha2 with ha2 | ha2
          · exact Finset.disjoint_left.mp (disjoint_branch_leaf r l u true false (by decide)) ha1 ha2
          · exact Finset.disjoint_left.mp dhr ha1 ha2

theorem CGTree.branchAssignment_eq_true_iff (t : CGTree) (u a : List Bool) :
    t.branchAssignment u a = true ↔ a ∈ t.branchAddresses u := by
  show decide (a ∈ t.branchAddresses u) = true ↔ a ∈ t.branchAddresses u
  by_cases h : a ∈ t.branchAddresses u <;> simp [h]

/-- on an active address, assignment `false` is exactly being a
leaf address of the tree. -/
theorem CGTree.branchAssignment_eq_false_of_mem_active (t : CGTree) (u a : List Bool) :
    a ∈ t.activeAddresses u →
      (t.branchAssignment u a = false ↔ a ∈ t.leafAddresses u) := by
  intro ha
  obtain ⟨eq, disj⟩ := CGTree.activeAddresses_eq_union t u
  constructor
  · intro hfalse
    by_cases hleaf : a ∈ t.leafAddresses u
    · exact hleaf
    · have hbr : a ∈ t.branchAddresses u := by
        have hmem : a ∈ t.branchAddresses u ∪ t.leafAddresses u := by
          rw [← eq]
          exact ha
        simp only [Finset.mem_union] at hmem
        rcases hmem with hmem | hmem
        · exact hmem
        · exact absurd hmem hleaf
      have htrue : t.branchAssignment u a = true :=
        (CGTree.branchAssignment_eq_true_iff t u a).mpr hbr
      rw [htrue] at hfalse
      simp at hfalse
  · intro hleaf
    have hnt : ¬ t.branchAssignment u a = true := by
      intro htrue
      have hbr : a ∈ t.branchAddresses u :=
        (CGTree.branchAssignment_eq_true_iff t u a).mp htrue
      exact Finset.disjoint_left.mp disj hbr hleaf
    cases hval : t.branchAssignment u a
    · rfl
    · exact (hnt hval).elim

theorem CGTree.mem_activeAddresses_node_iff (l r : CGTree) (u a : List Bool) :
    a ∈ (CGTree.node l r).activeAddresses u ↔
      a = u ∨ (∃ b, a = (u ++ [false]) ++ b ∧ b ∈ l.activeAddresses []) ∨
        ∃ b, a = (u ++ [true]) ++ b ∧ b ∈ r.activeAddresses [] := by
  rw [CGTree.activeAddresses_node]
  simp only [Finset.mem_insert, Finset.mem_union]
  constructor
  · rintro (rfl | hl | hr)
    · exact Or.inl rfl
    · obtain ⟨b, hb, hab⟩ := (mem_activeAddresses_iff l (u ++ [false]) a).mp hl
      exact Or.inr (Or.inl ⟨b, hab, hb⟩)
    · obtain ⟨b, hb, hab⟩ := (mem_activeAddresses_iff r (u ++ [true]) a).mp hr
      exact Or.inr (Or.inr ⟨b, hab, hb⟩)
  · rintro (rfl | ⟨b, hab, hb⟩ | ⟨b, hab, hb⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ((mem_activeAddresses_iff l (u ++ [false]) a).mpr ⟨b, hb, hab⟩))
    · exact Or.inr (Or.inr ((mem_activeAddresses_iff r (u ++ [true]) a).mpr ⟨b, hb, hab⟩))

/-- no descendant of a leaf is active. A non-empty continuation
`b` of a leaf address `a` is never constrained by the tree. -/
theorem CGTree.not_mem_activeAddresses_of_leaf (t : CGTree) {a : List Bool}
    (ha : a ∈ t.leafAddresses []) {b : List Bool} (hb : b ≠ []) :
    a ++ b ∉ t.activeAddresses [] := by
  exact not_mem_active_of_leaf_helper t a b ha hb

/-- The finite product over the active addresses at any prefix is the existing weight. -/
theorem cylinder_mass_active {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (t : CGTree) (u : List Bool) :
    BinaryTreeAddressLaw.cylinder_mass p (t.activeAddresses u) (t.branchAssignment u) =
      ENNReal.ofReal (t.weight p (1 - p)) := by
  revert u
  induction t with
  | leaf =>
      intro u
      have hnt : ¬ CGTree.leaf.branchAssignment u u = true := by
        rw [CGTree.branchAssignment_eq_true_iff, CGTree.branchAddresses_leaf]
        exact Finset.notMem_empty u
      have hw : CGTree.leaf.weight p (1 - p) = 1 - p := rfl
      have hmass : BinaryTreeAddressLaw.cylinder_mass p (CGTree.leaf.activeAddresses u)
          (CGTree.leaf.branchAssignment u) = ENNReal.ofReal (1 - p) := by
        simp only [CGTree.activeAddresses_leaf, BinaryTreeAddressLaw.cylinder_mass,
          Finset.prod_singleton, ite_eq_right hnt]
      rw [hmass, hw]
  | node l r ihl ihr =>
      intro u
      have hun : u ∉ l.activeAddresses (u ++ [false]) ∪ r.activeAddresses (u ++ [true]) := by
        intro hcon
        simp only [Finset.mem_union] at hcon
        rcases hcon with hcon | hcon
        · exact not_mem_active_child l u false hcon
        · exact not_mem_active_child r u true hcon
      have hdisj : Disjoint (l.activeAddresses (u ++ [false])) (r.activeAddresses (u ++ [true])) :=
        disjoint_active_child l r u false true (by decide)
      have hu_true : (CGTree.node l r).branchAssignment u u = true := by
        rw [CGTree.branchAssignment_eq_true_iff, CGTree.branchAddresses_node]
        simp
      have hpointL : ∀ a ∈ l.activeAddresses (u ++ [false]),
          (if (CGTree.node l r).branchAssignment u a then ENNReal.ofReal p else ENNReal.ofReal (1 - p)) =
          (if l.branchAssignment (u ++ [false]) a then ENNReal.ofReal p else ENNReal.ofReal (1 - p)) := by
        intro a ha
        rw [branchAssignment_node_left l r u a ha]
      have hpointR : ∀ a ∈ r.activeAddresses (u ++ [true]),
          (if (CGTree.node l r).branchAssignment u a then ENNReal.ofReal p else ENNReal.ofReal (1 - p)) =
          (if r.branchAssignment (u ++ [true]) a then ENNReal.ofReal p else ENNReal.ofReal (1 - p)) := by
        intro a ha
        rw [branchAssignment_node_right l r u a ha]
      have ihL := ihl (u ++ [false])
      have ihR := ihr (u ++ [true])
      simp only [BinaryTreeAddressLaw.cylinder_mass] at ihL ihR
      simp only [CGTree.activeAddresses_node, BinaryTreeAddressLaw.cylinder_mass,
        Finset.prod_insert hun, Finset.prod_union hdisj]
      rw [Finset.prod_congr rfl hpointL, Finset.prod_congr rfl hpointR, ite_eq_left hu_true, ihL,
        ihR]
      have hw : (CGTree.node l r).weight p (1 - p) =
          p * l.weight p (1 - p) * r.weight p (1 - p) := rfl
      rw [hw, ENNReal.ofReal_mul
          (mul_nonneg hp0 (cgWeight_nonneg p (1 - p) hp0 (sub_nonneg.mpr hp1) l)),
        ENNReal.ofReal_mul hp0, mul_assoc]

theorem treeCylinder_def (t : CGTree) :
    treeCylinder t =
      BinaryTreeAddressLaw.cylinder (t.activeAddresses []) (t.branchAssignment []) := by
  rfl

theorem mem_treeCylinder {t : CGTree} {ω : BinaryTreeAddressLaw.Ω} :
    ω ∈ treeCylinder t ↔ ∀ a ∈ t.activeAddresses [], ω a = t.branchAssignment [] a := by
  rw [treeCylinder_def]
  exact BinaryTreeAddressLaw.mem_cylinder

/-- membership depends only on the values at active addresses:
changing `ω` anywhere else, in particular below any leaf, keeps it
in (and out of) the cylinder. -/
theorem treeCylinder_mem_of_agree_on_active {t : CGTree}
    {ω ω' : BinaryTreeAddressLaw.Ω}
    (h : ∀ a ∈ t.activeAddresses [], ω' a = ω a) :
    ω' ∈ treeCylinder t ↔ ω ∈ treeCylinder t := by
  rw [mem_treeCylinder, mem_treeCylinder]
  constructor
  · intro h2 a ha
    rw [← h a ha]
    exact h2 a ha
  · intro h2 a ha
    rw [h a ha]
    exact h2 a ha

/-- the tree's own assignment, read as a point of `Ω`, lies in
its cylinder, so every tree cylinder is nonempty (consistent) even
when a boundary probability gives it measure zero. -/
theorem CGTree.branchAssignment_mem_treeCylinder (t : CGTree) :
    t.branchAssignment [] ∈ treeCylinder t := by
  rw [mem_treeCylinder]
  intro a _
  rfl

/-- a node cylinder is the root-branch event together with the
two subtree cylinders pulled back along the exact prefix shifts of the binary address law. This is the decomposition the measure proof
recurses on. -/
theorem treeCylinder_node (l r : CGTree) :
    treeCylinder (CGTree.node l r) =
      BinaryTreeAddressLaw.branchAt [] ∩
        (BinaryTreeAddressLaw.shiftLeft ⁻¹' treeCylinder l) ∩
          (BinaryTreeAddressLaw.shiftRight ⁻¹' treeCylinder r) := by
  ext ω
  simp only [Set.mem_inter_iff, BinaryTreeAddressLaw.branchAt, Set.mem_setOf_eq,
    Set.mem_preimage, mem_treeCylinder]
  constructor
  · intro h
    have hroot : ω [] = true := by
      have hmem : [] ∈ (CGTree.node l r).activeAddresses [] := by
        simp [CGTree.activeAddresses_node]
      have e := h [] hmem
      have ht : (CGTree.node l r).branchAssignment [] [] = true := by
        rw [CGTree.branchAssignment_eq_true_iff, CGTree.branchAddresses_node]
        simp
      rw [ht] at e
      exact e
    refine ⟨⟨hroot, ?_⟩, ?_⟩
    · intro b hb
      have hmem : [false] ++ b ∈ l.activeAddresses ([] ++ [false]) :=
        (mem_activeAddresses_iff l ([] ++ [false]) ([false] ++ b)).mpr ⟨b, hb, by simp⟩
      have hmemN : [false] ++ b ∈ (CGTree.node l r).activeAddresses [] := by
        simp only [CGTree.activeAddresses_node, Finset.mem_insert, Finset.mem_union]
        exact Or.inr (Or.inl hmem)
      have e := h ([false] ++ b) hmemN
      have hagree : (CGTree.node l r).branchAssignment [] ([false] ++ b) =
          l.branchAssignment ([] ++ [false]) ([false] ++ b) :=
        branchAssignment_node_left l r [] ([false] ++ b) hmem
      have htrans : l.branchAssignment ([] ++ [false]) ([false] ++ b) =
          l.branchAssignment [] b := by
        have h2 := branchAssignment_append l ([] ++ [false]) b
        simpa using h2
      show ω ([false] ++ b) = l.branchAssignment [] b
      rw [e, hagree, htrans]
    · intro b hb
      have hmem : [true] ++ b ∈ r.activeAddresses ([] ++ [true]) :=
        (mem_activeAddresses_iff r ([] ++ [true]) ([true] ++ b)).mpr ⟨b, hb, by simp⟩
      have hmemN : [true] ++ b ∈ (CGTree.node l r).activeAddresses [] := by
        simp only [CGTree.activeAddresses_node, Finset.mem_insert, Finset.mem_union]
        exact Or.inr (Or.inr hmem)
      have e := h ([true] ++ b) hmemN
      have hagree : (CGTree.node l r).branchAssignment [] ([true] ++ b) =
          r.branchAssignment ([] ++ [true]) ([true] ++ b) :=
        branchAssignment_node_right l r [] ([true] ++ b) hmem
      have htrans : r.branchAssignment ([] ++ [true]) ([true] ++ b) =
          r.branchAssignment [] b := by
        have h2 := branchAssignment_append r ([] ++ [true]) b
        simpa using h2
      show ω ([true] ++ b) = r.branchAssignment [] b
      rw [e, hagree, htrans]
  · rintro ⟨⟨hroot, hL⟩, hR⟩
    intro a ha
    simp only [CGTree.activeAddresses_node, Finset.mem_insert, Finset.mem_union] at ha
    rcases ha with (rfl | ha | ha)
    · have ht : (CGTree.node l r).branchAssignment [] [] = true := by
        rw [CGTree.branchAssignment_eq_true_iff, CGTree.branchAddresses_node]
        simp
      rw [ht]
      exact hroot
    · obtain ⟨c, hc, hac⟩ := (mem_activeAddresses_iff l ([] ++ [false]) a).mp ha
      have eL := hL c hc
      have hagree : (CGTree.node l r).branchAssignment [] a =
          l.branchAssignment ([] ++ [false]) a :=
        branchAssignment_node_left l r [] a ha
      have htrans : l.branchAssignment ([] ++ [false]) a = l.branchAssignment [] c := by
        rw [hac]
        exact branchAssignment_append l ([] ++ [false]) c
      have haddr : [false] ++ c = a := by simp [hac, List.append_assoc]
      have eL' : ω ([false] ++ c) = l.branchAssignment [] c := eL
      rw [haddr] at eL'
      rw [eL', ← htrans, ← hagree]
    · obtain ⟨c, hc, hac⟩ := (mem_activeAddresses_iff r ([] ++ [true]) a).mp ha
      have eR := hR c hc
      have hagree : (CGTree.node l r).branchAssignment [] a =
          r.branchAssignment ([] ++ [true]) a :=
        branchAssignment_node_right l r [] a ha
      have htrans : r.branchAssignment ([] ++ [true]) a = r.branchAssignment [] c := by
        rw [hac]
        exact branchAssignment_append r ([] ++ [true]) c
      have haddr : [true] ++ c = a := by simp [hac, List.append_assoc]
      have eR' : ω ([true] ++ c) = r.branchAssignment [] c := eR
      rw [haddr] at eR'
      rw [eR', ← htrans, ← hagree]

/-- a leaf cylinder is exactly the root-leaf event; the values
below the root are unrestricted. -/
theorem treeCylinder_leaf :
    treeCylinder CGTree.leaf = BinaryTreeAddressLaw.leafAt [] := by
  have hf : CGTree.leaf.branchAssignment [] [] = false := by
    have hnt : ¬ CGTree.leaf.branchAssignment [] [] = true := by
      rw [CGTree.branchAssignment_eq_true_iff, CGTree.branchAddresses_leaf]
      exact Finset.notMem_empty []
    cases hval : CGTree.leaf.branchAssignment [] []
    · exact hval
    · exact (hnt hval).elim
  ext ω
  simp only [mem_treeCylinder, BinaryTreeAddressLaw.leafAt, Set.mem_setOf_eq,
    CGTree.activeAddresses_leaf, Finset.mem_singleton]
  constructor
  · intro h
    have e := h [] rfl
    rw [hf] at e
    exact e
  · intro h a ha
    subst ha
    rw [hf]
    exact h

/-! ## cylinder measure is the existing p/q weight -/

/-- the finite product over the active addresses is the
existing weight with leaf weight `1 - p`. Proof route on port:
induction on `t`, splitting `cylinder_mass` over the disjoint
branch/leaf (equivalently left/right) address sets. -/
theorem treeCylinder_mass {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (t : CGTree) :
    BinaryTreeAddressLaw.cylinder_mass p (t.activeAddresses []) (t.branchAssignment []) =
      ENNReal.ofReal (t.weight p (1 - p)) :=
  cylinder_mass_active hp0 hp1 t []

/-- the measure of a tree cylinder under the address law is its
existing p/q weight (leaf weight `1 - p`). Directly
`BinaryTreeAddressLaw.law_cylinder` composed with
`treeCylinder_mass`. No range hypothesis on a second weight is
needed or possible: the address law has only the one parameter. -/
theorem treeCylinder_weight {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (t : CGTree) :
    BinaryTreeAddressLaw.law p hp0 hp1 (treeCylinder t) =
      ENNReal.ofReal (t.weight p (1 - p)) := by
  rw [treeCylinder_def, BinaryTreeAddressLaw.law_cylinder hp0 hp1, treeCylinder_mass hp0 hp1]

/-! ## distinct finite trees have disjoint cylinders -/

/-- two distinct finite trees disagree, as branch/leaf, at some
address active for both. Proof route on port: induction on the first
tree, case split on the second; the first node where one side is a
leaf and the other a branch gives the address, and prefixes keep it
active for both. -/
theorem CGTree.exists_disagreement_of_ne {t₁ t₂ : CGTree} (h : t₁ ≠ t₂) :
    ∃ a, a ∈ t₁.activeAddresses [] ∧ a ∈ t₂.activeAddresses [] ∧
      t₁.branchAssignment [] a ≠ t₂.branchAssignment [] a := by
  revert t₂ h
  induction t₁ with
  | leaf =>
      intro t₂ h
      cases t₂ with
      | leaf => exact absurd rfl h
      | node l r =>
          have hf : CGTree.leaf.branchAssignment [] [] = false := by
            have hnt : ¬ CGTree.leaf.branchAssignment [] [] = true := by
              rw [CGTree.branchAssignment_eq_true_iff, CGTree.branchAddresses_leaf]
              exact Finset.notMem_empty []
            cases hval : CGTree.leaf.branchAssignment [] []
            · exact hval
            · exact (hnt hval).elim
          have ht : (CGTree.node l r).branchAssignment [] [] = true := by
            rw [CGTree.branchAssignment_eq_true_iff, CGTree.branchAddresses_node]
            simp
          refine ⟨[], by simp [CGTree.activeAddresses_leaf],
            by simp [CGTree.activeAddresses_node], ?_⟩
          rw [hf, ht]
          decide
  | node l₁ r₁ ihl ihr =>
      intro t₂ h
      cases t₂ with
      | leaf =>
          have ht : (CGTree.node l₁ r₁).branchAssignment [] [] = true := by
            rw [CGTree.branchAssignment_eq_true_iff, CGTree.branchAddresses_node]
            simp
          have hf : CGTree.leaf.branchAssignment [] [] = false := by
            have hnt : ¬ CGTree.leaf.branchAssignment [] [] = true := by
              rw [CGTree.branchAssignment_eq_true_iff, CGTree.branchAddresses_leaf]
              exact Finset.notMem_empty []
            cases hval : CGTree.leaf.branchAssignment [] []
            · exact hval
            · exact (hnt hval).elim
          refine ⟨[], by simp [CGTree.activeAddresses_node],
            by simp [CGTree.activeAddresses_leaf], ?_⟩
          rw [ht, hf]
          decide
      | node l₂ r₂ =>
          have hdisj : l₁ ≠ l₂ ∨ r₁ ≠ r₂ := by
            by_cases hl : l₁ = l₂
            · by_cases hr : r₁ = r₂
              · have heq : CGTree.node l₁ r₁ = CGTree.node l₂ r₂ := by rw [hl, hr]
                exact absurd heq h
              · exact Or.inr hr
            · exact Or.inl hl
          rcases hdisj with hne | hne
          · obtain ⟨a, ha1, ha2, hdiff⟩ := ihl hne
            refine ⟨([] ++ [false]) ++ a, ?_, ?_, ?_⟩
            · simp only [CGTree.activeAddresses_node, Finset.mem_insert, Finset.mem_union]
              exact Or.inr (Or.inl
                ((mem_activeAddresses_iff l₁ ([] ++ [false]) (([] ++ [false]) ++ a)).mpr
                  ⟨a, ha1, rfl⟩))
            · simp only [CGTree.activeAddresses_node, Finset.mem_insert, Finset.mem_union]
              exact Or.inr (Or.inl
                ((mem_activeAddresses_iff l₂ ([] ++ [false]) (([] ++ [false]) ++ a)).mpr
                  ⟨a, ha2, rfl⟩))
            · have ag1 : (CGTree.node l₁ r₁).branchAssignment [] (([] ++ [false]) ++ a) =
                  l₁.branchAssignment ([] ++ [false]) (([] ++ [false]) ++ a) :=
                branchAssignment_node_left l₁ r₁ [] _ ((mem_activeAddresses_iff l₁
                  ([] ++ [false]) (([] ++ [false]) ++ a)).mpr ⟨a, ha1, rfl⟩)
              have ag2 : (CGTree.node l₂ r₂).branchAssignment [] (([] ++ [false]) ++ a) =
                  l₂.branchAssignment ([] ++ [false]) (([] ++ [false]) ++ a) :=
                branchAssignment_node_left l₂ r₂ [] _ ((mem_activeAddresses_iff l₂
                  ([] ++ [false]) (([] ++ [false]) ++ a)).mpr ⟨a, ha2, rfl⟩)
              have tr1 : l₁.branchAssignment ([] ++ [false]) (([] ++ [false]) ++ a) =
                  l₁.branchAssignment [] a :=
                branchAssignment_append l₁ ([] ++ [false]) a
              have tr2 : l₂.branchAssignment ([] ++ [false]) (([] ++ [false]) ++ a) =
                  l₂.branchAssignment [] a :=
                branchAssignment_append l₂ ([] ++ [false]) a
              rw [ag1, ag2, tr1, tr2]
              exact hdiff
          · obtain ⟨a, ha1, ha2, hdiff⟩ := ihr hne
            refine ⟨([] ++ [true]) ++ a, ?_, ?_, ?_⟩
            · simp only [CGTree.activeAddresses_node, Finset.mem_insert, Finset.mem_union]
              exact Or.inr (Or.inr
                ((mem_activeAddresses_iff r₁ ([] ++ [true]) (([] ++ [true]) ++ a)).mpr
                  ⟨a, ha1, rfl⟩))
            · simp only [CGTree.activeAddresses_node, Finset.mem_insert, Finset.mem_union]
              exact Or.inr (Or.inr
                ((mem_activeAddresses_iff r₂ ([] ++ [true]) (([] ++ [true]) ++ a)).mpr
                  ⟨a, ha2, rfl⟩))
            · have ag1 : (CGTree.node l₁ r₁).branchAssignment [] (([] ++ [true]) ++ a) =
                  r₁.branchAssignment ([] ++ [true]) (([] ++ [true]) ++ a) :=
                branchAssignment_node_right l₁ r₁ [] _ ((mem_activeAddresses_iff r₁
                  ([] ++ [true]) (([] ++ [true]) ++ a)).mpr ⟨a, ha1, rfl⟩)
              have ag2 : (CGTree.node l₂ r₂).branchAssignment [] (([] ++ [true]) ++ a) =
                  r₂.branchAssignment ([] ++ [true]) (([] ++ [true]) ++ a) :=
                branchAssignment_node_right l₂ r₂ [] _ ((mem_activeAddresses_iff r₂
                  ([] ++ [true]) (([] ++ [true]) ++ a)).mpr ⟨a, ha2, rfl⟩)
              have tr1 : r₁.branchAssignment ([] ++ [true]) (([] ++ [true]) ++ a) =
                  r₁.branchAssignment [] a :=
                branchAssignment_append r₁ ([] ++ [true]) a
              have tr2 : r₂.branchAssignment ([] ++ [true]) (([] ++ [true]) ++ a) =
                  r₂.branchAssignment [] a :=
                branchAssignment_append r₂ ([] ++ [true]) a
              rw [ag1, ag2, tr1, tr2]
              exact hdiff

/-- distinct finite trees have disjoint cylinders, via
`BinaryTreeAddressLaw.cylinder_disjoint_of_ne` at the disagreement
address of `exists_disagreement_of_ne`. -/
theorem treeCylinder_disjoint_of_ne {t₁ t₂ : CGTree} (h : t₁ ≠ t₂) :
    Disjoint (treeCylinder t₁) (treeCylinder t₂) := by
  rw [Set.disjoint_left]
  intro ω h1 h2
  obtain ⟨a, ha1, ha2, hne⟩ := CGTree.exists_disagreement_of_ne h
  rw [mem_treeCylinder] at h1 h2
  exact hne ((h1 a ha1).symm.trans (h2 a ha2))

/-- NEW (proposed symbol): the production headline. For every
branch probability `p ∈ [0, 1]`, each finite tree's cylinder has
measure its existing p/q weight (leaf weight `1 - p`), and distinct
finite trees have disjoint cylinders. The two weight clauses are
`treeCylinder_weight` at `t₁` and `t₂`; the disjointness clause is
`treeCylinder_disjoint_of_ne`. Boundary probabilities are included:
at `p = 0` or `p = 1` a consistent (nonempty) cylinder may have
measure zero; see the Tests boundary checks. -/
theorem treeCylinder_weight_disjoint {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (t₁ t₂ : CGTree) (h : t₁ ≠ t₂) :
    BinaryTreeAddressLaw.law p hp0 hp1 (treeCylinder t₁) =
        ENNReal.ofReal (t₁.weight p (1 - p)) ∧
      BinaryTreeAddressLaw.law p hp0 hp1 (treeCylinder t₂) =
        ENNReal.ofReal (t₂.weight p (1 - p)) ∧
      Disjoint (treeCylinder t₁) (treeCylinder t₂) :=
  ⟨treeCylinder_weight hp0 hp1 t₁, treeCylinder_weight hp0 hp1 t₂,
    treeCylinder_disjoint_of_ne h⟩
/-! ## derivation trees (`PDerivTree`) via their shapes -/

/-- the address sets of a derivation tree are those of its
`CGTree` shape, at every prefix. -/
theorem PDerivTree.addresses_shape {NT T : Type*} (t : PDerivTree NT T) (u : List Bool) :
    t.branchAddresses u = t.shape.branchAddresses u ∧
      t.leafAddresses u = t.shape.leafAddresses u ∧
      t.activeAddresses u = t.shape.activeAddresses u := by
  exact ⟨rfl, rfl, rfl⟩

/-- a derivation tree's cylinder is the cylinder of its shape. -/
theorem PDerivTree.treeCylinder_eq {NT T : Type*} (t : PDerivTree NT T) :
    t.treeCylinder = Cslib.Language.treeCylinder t.shape := by
  rfl

/-- the shape maps of the copied bijection agree with the
existing `toCGTree` on `ambG` trees. -/
theorem PDerivTree.shape_eq_toCGTree (t : PDerivTree ambG.NT Unit) :
    t.shape = toCGTree t := by
  induction t with
  | leaf A a => rfl
  | node A B C l r ihl ihr => simp only [PDerivTree.shape, toCGTree, ihl, ihr]

/-- A derivation tree's existing weight equals its shape's weight under shape-only rule weights. -/
theorem PDerivTree.weightOf_eq_shape_weight {NT T : Type*} (w : ContextFreeRule T NT → ℝ)
    (p : ℝ) (hw_node : ∀ A B C, w ⟨A, [Symbol.nonterminal B, Symbol.nonterminal C]⟩ = p)
    (hw_leaf : ∀ A a, w ⟨A, [Symbol.terminal a]⟩ = 1 - p) (t : PDerivTree NT T) :
    t.weightOf w = t.shape.weight p (1 - p) := by
  induction t with
  | leaf A a => simp only [PDerivTree.weightOf, PDerivTree.shape, CGTree.weight, hw_leaf]
  | node A B C l r ihl ihr =>
      simp only [PDerivTree.weightOf, PDerivTree.shape, CGTree.weight, hw_node, ihl, ihr]

/-- under rule weights that depend only on rule shape (binary
weight `p`, terminal weight `1 - p`), a derivation tree's cylinder
measure is its existing derivation weight `PDerivTree.weightOf`.
Proof route: `treeCylinder_eq`, induction on `t` for
`weightOf = shape.weight`, then `treeCylinder_weight`. -/
theorem PDerivTree.treeCylinder_weight {NT T : Type*} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (w : ContextFreeRule T NT → ℝ)
    (hw_node : ∀ A B C, w ⟨A, [Symbol.nonterminal B, Symbol.nonterminal C]⟩ = p)
    (hw_leaf : ∀ A a, w ⟨A, [Symbol.terminal a]⟩ = 1 - p)
    (t : PDerivTree NT T) :
    BinaryTreeAddressLaw.law p hp0 hp1 t.treeCylinder = ENNReal.ofReal (t.weightOf w) := by
  rw [PDerivTree.treeCylinder_eq, Cslib.Language.treeCylinder_weight hp0 hp1,
    PDerivTree.weightOf_eq_shape_weight w p hw_node hw_leaf t]

/-- derivation trees of distinct shape have disjoint cylinders.
Distinct labelled trees of the *same* shape have equal cylinders, so
shape-distinctness is the exact hypothesis; terminal yield plays no
role (two trees below share a yield and are still disjoint). -/
theorem PDerivTree.treeCylinder_disjoint_of_shape_ne {NT T : Type*}
    {t₁ t₂ : PDerivTree NT T} (h : t₁.shape ≠ t₂.shape) :
    Disjoint t₁.treeCylinder t₂.treeCylinder := by
  rw [PDerivTree.treeCylinder_eq, PDerivTree.treeCylinder_eq]
  exact treeCylinder_disjoint_of_ne h


end Cslib.Language
