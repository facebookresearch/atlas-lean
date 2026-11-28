/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Nat.Log
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
public import Mathlib.Order.MinMax
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

/-!
# Braun trees: shape, completeness, and height bounds

Binary trees (`Tree`), their `size` / `height` / `minHeight`, the Braun
invariant (`braun`), almost-completeness (`acomplete`), and completeness
(`complete`), with the height / size / logarithm bounds that the array
implementation rests on.

Covered book content: §11.2 (`braun`, `acomplete`, Lemma 11.1 via
`acomplete_node_of_size`, Lemma 11.2 via `braun_acomplete`, Exercise 11.1
via `braun_height_bound` / `braun_height_log`, Exercise 11.2 via `lh`,
Exercise 11.3 via `braun_height_children`), Chapter 4 (`complete`:
Lemmas 4.1–4.4, Corollary 4.5; Lemmas 4.7–4.8 via
`acomplete_height_log` / `acomplete_minHeight_log`; Lemma 4.6 via
`acomplete_height_optimal`; Exercise 4.8 via `acomplete_node_iff`),
and `inorder` (used by `Balance`).

## Carrier

`Tree` is a dedicated inductive, not Mathlib's `BinaryTree`: the
book and the Isabelle development state every definition, equation,
and induction over their own tree datatype, with `Node l x r`
(children first), while `BinaryTree.node` takes the value first
(`node x l r`). Restating the development over `BinaryTree` would
reorder every pattern match, equation lemma, and induction case
for no proved benefit: the development is self-contained, using no
Mathlib tree lemmas, and `size` / `height` are the book's recursions
(`|t|`, `h t`). This follows the repo's sibling textbook ports,
which likewise carry their own types (Chapter 13 quadtrees,
Chapter 15 leftist heaps).

## Provenance

A Lean formalisation of the Chapter 11 Isabelle development in the
Isabelle distribution's `HOL-Data_Structures` theories
(`Braun_Tree.thy`, `Balance.thy`). The book is Tobias Nipkow (ed.),
*Functional Data Structures and Algorithms* (ACM Books, 2025; text
version of July 27, 2026), Chapter 11 (Arrays via Braun Trees) and
Chapter 4.

## Deviations

`acomplete` is the recursive (height, `minHeight`) characterisation;
the book's `h t ≤ mh t + 1` definition is proved equivalent
(`acomplete_iff`). `complete` is `Prop`-valued (the book has it
`bool`-valued).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib.Algorithms.Lean
namespace BraunTree

variable {α : Type u}

/-- Binary trees, the book's `'a tree` (`Leaf` = `⟨⟩`, `Node l x r` = `⟨l; x; r⟩`). -/
inductive Tree (α : Type u) where
  | Leaf : Tree α
  | Node : Tree α → α → Tree α → Tree α
deriving DecidableEq

/-- `size t` = number of nodes of `t` (the book's `|t|`). -/
def size : Tree α → ℕ
  | .Leaf => 0
  | .Node l _ r => size l + size r + 1

/-- `height t` = length of the longest root-to-leaf path (`h t`). -/
def height : Tree α → ℕ
  | .Leaf => 0
  | .Node l _ r => max (height l) (height r) + 1

/-- `minHeight t` = length of the shortest root-to-leaf path (`mh t`). -/
def minHeight : Tree α → ℕ
  | .Leaf => 0
  | .Node l _ r => min (minHeight l) (minHeight r) + 1

/-- `size Leaf = 0`. -/
@[simp] theorem size_leaf : size (Tree.Leaf : Tree α) = 0 := rfl

/-- `size (Node l x r) = size l + size r + 1`. -/
@[simp] theorem size_node (l : Tree α) (x : α) (r : Tree α) :
    size (Tree.Node l x r) = size l + size r + 1 := rfl

/-- `height Leaf = 0`. -/
@[simp] theorem height_leaf : height (Tree.Leaf : Tree α) = 0 := rfl

/-- `height (Node l x r) = max (height l) (height r) + 1`. -/
@[simp] theorem height_node (l : Tree α) (x : α) (r : Tree α) :
    height (Tree.Node l x r) = max (height l) (height r) + 1 := rfl

/-- `minHeight Leaf = 0`. -/
@[simp] theorem minHeight_leaf : minHeight (Tree.Leaf : Tree α) = 0 := rfl

/-- `minHeight (Node l x r) = min (minHeight l) (minHeight r) + 1`. -/
@[simp] theorem minHeight_node (l : Tree α) (x : α) (r : Tree α) :
    minHeight (Tree.Node l x r) = min (minHeight l) (minHeight r) + 1 := rfl

/-- `braun t`: `t` is a Braun tree (book §11.2). -/
def braun : Tree α → Prop
  | .Leaf => True
  | .Node l _ r =>
      (size l = size r ∨ size l = size r + 1) ∧ braun l ∧ braun r

/-- `acomplete t`: `t` is almost complete. At every node, the two children
are almost complete and one of: the heights are equal; the left child is
one taller and the right child is perfect (`minHeight r = height r`);
the right child is one taller and the left child is perfect. This is the
(height, minHeight) characterisation of "all leaves lie at the two
deepest levels": the old (height-diff ≤ 1 ∧ minHeight-diff ≤ 1) form is
too weak — e.g. children of shape `(h, mh) = (3, 2)` and `(2, 1)` satisfy
it, yet their parent has leaves at depths 2 and 4. -/
def acomplete : Tree α → Prop
  | .Leaf => True
  | .Node l _ r =>
      acomplete l ∧ acomplete r ∧
        ((height l = height r) ∨
         (height l = height r + 1 ∧ minHeight r = height r) ∨
         (height r = height l + 1 ∧ minHeight l = height l))

/-- `braun Leaf`. -/
theorem braun_leaf : braun (Tree.Leaf : Tree α) := trivial

/-- `acomplete Leaf`. -/
theorem acomplete_leaf : acomplete (Tree.Leaf : Tree α) := trivial

/-- `braun (Node l x r)` iff the size condition and Braun children. -/
theorem braun_node {l r : Tree α} {x : α} :
    braun (Tree.Node l x r) ↔
      (size l = size r ∨ size l = size r + 1) ∧ braun l ∧ braun r :=
  Iff.rfl

/-- `acomplete (Node l x r)` iff the height condition and almost-complete children. -/
theorem acomplete_node {l r : Tree α} {x : α} :
    acomplete (Tree.Node l x r) ↔
      acomplete l ∧ acomplete r ∧
        ((height l = height r) ∨
         (height l = height r + 1 ∧ minHeight r = height r) ∨
         (height r = height l + 1 ∧ minHeight l = height l)) :=
  Iff.rfl

/-- `size t = 0 ↔ t = Leaf`. -/
theorem size_eq_zero_iff {t : Tree α} : size t = 0 ↔ t = .Leaf := by
  cases t with
  | Leaf => simp
  | Node l x r => simp [size_node]

/-- `height t ≤ size t`. -/
theorem height_le_size {t : Tree α} : height t ≤ size t := by
  induction t with
  | Leaf => simp
  | Node l x r ihl ihr =>
    simp only [height_node, size_node]
    have h1 : height l ≤ size l := ihl
    have h2 : height r ≤ size r := ihr
    omega

/-- `height t = 0 ↔ t = Leaf`. -/
theorem height_eq_zero_iff {t : Tree α} : height t = 0 ↔ t = .Leaf := by
  cases t with
  | Leaf => simp
  | Node l x r =>
    constructor
    · intro h; simp only [height_node] at h; omega
    · intro h; nomatch h

/-- `minHeight t ≤ height t`. -/
theorem minHeight_le_height {t : Tree α} : minHeight t ≤ height t := by
  induction t with
  | Leaf => simp
  | Node l x r ihl ihr =>
    simp only [minHeight_node, height_node]
    calc min (minHeight l) (minHeight r) + 1
        ≤ minHeight l + 1 := Nat.add_le_add_right (Nat.min_le_left _ _) 1
      _ ≤ height l + 1 := Nat.add_le_add_right ihl 1
      _ ≤ max (height l) (height r) + 1 :=
          Nat.add_le_add_right (Nat.le_max_left _ _) 1

/-- A perfect tree (`minHeight = height`) has `2 ^ height` leaves. -/
theorem perfect_size {t : Tree α} (h : minHeight t = height t) :
    size t + 1 = 2 ^ height t := by
  induction t with
  | Leaf => rfl
  | Node l x r ihl ihr =>
    simp only [minHeight_node, height_node] at h
    have hminmax : min (minHeight l) (minHeight r)
        = max (height l) (height r) := by omega
    have hml : minHeight l = height l := by
      have h1 := minHeight_le_height (t := l)
      have h2 := minHeight_le_height (t := r)
      have h3 : height l ≤ max (height l) (height r) := Nat.le_max_left _ _
      have h4 : min (minHeight l) (minHeight r) ≤ minHeight l := Nat.min_le_left _ _
      omega
    have hmr : minHeight r = height r := by
      have h1 := minHeight_le_height (t := l)
      have h2 := minHeight_le_height (t := r)
      have h3 : height r ≤ max (height l) (height r) := Nat.le_max_right _ _
      have h4 : min (minHeight l) (minHeight r) ≤ minHeight r := Nat.min_le_right _ _
      omega
    have hmm : min (height l) (height r) = max (height l) (height r) := by
      rw [hml, hmr] at hminmax; exact hminmax
    have hhh : height l = height r := by
      rcases le_total (height l) (height r) with hc | hc
      · rw [Nat.min_eq_left hc, Nat.max_eq_right hc] at hmm; exact hmm
      · rw [Nat.min_eq_right hc, Nat.max_eq_left hc] at hmm; exact hmm.symm
    have ihl' := ihl hml
    have ihr' := ihr hmr
    have e : (2 : ℕ) ^ height r = 2 ^ height l := by rw [← hhh]
    have hmax : max (height l) (height r) = height l :=
      Nat.max_eq_left (le_of_eq hhh.symm)
    simp only [size_node, height_node]
    rw [hmax]
    have e2 : (2 : ℕ) ^ (height l + 1) = 2 * 2 ^ height l := by rw [pow_succ']
    omega

/-- For an almost-complete tree, `minHeight` and `height` differ by at most one. -/
theorem acomplete_minHeight_le_height {t : Tree α} (h : acomplete t) :
    minHeight t ≤ height t ∧ height t ≤ minHeight t + 1 := by
  induction t with
  | Leaf => simp
  | Node l x r ihl ihr =>
    have hc := acomplete_node.mp h
    obtain ⟨hcl, hcr, hh⟩ := hc
    have ih1 := ihl hcl
    have ih2 := ihr hcr
    simp only [height_node, minHeight_node]
    have hmax1 : min (minHeight l) (minHeight r) ≤ max (height l) (height r) := by
      rcases hh with h1 | h2 | h3
      · calc min (minHeight l) (minHeight r) ≤ minHeight l := Nat.min_le_left _ _
          _ ≤ height l := ih1.1
          _ ≤ max (height l) (height r) := Nat.le_max_left _ _
      · obtain ⟨h21, h22⟩ := h2
        calc min (minHeight l) (minHeight r) ≤ minHeight r := Nat.min_le_right _ _
          _ = height r := h22
          _ ≤ height l := by omega
          _ ≤ max (height l) (height r) := Nat.le_max_left _ _
      · obtain ⟨h31, h32⟩ := h3
        calc min (minHeight l) (minHeight r) ≤ minHeight l := Nat.min_le_left _ _
          _ = height l := h32
          _ ≤ height r := by omega
          _ ≤ max (height l) (height r) := Nat.le_max_right _ _
    have hmax2 : max (height l) (height r) ≤ min (minHeight l) (minHeight r) + 1 := by
      rcases hh with h1 | h2 | h3
      · rcases le_total (minHeight l) (minHeight r) with hmin | hmin
        · rw [Nat.min_eq_left hmin, Nat.max_eq_left (by omega : height r ≤ height l)]
          exact ih1.2
        · rw [Nat.min_eq_right hmin, Nat.max_eq_left (by omega : height r ≤ height l)]
          omega
      · obtain ⟨h21, h22⟩ := h2
        have hml : height r ≤ minHeight l := by omega
        rw [h22, Nat.min_eq_right hml, Nat.max_eq_left (by omega : height r ≤ height l)]
        omega
      · obtain ⟨h31, h32⟩ := h3
        have hmr : height l ≤ minHeight r := by omega
        rw [h32, Nat.min_eq_left hmr, Nat.max_eq_right (by omega : height l ≤ height r)]
        omega
    omega

/-- Converse direction of the book's Chapter 4 definition of `acomplete`:
`h t ≤ mh t + 1` implies `acomplete t`. The proof uses that the bound is
inherited by children (from the parent's bound), and that the heights of
siblings differ by at most one: a child whose height lagged by two would
force `mh` above `h`, contradicting `minHeight_le_height`. -/
theorem acomplete_of_height_le {t : Tree α} (h : height t ≤ minHeight t + 1) :
    acomplete t := by
  induction t with
  | Leaf => trivial
  | Node l x r ihl ihr =>
    simp only [height_node, minHeight_node] at h
    have hchild : height l ≤ minHeight l + 1 ∧ height r ≤ minHeight r + 1 := by
      rcases le_total (height l) (height r) with hc | hc
      · rw [Nat.max_eq_right hc] at h
        rcases le_total (minHeight l) (minHeight r) with hm | hm
        · rw [Nat.min_eq_left hm] at h
          constructor <;> omega
        · rw [Nat.min_eq_right hm] at h
          constructor <;> omega
      · rw [Nat.max_eq_left hc] at h
        rcases le_total (minHeight l) (minHeight r) with hm | hm
        · rw [Nat.min_eq_left hm] at h
          constructor <;> omega
        · rw [Nat.min_eq_right hm] at h
          constructor <;> omega
    have hacl := ihl hchild.1
    have hacr := ihr hchild.2
    have hdisj : (height l = height r) ∨
        (height l = height r + 1 ∧ minHeight r = height r) ∨
        (height r = height l + 1 ∧ minHeight l = height l) := by
      have hml : minHeight l ≤ height l := minHeight_le_height
      have hmr : minHeight r ≤ height r := minHeight_le_height
      rcases le_total (height l) (height r) with hc | hc
      · rcases le_total (minHeight l) (minHeight r) with hm | hm
        · rw [Nat.max_eq_right hc, Nat.min_eq_left hm] at h
          omega
        · rw [Nat.max_eq_right hc, Nat.min_eq_right hm] at h
          omega
      · rcases le_total (minHeight l) (minHeight r) with hm | hm
        · rw [Nat.max_eq_left hc, Nat.min_eq_left hm] at h
          omega
        · rw [Nat.max_eq_left hc, Nat.min_eq_right hm] at h
          omega
    exact acomplete_node.mpr ⟨hacl, hacr, hdisj⟩

/-- The book's Chapter 4 definition of almost-completeness: `acomplete t`
is `h t ≤ mh t + 1`. Our `acomplete` is the recursive (height, min-height)
characterisation at every node, which is equivalent (the bound is inherited
by children, and siblings' heights differ by at most one). -/
theorem acomplete_iff {t : Tree α} :
    acomplete t ↔ height t ≤ minHeight t + 1 :=
  ⟨fun h => (acomplete_minHeight_le_height h).2, acomplete_of_height_le⟩

/-- An almost-complete tree has at most `2 ^ height - 1` elements. -/
theorem acomplete_size_upper {t : Tree α} (h : acomplete t) :
    size t + 1 ≤ 2 ^ height t := by
  induction t with
  | Leaf => simp
  | Node l x r ihl ihr =>
    have hc := acomplete_node.mp h
    obtain ⟨hcl, hcr, -⟩ := hc
    have h1 := ihl hcl
    have h2 := ihr hcr
    simp only [size_node, height_node]
    have e1 : 2 ^ height l ≤ 2 ^ max (height l) (height r) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.le_max_left _ _)
    have e2 : 2 ^ height r ≤ 2 ^ max (height l) (height r) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.le_max_right _ _)
    have e3 : 2 ^ (max (height l) (height r) + 1) = 2 * 2 ^ max (height l) (height r) := by
      rw [pow_succ']
    omega

/-- An almost-complete tree has at least `2 ^ minHeight - 1` elements. -/
theorem acomplete_size_lower {t : Tree α} (h : acomplete t) :
    2 ^ minHeight t ≤ size t + 1 := by
  induction t with
  | Leaf => simp
  | Node l x r ihl ihr =>
    have hc := acomplete_node.mp h
    obtain ⟨hcl, hcr, -⟩ := hc
    have h1 := ihl hcl
    have h2 := ihr hcr
    simp only [size_node, minHeight_node]
    have e1 : 2 ^ min (minHeight l) (minHeight r) ≤ 2 ^ minHeight l :=
      Nat.pow_le_pow_right (by norm_num) (Nat.min_le_left _ _)
    have e2 : 2 ^ min (minHeight l) (minHeight r) ≤ 2 ^ minHeight r :=
      Nat.pow_le_pow_right (by norm_num) (Nat.min_le_right _ _)
    have e3 : 2 ^ (min (minHeight l) (minHeight r) + 1)
        = 2 * 2 ^ min (minHeight l) (minHeight r) := by
      rw [pow_succ']
    omega

/-- An almost-complete tree with the maximal size is perfect. -/
theorem perfect_complete {t : Tree α} (h : acomplete t)
    (hp : size t + 1 = 2 ^ height t) : minHeight t = height t := by
  induction t with
  | Leaf => rfl
  | Node l x r ihl ihr =>
    have hc := acomplete_node.mp h
    obtain ⟨hcl, hcr, -⟩ := hc
    have up1 := acomplete_size_upper hcl
    have up2 := acomplete_size_upper hcr
    simp only [size_node, height_node] at hp
    have e5 : (2 : ℕ) ^ (max (height l) (height r) + 1)
        = 2 * 2 ^ max (height l) (height r) := by rw [pow_succ']
    have e1 : 2 ^ height l ≤ 2 ^ max (height l) (height r) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.le_max_left _ _)
    have e2 : 2 ^ height r ≤ 2 ^ max (height l) (height r) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.le_max_right _ _)
    have hA : size l + 1 = 2 ^ max (height l) (height r) := by omega
    have hB : size r + 1 = 2 ^ max (height l) (height r) := by omega
    have hhl : height l = max (height l) (height r) := by
      by_contra hc2
      push Not at hc2
      have hle : height l ≤ max (height l) (height r) := Nat.le_max_left _ _
      have hlt : (2 : ℕ) ^ height l < 2 ^ max (height l) (height r) :=
        Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    have hhr : height r = max (height l) (height r) := by
      by_contra hc2
      push Not at hc2
      have hle : height r ≤ max (height l) (height r) := Nat.le_max_right _ _
      have hlt : (2 : ℕ) ^ height r < 2 ^ max (height l) (height r) :=
        Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    have hml : minHeight l = height l :=
      ihl hcl (by
        have e : (2 : ℕ) ^ height l = 2 ^ max (height l) (height r) :=
          congrArg (2 ^ ·) hhl
        omega)
    have hmr : minHeight r = height r :=
      ihr hcr (by
        have e : (2 : ℕ) ^ height r = 2 ^ max (height l) (height r) :=
          congrArg (2 ^ ·) hhr
        omega)
    have hhh : height l = height r := by omega
    simp only [minHeight_node, height_node]
    rw [hml, hmr, hhh]
    simp

/-- Sharp lower bound for almost-complete trees: a non-empty
almost-complete tree of height `h` has at least `2 ^ (h - 1)` nodes. -/
theorem acomplete_size_sharp {t : Tree α} (h : acomplete t) (hne : t ≠ .Leaf) :
    2 ^ (height t - 1) ≤ size t := by
  induction t with
  | Leaf => exact absurd rfl hne
  | Node l x r ihl ihr =>
    have hc := acomplete_node.mp h
    obtain ⟨hcl, hcr, hh⟩ := hc
    simp only [size_node, height_node]
    have hmax : max (height l) (height r) + 1 - 1 = max (height l) (height r) := by omega
    rw [hmax]
    rcases hh with h1 | h2 | h3
    · by_cases hzero : height l = 0
      · have hl0 : l = .Leaf := height_eq_zero_iff.mp hzero
        have hr0 : r = .Leaf := height_eq_zero_iff.mp (by omega)
        rw [hl0, hr0]; simp
      · have hln : l ≠ .Leaf := by
          intro hl'; apply hzero; rw [hl']; rfl
        have hrn : r ≠ .Leaf := by
          intro hr'; apply hzero; rw [hr'] at h1; simpa using h1
        have s1 := ihl hcl hln
        have s2 := ihr hcr hrn
        have e : (2 : ℕ) ^ height l = 2 * 2 ^ (height l - 1) := by
          conv_lhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ height l)]
          rw [pow_succ']
        have hmax2 : max (height l) (height r) = height l :=
          Nat.max_eq_left (by omega : height r ≤ height l)
        rw [hmax2]
        have e2 : (2 : ℕ) ^ (height r - 1) = 2 ^ (height l - 1) := by rw [h1]
        omega
    · obtain ⟨hhl, hmr⟩ := h2
      have hper : size r + 1 = 2 ^ height r := perfect_size hmr
      have hln : l ≠ .Leaf := by
        intro hl'; apply (show height l ≠ 0 by omega); rw [hl']; rfl
      have s1 := ihl hcl hln
      have e : (2 : ℕ) ^ height l = 2 * 2 ^ height r := by
        calc (2 : ℕ) ^ height l = 2 ^ (height r + 1) := by rw [hhl]
          _ = 2 * 2 ^ height r := by rw [pow_succ']
      have hmax2 : max (height l) (height r) = height l :=
        Nat.max_eq_left (by omega : height r ≤ height l)
      rw [hmax2]
      have e3 : height l - 1 = height r := by omega
      rw [e3] at s1
      omega
    · obtain ⟨hhr, hml⟩ := h3
      have hper : size l + 1 = 2 ^ height l := perfect_size hml
      have hrn : r ≠ .Leaf := by
        intro hr'; apply (show height r ≠ 0 by omega); rw [hr']; rfl
      have s2 := ihr hcr hrn
      have e : (2 : ℕ) ^ height r = 2 * 2 ^ height l := by
        calc (2 : ℕ) ^ height r = 2 ^ (height l + 1) := by rw [hhr]
          _ = 2 * 2 ^ height l := by rw [pow_succ']
      have hmax2 : max (height l) (height r) = height r :=
        Nat.max_eq_right (by omega : height l ≤ height r)
      rw [hmax2]
      have e3 : height r - 1 = height l := by omega
      rw [e3] at s2
      omega

/-- Lemma 11.1. `acomplete l ∧ acomplete r ∧ |l| = |r| + 1 ⟹ acomplete ⟨l; x; r⟩`. -/
theorem acomplete_node_of_size {l r : Tree α} {x : α}
    (hcl : acomplete l) (hcr : acomplete r) (hsz : size l = size r + 1) :
    acomplete (Tree.Node l x r) := by
  have hb1 := acomplete_minHeight_le_height hcl
  have hb2 := acomplete_minHeight_le_height hcr
  have up1 := acomplete_size_upper hcl
  have up2 := acomplete_size_upper hcr
  have lo1 := acomplete_size_lower hcl
  have lo2 := acomplete_size_lower hcr
  -- height bounds: hr ≤ hl ≤ hr + 1
  have hle1 : height r ≤ height l := by
    by_contra hcon
    push Not at hcon
    have e1 : (2 : ℕ) ^ height l ≤ size r + 1 := by
      calc (2 : ℕ) ^ height l ≤ 2 ^ minHeight r :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
        _ ≤ size r + 1 := lo2
    omega
  have hle2 : height l ≤ height r + 1 := by
    by_contra hcon
    push Not at hcon
    have e1 : (2 : ℕ) ^ (height r + 1) ≤ size l + 1 := by
      calc (2 : ℕ) ^ (height r + 1) ≤ 2 ^ minHeight l :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
        _ ≤ size l + 1 := lo1
    have e5 : (2 : ℕ) ^ (height r + 1) = 2 * 2 ^ height r := by rw [pow_succ']
    by_cases hzero : height r = 0
    · have h2r : (2 : ℕ) ^ height r = 1 := by simp [hzero]
      have hs1 := height_le_size (t := l)
      omega
    · have hge : (2 : ℕ) ≤ 2 ^ height r := by
        calc (2 : ℕ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ height r := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  have hhl : height l = height r ∨ height l = height r + 1 := by omega
  rcases hhl with hhl | hhl
  · exact acomplete_node.mpr ⟨hcl, hcr, Or.inl hhl⟩
  · have hmr : minHeight r = height r := by
      have hne : l ≠ .Leaf := by
        intro hle; subst hle; simp at hhl
      have hsharp := acomplete_size_sharp hcl hne
      have hle : (2 : ℕ) ^ height r ≤ size l := by
        calc (2 : ℕ) ^ height r = 2 ^ (height l - 1) := by
              have hsub : height l - 1 = height r := by omega
              rw [hsub]
          _ ≤ size l := hsharp
      have hsr : size r + 1 = 2 ^ height r := by omega
      exact perfect_complete hcr hsr
    exact acomplete_node.mpr ⟨hcl, hcr, Or.inr (Or.inl ⟨hhl, hmr⟩)⟩

/-- Braun trees of the same size have the same height and min-height
(the shape of a Braun tree is determined by its size — cf. `braun_unique`
in `Braun_Tree.thy`). Proved by strong induction on the size: the
children's sizes are forced by `braun` (the two children differ by at
most one, summing to `size - 1`), so the induction hypothesis applies
to each pair of children. -/
theorem braun_height_minHeight_unique_aux :
    ∀ n : ℕ, ∀ t t' : Tree α, size t = n → braun t → size t' = n → braun t' →
      height t = height t' ∧ minHeight t = minHeight t' := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro t t' htn ht ht'n ht'
    cases t with
    | Leaf =>
      cases t' with
      | Leaf => exact ⟨rfl, rfl⟩
      | Node l' x' r' => simp only [size] at htn ht'n; omega
    | Node l x r =>
      cases t' with
      | Leaf => simp only [size] at htn ht'n; omega
      | Node l' x' r' =>
        have hb := braun_node.mp ht
        have hb' := braun_node.mp ht'
        obtain ⟨hsz, hbl, hbr⟩ := hb
        obtain ⟨hsz', hbl', hbr'⟩ := hb'
        simp only [size_node] at htn ht'n
        -- children's sizes are forced: sl + sr = sl' + sr' = n - 1 with
        -- each pair differing by at most one, hence sl = sl', sr = sr'
        have hcl : size l = size l' := by
          rcases hsz with hsz | hsz <;> rcases hsz' with hsz' | hsz' <;> omega
        have hcr : size r = size r' := by
          rcases hsz with hsz | hsz <;> rcases hsz' with hsz' | hsz' <;> omega
        have hlt1 : size l < n := by omega
        have hlt2 : size r < n := by omega
        obtain ⟨hh1, hm1⟩ := ih (size l) hlt1 l l' rfl hbl hcl.symm hbl'
        obtain ⟨hh2, hm2⟩ := ih (size r) hlt2 r r' rfl hbr hcr.symm hbr'
        constructor
        · simp only [height_node, hh1, hh2]
        · simp only [minHeight_node, hm1, hm2]

/-- Braun trees of the same size have the same height and min-height. -/
theorem braun_height_minHeight_unique {t t' : Tree α}
    (ht : braun t) (ht' : braun t') (hsz : size t = size t') :
    height t = height t' ∧ minHeight t = minHeight t' :=
  braun_height_minHeight_unique_aux (size t) t t' rfl ht (by rw [hsz]) ht'

/-- Lemma 11.2. `braun t ⟹ acomplete t`. -/
theorem braun_acomplete {t : Tree α} (h : braun t) : acomplete t := by
  induction t with
  | Leaf => exact acomplete_leaf
  | Node l x r ihl ihr =>
    have hb := braun_node.mp h
    obtain ⟨hsz, hbl, hbr⟩ := hb
    have hcl := ihl hbl
    have hcr := ihr hbr
    rcases hsz with hsz | hsz
    · -- |l| = |r|: heights agree by uniqueness
      obtain ⟨hheq, -⟩ := braun_height_minHeight_unique hbl hbr hsz
      exact acomplete_node.mpr ⟨hcl, hcr, Or.inl hheq⟩
    · -- |l| = |r| + 1: Lemma 11.1
      exact acomplete_node_of_size hcl hcr hsz

/-- Exercise 11.1, key inequality (cf. `height_size_braun` in
`Priority_Queue_Braun.thy`): `2 ^ height t ≤ 2 * size t + 1` for Braun
trees. The full equality form of Exercise 11.1 is `braun_height_log`
below (proved from this inequality's proof together with
`acomplete_size_sharp` / `acomplete_size_upper`). -/
theorem braun_height_bound {t : Tree α} (h : braun t) :
    2 ^ height t ≤ 2 * size t + 1 := by
  -- Strengthened statement, proved by induction: the bound above, plus
  -- `2 ^ height t ≤ 2 * size t` for non-empty trees.
  have key : 2 ^ height t ≤ 2 * size t + 1 ∧
      (t ≠ .Leaf → 2 ^ height t ≤ 2 * size t) := by
    induction t with
    | Leaf => simp
    | Node l x r ihl ihr =>
      have hb := braun_node.mp h
      obtain ⟨hsz, hbl, hbr⟩ := hb
      have ih1 := ihl hbl
      have ih2 := ihr hbr
      have hmax : 2 ^ max (height l) (height r)
          = max (2 ^ height l) (2 ^ height r) := by
        rcases le_total (height l) (height r) with hc | hc
        · rw [max_eq_right hc, max_eq_right (Nat.pow_le_pow_right (by norm_num) hc)]
        · rw [max_eq_left hc, max_eq_left (Nat.pow_le_pow_right (by norm_num) hc)]
      have hsucc : (2 : ℕ) ^ (max (height l) (height r) + 1)
          = 2 * 2 ^ max (height l) (height r) := by rw [pow_succ']
      have hpow : (2 : ℕ) ^ max (height l) (height r) ≤ 2 * max (size l) (size r) + 1 := by
        calc _ = max (2 ^ height l) (2 ^ height r) := hmax
          _ ≤ max (2 * size l + 1) (2 * size r + 1) := by
              apply max_le_max
              · exact ih1.1
              · exact ih2.1
          _ = 2 * max (size l) (size r) + 1 := by
              rcases le_total (size l) (size r) with hc | hc
              · rw [max_eq_right hc, max_eq_right (show 2 * size l + 1 ≤ 2 * size r + 1 by omega)]
              · rw [max_eq_left hc, max_eq_left (show 2 * size r + 1 ≤ 2 * size l + 1 by omega)]
      simp only [height_node, size_node]
      constructor
      · -- 2^(max+1) = 2 * 2^max; if |l| = |r| use the weak bound, if
        -- |l| = |r| + 1 use the strengthened bound on the taller child
        rw [hsucc]
        rcases hsz with hsz | hsz
        · rw [Nat.max_eq_left (le_of_eq hsz.symm)] at hpow
          omega
        · rcases Nat.lt_or_ge (height l) (height r) with hc | hc
          · rw [Nat.max_eq_right (le_of_lt hc)]
            have hne : r ≠ .Leaf := by
              intro hr'; subst hr'; simp at hc
            have hstrong := ih2.2 hne
            omega
          · rw [Nat.max_eq_left hc]
            have hne : l ≠ .Leaf := by
              intro hl'; subst hl'; simp at hsz
            have hstrong := ih1.2 hne
            omega
      · intro _
        rw [hsucc]
        -- max (2^hl) (2^hr) ≤ sl + sr + 1, by cases on whether children are empty
        have c1 : 2 ^ height l ≤ 2 * size l + (if size l = 0 then 1 else 0) := by
          by_cases hz : size l = 0
          · have hleaf : l = .Leaf := size_eq_zero_iff.mp hz
            simp [hleaf]
          · have hne : l ≠ .Leaf := by
              intro hl; subst hl; simp at hz
            simp [hz, ih1.2 hne]
        have c2 : 2 ^ height r ≤ 2 * size r + (if size r = 0 then 1 else 0) := by
          by_cases hz : size r = 0
          · have hleaf : r = .Leaf := size_eq_zero_iff.mp hz
            simp [hleaf]
          · have hne : r ≠ .Leaf := by
              intro hr; subst hr; simp at hz
            simp [hz, ih2.2 hne]
        have hle_l : height l ≤ size l := height_le_size
        have hle_r : height r ≤ size r := height_le_size
        have e1 : 2 ^ height l ≤ 2 * size l + 1 := ih1.1
        have e2 : 2 ^ height r ≤ 2 * size r + 1 := ih2.1
        rw [hmax]
        rcases hsz with hsz | hsz
        · -- |l| = |r|
          by_cases hz1 : size l = 0
          · -- both sizes 0: max = 1 ≤ 1
            have hz2 : size r = 0 := by omega
            simp [size_eq_zero_iff.mp hz1, size_eq_zero_iff.mp hz2]
          · by_cases hz2 : size r = 0
            · omega
            · -- both positive: c1, c2 give 2^h ≤ 2*size, hence max ≤ 2*max ≤ sl+sr+1
              simp only [hz1, hz2, ite_false] at c1 c2
              rcases le_total (2 ^ height l) (2 ^ height r) with hc | hc
              · rw [max_eq_right hc]; omega
              · rw [max_eq_left hc]; omega
        · -- |l| = |r| + 1
          by_cases hz2 : size r = 0
          · -- r Leaf, so |l| = 1, hence height l ≤ 1
            have hsl : size l = 1 := by omega
            have hhl : height l ≤ 1 := by omega
            have hr0 : height r = 0 := by
              have : r = .Leaf := size_eq_zero_iff.mp hz2; rw [this]; rfl
            have h1r : (2 : ℕ) ^ height r = 1 := by simp [hr0]
            have hpos : 0 < (2 : ℕ) ^ height l := pow_pos (by norm_num) _
            rw [max_eq_left (by omega : 2 ^ height r ≤ 2 ^ height l)]
            have : (2 : ℕ) ^ height l ≤ 2 := by
              calc (2 : ℕ) ^ height l ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hhl
                _ = 2 := by norm_num
            omega
          · by_cases hz1 : size l = 0
            · omega
            · simp only [hz1, hz2, ite_false] at c1 c2
              rcases le_total (2 ^ height l) (2 ^ height r) with hc | hc
              · rw [max_eq_right hc]; omega
              · rw [max_eq_left hc]; omega
  exact key.1

/-- **Lemma 4.7** (Chapter 4): for a non-empty almost-complete tree, the
height is `⌊log₂ |t|⌋ + 1`, i.e. the book's `⌈log₂ (|t| + 1)⌉`. Proved
from the two-sided size bounds `2 ^ (h - 1) ≤ |t|`
(`acomplete_size_sharp`) and `|t| + 1 ≤ 2 ^ h` (`acomplete_size_upper`),
via `Nat.log2_eq_iff`. -/
theorem acomplete_height_log {t : Tree α} (h : acomplete t) (hne : t ≠ .Leaf) :
    height t = Nat.log2 (size t) + 1 := by
  have hpos : 0 < height t := by
    by_contra hc
    push Not at hc
    have hz : height t = 0 := by omega
    exact hne (height_eq_zero_iff.mp hz)
  have hsharp := acomplete_size_sharp h hne
  have hupper := acomplete_size_upper h
  have hmsize : size t ≠ 0 := by
    intro hz
    exact hne (size_eq_zero_iff.mp hz)
  have hlog : Nat.log2 (size t) = height t - 1 := by
    rw [Nat.log2_eq_iff hmsize]
    constructor
    · exact hsharp
    · have e : height t - 1 + 1 = height t := by omega
      rw [e]
      omega
  omega

/-- **Exercise 11.1**, full statement: for a non-empty Braun tree, the height is
`⌊log₂ |t|⌋ + 1`, i.e. the book's `⌈log₂ (|t| + 1)⌉` (for `|t| ≥ 1`,
`⌈log₂ (|t| + 1)⌉ = ⌊log₂ |t|⌋ + 1`). This is Lemma 4.7, since Braun
trees are almost complete. -/
theorem braun_height_log {t : Tree α} (h : braun t) (hne : t ≠ .Leaf) :
    height t = Nat.log2 (size t) + 1 :=
  acomplete_height_log (braun_acomplete h) hne

/-- **Lemma 4.8** (Chapter 4): for an almost-complete tree, the minimal
height is `⌊log₂ (|t| + 1)⌋`. If the tree is perfect (`mh = h`) then
`|t| + 1 = 2 ^ h`, so the logarithm is `h`; otherwise `mh = h - 1` and
`2 ^ (h - 1) < |t| + 1 < 2 ^ h`, so the logarithm is `h - 1` (the strict
upper bound excludes perfection via `perfect_complete`). -/
theorem acomplete_minHeight_log {t : Tree α} (h : acomplete t) :
    minHeight t = Nat.log2 (size t + 1) := by
  cases t with
  | Leaf =>
    have hlog : Nat.log2 1 = 0 := by
      rw [Nat.log2_eq_iff (by norm_num)]
      constructor <;> norm_num
    exact hlog.symm
  | Node l x r =>
    have hb := acomplete_minHeight_le_height h
    have hpos : 0 < height (Tree.Node l x r) := by
      simp only [height_node]; omega
    have hsplit : minHeight (Tree.Node l x r) = height (Tree.Node l x r) ∨
        minHeight (Tree.Node l x r) = height (Tree.Node l x r) - 1 := by omega
    rcases hsplit with hEq | hEq
    · have hper := perfect_size hEq
      have h2 : (0 : ℕ) < 2 ^ height (Tree.Node l x r) := pow_pos (by norm_num) _
      have h2ne : (2 : ℕ) ^ height (Tree.Node l x r) ≠ 0 := by omega
      have h2succ : (2 : ℕ) ^ (height (Tree.Node l x r) + 1)
          = 2 * 2 ^ height (Tree.Node l x r) := by rw [pow_succ']
      have hlog : Nat.log2 (size (Tree.Node l x r) + 1)
          = height (Tree.Node l x r) := by
        rw [hper, Nat.log2_eq_iff h2ne]
        constructor <;> omega
      omega
    · have hsharp := acomplete_size_sharp h (by simp)
      have hupper := acomplete_size_upper h
      have hlt : size (Tree.Node l x r) + 1 < 2 ^ height (Tree.Node l x r) := by
        rcases lt_or_eq_of_le hupper with hlt | heq
        · exact hlt
        · have hper : minHeight (Tree.Node l x r) = height (Tree.Node l x r) :=
            perfect_complete h heq
          omega
      have hsize_ne : size (Tree.Node l x r) + 1 ≠ 0 := by omega
      have hlog : Nat.log2 (size (Tree.Node l x r) + 1)
          = height (Tree.Node l x r) - 1 := by
        rw [Nat.log2_eq_iff hsize_ne]
        constructor
        · omega
        · have e : height (Tree.Node l x r) - 1 + 1 = height (Tree.Node l x r) := by
            omega
          rw [e]
          omega
      omega

/-- Exercise 11.3. For a Braun node, the left height is the right height
or one more: `braun ⟨l; x; r⟩ ⟹ h l = h r ∨ h l = h r + 1`. -/
theorem braun_height_children {l r : Tree α} {x : α} (h : braun (Tree.Node l x r)) :
    height l = height r ∨ height l = height r + 1 := by
  have hb := braun_node.mp h
  obtain ⟨hsz, hbl, hbr⟩ := hb
  rcases hsz with hsz | hsz
  · obtain ⟨hheq, -⟩ := braun_height_minHeight_unique hbl hbr hsz
    exact Or.inl hheq
  · have hac := @acomplete_node_of_size α l r x (braun_acomplete hbl) (braun_acomplete hbr) hsz
    have hn := acomplete_node.mp hac
    obtain ⟨-, -, hh⟩ := hn
    rcases hh with h1 | h2 | h3
    · exact Or.inl h1
    · exact Or.inr h2.1
    · obtain ⟨hhr, hml⟩ := h3
      have hper : size l + 1 = 2 ^ height l := perfect_size hml
      have hb2 := acomplete_minHeight_le_height (braun_acomplete hbr)
      have lo2 := acomplete_size_lower (braun_acomplete hbr)
      have e : (2 : ℕ) ^ height l ≤ size r + 1 := by
        calc (2 : ℕ) ^ height l ≤ 2 ^ minHeight r :=
              Nat.pow_le_pow_right (by norm_num) (by omega : height l ≤ minHeight r)
          _ ≤ size r + 1 := lo2
      omega

/-- Exercise 11.2. `lh t` = length of the left spine of `t`. -/
def lh : Tree α → ℕ
  | .Leaf => 0
  | .Node l _ _ => lh l + 1

/-- Exercise 11.2. The left height of a Braun tree equals its height. -/
theorem braun_lh_eq_height {t : Tree α} (h : braun t) : lh t = height t := by
  induction t with
  | Leaf => rfl
  | Node l x r ihl ihr =>
    have hb := braun_node.mp h
    obtain ⟨hsz, hbl, hbr⟩ := hb
    have hh := braun_height_children h
    simp only [lh, height_node]
    have ih := ihl hbl
    -- height l = height r or +1, and lh l = height l; lh (Node) = lh l + 1 = max + 1
    rcases hh with hh | hh
    · rw [Nat.max_eq_left (le_of_eq hh.symm)]; omega
    · rw [Nat.max_eq_left (by omega : height r ≤ height l)]; omega

/-- Inorder traversal (Chapter 4). -/
def inorder : Tree α → List α
  | .Leaf => []
  | .Node l x r => inorder l ++ (x :: inorder r)

/-- `(inorder t).length = size t`. -/
theorem inorder_length {t : Tree α} : (inorder t).length = size t := by
  induction t with
  | Leaf => rfl
  | Node l x r ihl ihr =>
    simp only [inorder, size_node, List.length_append, List.length_cons, ihl, ihr]
    omega

/-- `complete t`: all leaves at the same depth (Chapter 4). -/
def complete : Tree α → Prop
  | .Leaf => True
  | .Node l _ r => height l = height r ∧ complete l ∧ complete r

/-- Completeness at a node is equal heights plus complete children. -/
theorem complete_node {l r : Tree α} {x : α} :
    complete (Tree.Node l x r) ↔
      height l = height r ∧ complete l ∧ complete r :=
  Iff.rfl

/-- Every tree has at most `2 ^ height - 1` elements. -/
theorem size_add_one_le_pow_height {t : Tree α} : size t + 1 ≤ 2 ^ height t := by
  induction t with
  | Leaf => simp
  | Node l x r ihl ihr =>
    simp only [size_node, height_node]
    have hsucc : (2 : ℕ) ^ (max (height l) (height r) + 1)
        = 2 * 2 ^ max (height l) (height r) := by rw [pow_succ']
    rw [hsucc]
    have h2 : (2 : ℕ) ^ height l ≤ 2 ^ max (height l) (height r) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.le_max_left _ _)
    have h3 : (2 : ℕ) ^ height r ≤ 2 ^ max (height l) (height r) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.le_max_right _ _)
    omega

/-- Every tree has at least `2 ^ minHeight - 1` elements. -/
theorem pow_minHeight_le_size_add_one {t : Tree α} :
    2 ^ minHeight t ≤ size t + 1 := by
  induction t with
  | Leaf => simp
  | Node l x r ihl ihr =>
    simp only [minHeight_node, size_node]
    have hsucc : (2 : ℕ) ^ (min (minHeight l) (minHeight r) + 1)
        = 2 * 2 ^ min (minHeight l) (minHeight r) := by rw [pow_succ']
    rw [hsucc]
    have h2 : (2 : ℕ) ^ min (minHeight l) (minHeight r) ≤ 2 ^ minHeight l :=
      Nat.pow_le_pow_right (by norm_num) (Nat.min_le_left _ _)
    have h3 : (2 : ℕ) ^ min (minHeight l) (minHeight r) ≤ 2 ^ minHeight r :=
      Nat.pow_le_pow_right (by norm_num) (Nat.min_le_right _ _)
    omega

/-- **Lemma 4.1** (Chapter 4): a complete tree has `mh t = h t`. -/
theorem complete_minHeight_eq_height {t : Tree α} (h : complete t) :
    minHeight t = height t := by
  induction t with
  | Leaf => rfl
  | Node l x r ihl ihr =>
    obtain ⟨hheq, hcl, hcr⟩ := h
    have e1 := ihl hcl
    have e2 := ihr hcr
    simp only [minHeight_node, height_node]
    rcases min_choice (minHeight l) (minHeight r) with hm | hm <;>
    rcases max_choice (height l) (height r) with hM | hM <;>
    rw [hm, hM] <;> omega

/-- **Lemma 4.2** (Chapter 4): a complete tree has `|t| + 1 = 2 ^ h t`. -/
theorem complete_size {t : Tree α} (h : complete t) : size t + 1 = 2 ^ height t :=
  perfect_size (complete_minHeight_eq_height h)

/-- **Lemma 4.3** (Chapter 4): an incomplete tree has `|t| + 1 < 2 ^ h t`. -/
theorem not_complete_size_lt {t : Tree α} (h : ¬ complete t) :
    size t + 1 < 2 ^ height t := by
  induction t with
  | Leaf => exact absurd trivial h
  | Node l x r ihl ihr =>
    have hsize : size (Tree.Node l x r) + 1 = size l + 1 + (size r + 1) := by
      simp only [size_node]; omega
    have hheight : height (Tree.Node l x r) = max (height l) (height r) + 1 := rfl
    rw [hsize, hheight]
    by_cases hheq : height l = height r
    · have hchild : ¬ complete l ∨ ¬ complete r := by
        by_contra hc
        push Not at hc
        exact h ⟨hheq, hc.1, hc.2⟩
      have hpow : (2 : ℕ) ^ (max (height l) (height r) + 1)
          = 2 ^ height l + 2 ^ height r := by
        rw [Nat.max_eq_left (le_of_eq hheq.symm), pow_succ', ← hheq]
        omega
      rw [hpow]
      have hleft : size l + 1 ≤ 2 ^ height l := size_add_one_le_pow_height
      have hright : size r + 1 ≤ 2 ^ height r := size_add_one_le_pow_height
      rcases hchild with hc | hc
      · have hs := ihl hc; omega
      · have hs := ihr hc; omega
    · rcases le_total (height l) (height r) with hle | hle
      · have hlt : height l < height r := by omega
        have hp : (2 : ℕ) ^ height l < 2 ^ height r :=
          Nat.pow_lt_pow_right (by norm_num) hlt
        have hleft : size l + 1 ≤ 2 ^ height l := size_add_one_le_pow_height
        have hright : size r + 1 ≤ 2 ^ height r := size_add_one_le_pow_height
        rw [Nat.max_eq_right hle, pow_succ']
        omega
      · have hlt : height r < height l := by omega
        have hp : (2 : ℕ) ^ height r < 2 ^ height l :=
          Nat.pow_lt_pow_right (by norm_num) hlt
        have hleft : size l + 1 ≤ 2 ^ height l := size_add_one_le_pow_height
        have hright : size r + 1 ≤ 2 ^ height r := size_add_one_le_pow_height
        rw [Nat.max_eq_left hle, pow_succ']
        omega

/-- **Lemma 4.4** (Chapter 4): an incomplete tree has `2 ^ mh t < |t| + 1`. -/
theorem not_complete_pow_minHeight_lt {t : Tree α} (h : ¬ complete t) :
    2 ^ minHeight t < size t + 1 := by
  induction t with
  | Leaf => exact absurd trivial h
  | Node l x r ihl ihr =>
    have hsize : size (Tree.Node l x r) + 1 = size l + 1 + (size r + 1) := by
      simp only [size_node]; omega
    rw [hsize]
    by_cases hboth : complete l ∧ complete r
    · have hne : height l ≠ height r := by
        intro he; exact h ⟨he, hboth.1, hboth.2⟩
      have hml := complete_minHeight_eq_height hboth.1
      have hmr := complete_minHeight_eq_height hboth.2
      have hsl := complete_size hboth.1
      have hsr := complete_size hboth.2
      have hmh : minHeight (Tree.Node l x r) = min (height l) (height r) + 1 := by
        simp only [minHeight_node, hml, hmr]
      rw [hmh]
      have hsucc : (2 : ℕ) ^ (min (height l) (height r) + 1)
          = 2 * 2 ^ min (height l) (height r) := by rw [pow_succ']
      rw [hsucc]
      rcases le_total (height l) (height r) with hle | hle
      · rw [Nat.min_eq_left hle]
        have hlt : height l < height r := by omega
        have hp : (2 : ℕ) ^ height l < 2 ^ height r :=
          Nat.pow_lt_pow_right (by norm_num) hlt
        omega
      · rw [Nat.min_eq_right hle]
        have hlt : height r < height l := by omega
        have hp : (2 : ℕ) ^ height r < 2 ^ height l :=
          Nat.pow_lt_pow_right (by norm_num) hlt
        omega
    · push Not at hboth
      have hle1 : (2 : ℕ) ^ minHeight l ≤ size l + 1 := pow_minHeight_le_size_add_one
      have hle2 : (2 : ℕ) ^ minHeight r ≤ size r + 1 := pow_minHeight_le_size_add_one
      have hmh : minHeight (Tree.Node l x r) = min (minHeight l) (minHeight r) + 1 := by
        simp only [minHeight_node]
      rw [hmh]
      have hsucc : (2 : ℕ) ^ (min (minHeight l) (minHeight r) + 1)
          = 2 * 2 ^ min (minHeight l) (minHeight r) := by rw [pow_succ']
      rw [hsucc]
      have hm1 : (2 : ℕ) ^ min (minHeight l) (minHeight r) ≤ 2 ^ minHeight l :=
        Nat.pow_le_pow_right (by norm_num) (Nat.min_le_left _ _)
      have hm2 : (2 : ℕ) ^ min (minHeight l) (minHeight r) ≤ 2 ^ minHeight r :=
        Nat.pow_le_pow_right (by norm_num) (Nat.min_le_right _ _)
      by_cases hcl : complete l
      · have hIH := ihr (hboth hcl); omega
      · have hIH := ihl hcl; omega

/-- **Corollary 4.5** (Chapter 4): complete trees are precisely those with
`|t| + 1 = 2 ^ h t`. -/
theorem complete_iff_size {t : Tree α} : complete t ↔ size t + 1 = 2 ^ height t := by
  constructor
  · exact complete_size
  · intro h
    by_contra hc
    have hlt := not_complete_size_lt hc
    omega

/-- `complete t ↔ minHeight t = height t` (the converse of Lemma 4.1:
equal min-height and height means all leaves are at the same depth). -/
theorem complete_iff_minHeight_eq_height {t : Tree α} :
    complete t ↔ minHeight t = height t := by
  constructor
  · exact complete_minHeight_eq_height
  · intro h
    induction t with
    | Leaf => trivial
    | Node l x r ihl ihr =>
      have hml : minHeight l ≤ height l := minHeight_le_height
      have hmr : minHeight r ≤ height r := minHeight_le_height
      simp only [minHeight_node, height_node] at h
      have key : height l = height r ∧ minHeight l = height l
          ∧ minHeight r = height r := by
        rcases le_total (minHeight l) (minHeight r) with hmc | hmc <;>
        rcases le_total (height l) (height r) with hMc | hMc
        · rw [Nat.min_eq_left hmc, Nat.max_eq_right hMc] at h; omega
        · rw [Nat.min_eq_left hmc, Nat.max_eq_left hMc] at h; omega
        · rw [Nat.min_eq_right hmc, Nat.max_eq_right hMc] at h; omega
        · rw [Nat.min_eq_right hmc, Nat.max_eq_left hMc] at h; omega
      obtain ⟨hheq, e1, e2⟩ := key
      exact ⟨hheq, ihl e1, ihr e2⟩

/-- **Lemma 4.6** (Chapter 4): almost-complete trees have optimal height:
among all trees with at least as many nodes, an almost-complete one is
shortest. (The book's extra step `h s ≠ mh s` is unnecessary: `mh s < h t`
and `h s ≤ mh s + 1` already give `h s ≤ h t`.) -/
theorem acomplete_height_optimal {s t : Tree α} (hs : acomplete s)
    (hle : size s ≤ size t) : height s ≤ height t := by
  by_cases hcomp : complete s
  · have h1 := complete_size hcomp
    have h2 : size t + 1 ≤ 2 ^ height t := size_add_one_le_pow_height
    have hle2 : (2 : ℕ) ^ height s ≤ 2 ^ height t := by omega
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hle2
  · have h1 := not_complete_pow_minHeight_lt hcomp
    have h2 : size t + 1 ≤ 2 ^ height t := size_add_one_le_pow_height
    have h3 := (acomplete_minHeight_le_height hs).2
    have hlt : minHeight s < height t := by
      by_contra hge
      push Not at hge
      have hle2 : (2 : ℕ) ^ height t ≤ 2 ^ minHeight s :=
        Nat.pow_le_pow_right (by norm_num) hge
      omega
    omega

/-- **Exercise 4.8.** `acomplete ⟨l; x; r⟩` is the formula `B` built from
`acomplete`, `complete`, `h`, arithmetic and Boolean operations only:
the two children are almost complete, and either their heights are equal
or the taller side's sibling subtree is complete. -/
theorem acomplete_node_iff {l r : Tree α} {x : α} :
    acomplete (Tree.Node l x r) ↔
      acomplete l ∧ acomplete r ∧
        ((height l = height r) ∨
         (height l = height r + 1 ∧ complete r) ∨
         (height r = height l + 1 ∧ complete l)) := by
  rw [acomplete_node]
  constructor
  · rintro ⟨hcl, hcr, hdisj⟩
    refine ⟨hcl, hcr, ?_⟩
    rcases hdisj with h1 | ⟨h21, h22⟩ | ⟨h31, h32⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl ⟨h21, complete_iff_minHeight_eq_height.mpr h22⟩)
    · exact Or.inr (Or.inr ⟨h31, complete_iff_minHeight_eq_height.mpr h32⟩)
  · rintro ⟨hcl, hcr, hdisj⟩
    refine ⟨hcl, hcr, ?_⟩
    rcases hdisj with h1 | ⟨h21, h22⟩ | ⟨h31, h32⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl ⟨h21, complete_iff_minHeight_eq_height.mp h22⟩)
    · exact Or.inr (Or.inr ⟨h31, complete_iff_minHeight_eq_height.mp h32⟩)

end BraunTree
end Cslib.Algorithms.Lean
