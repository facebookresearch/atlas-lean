/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Basic.Real.Basic
public import Mathlib.Logic.Relation
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Pedigree kinship: gene dropping, Malécot's recursion and Wright's path formula

On a finite pedigree (numbered so that parents precede children), gene dropping assigns every
non-founder gene copy a fair Mendelian coin choosing one of the two copies of the corresponding
parent; founder copies are distinct (founders are unrelated and not inbred). The probability
that two copies descend from the same founder copy is their probability of identity by descent.
Kinship and inbreeding under gene dropping satisfy Malécot's recursion
`φ_ij = (φ_{i,f(j)} + φ_{i,m(j)}) / 2` for `j` not an ancestor of `i`, `φ_ii = (1 + F_i) / 2` and
`F_i = φ_{f(i),m(i)}`, and therefore agree with the tabular method `Pedigree.kinship`. On a
pedigree without selfing, the tabular kinship equals Wright's path formula
`F_i = Σ (1/2)^{n₁ + n₂ + 1} (1 + F_A)`, the sum over common ancestors `A` of the parents and
pairs of ancestral paths from the parents to `A` that meet only at `A`.

## Main results

* `Pedigree`, `Pedigree.origin`, `Pedigree.ibd`, `Pedigree.geneDropKinship`,
  `Pedigree.inbreeding`: gene dropping on a finite pedigree.
* `Pedigree.geneDropKinship_of_parents_eq_some`, `Pedigree.geneDropKinship_of_parents_eq_none`,
  `Pedigree.geneDropKinship_self`, `Pedigree.inbreeding_of_parents_eq_some`: Malécot's
  recursion under gene dropping.
* `Pedigree.kinship`, `Pedigree.geneDropKinship_eq_kinship`,
  `Pedigree.inbreeding_eq_kinshipInbreeding`: the tabular method computes the gene-dropping
  kinship and inbreeding.
* `Pedigree.kinship_eq_sum_paths`, `Pedigree.inbreeding_eq_sum_paths`: Wright's path formula.

## References

* S. Wright, *Coefficients of inbreeding and relationship*, Am. Nat. 56 (1922), 330–338.
* G. Malécot, *Les mathématiques de l'hérédité*, Masson, Paris, 1948.
* K. Lange, *Mathematical and Statistical Methods for Genetic Analysis*, 2nd ed., Springer,
  2002, ch. 5.
-/

@[expose] public section

namespace MathlibExt.Biology.StatisticalGenetics.Kinship

/-- A pedigree on the individuals `Fin n`, numbered so that parents precede their children
(every finite pedigree, a finite DAG, has such a numbering). `parents i = some g` means that
`g 0` is the father and `g 1` the mother of `i`; `parents i = none` means that `i` is a founder.
Founders are unrelated and not inbred (their `2 n_F` gene copies are distinct). -/
structure Pedigree (n : ℕ) where
  /-- The parents `(g 0, g 1)` = (father, mother) of a non-founder; `none` for a founder. -/
  parents : Fin n → Option (Fin 2 → Fin n)
  /-- Parents precede their children. -/
  parents_lt : ∀ i g, parents i = some g → ∀ k, g k < i

namespace Pedigree

variable {n : ℕ} (P : Pedigree n)

/-- `a` is a parent of `b`. -/
def IsParent (a b : Fin n) : Prop := ∃ g, P.parents b = some g ∧ ∃ k, g k = a

/-- `a` is an ancestor of `b` (a parent, a parent of a parent, …). -/
def IsAncestor : Fin n → Fin n → Prop := Relation.TransGen P.IsParent

/-- No individual is the offspring of a selfing (father ≠ mother), as in Wright's setting of a
bisexual population. -/
def NoSelfing : Prop := ∀ i g, P.parents i = some g → g 0 ≠ g 1

/-! ### Gene dropping -/

/-- A gene-dropping outcome: `ω i k` is the Mendelian coin of the copy `(i, k)` (`k = 0` the
paternal copy, `k = 1` the maternal copy), saying which copy (`0` or `1`) of the parent `g k`
of `i` it inherits. Under gene dropping all `4 ^ n` outcomes are equally likely. -/
abbrev Coins (n : ℕ) : Type := Fin n → Fin 2 → Fin 2

/-- The founder copy from which the gene copy `c = (i, k)` descends under the gene-dropping
outcome `ω`: a founder copy is its own origin; a copy of a non-founder descends from the copy
`ω i k` of its parent `g k`. -/
def origin (ω : Coins n) (c : Fin n × Fin 2) : Fin n × Fin 2 :=
  match _h : P.parents c.1 with
  | none => c
  | some g => origin ω (g c.2, ω c.1 c.2)
termination_by c.1.val
decreasing_by exact P.parents_lt c.1 g _h c.2

/-- The probability, under gene dropping (independent fair Mendelian coins), that the gene
copies `c` and `d` are identical by descent, i.e. descend from the same founder copy. -/
noncomputable def ibd (c d : Fin n × Fin 2) : ℝ :=
  ((Finset.univ.filter fun ω : Coins n => P.origin ω c = P.origin ω d).card : ℝ) / 4 ^ n

/-- The kinship (coancestry) coefficient under gene dropping: the probability that a copy drawn
at random from `i` and a copy drawn at random from `j` are identical by descent. -/
noncomputable def geneDropKinship (i j : Fin n) : ℝ :=
  (∑ a : Fin 2, ∑ b : Fin 2, P.ibd (i, a) (j, b)) / 4

/-- The inbreeding coefficient under gene dropping: the probability that the two copies of `i`
are identical by descent. -/
noncomputable def inbreeding (i : Fin n) : ℝ := P.ibd (i, 0) (i, 1)

/-! ### Malécot's recursion (the tabular method) -/

/-- The kinship coefficient by Malécot's recursion, computed in the order of the numbering
(the tabular method): for `i < j`, `φ i j = (φ i f + φ i m) / 2` with `f, m` the parents of `j`
and `φ i j = 0` if `j` is a founder; `φ i i = (1 + φ f m) / 2` with `f, m` the parents of `i`
and `φ i i = 1 / 2` for a founder; symmetric for `j < i`. -/
noncomputable def kinship (i j : Fin n) : ℝ :=
  if _hji : j < i then
    match h : P.parents i with
    | none => 0
    | some g => (kinship (g 0) j + kinship (g 1) j) / 2
  else if _hij : i < j then
    match h : P.parents j with
    | none => 0
    | some g => (kinship i (g 0) + kinship i (g 1)) / 2
  else
    match h : P.parents i with
    | none => 1 / 2
    | some g => (1 + kinship (g 0) (g 1)) / 2
termination_by i.val + j.val
decreasing_by
  all_goals
    have h0 := P.parents_lt _ g h 0
    have h1 := P.parents_lt _ g h 1
    simp only [Fin.lt_def, not_lt] at *
    omega

/-- The inbreeding coefficient by Malécot's recursion: `F i = φ f m` for the parents `f, m` of
`i`, and `F i = 0` for a founder. -/
noncomputable def kinshipInbreeding (i : Fin n) : ℝ :=
  match P.parents i with
  | none => 0
  | some g => P.kinship (g 0) (g 1)

/-- The tabular recursion for `i < j` with `j` a non-founder. -/
theorem kinship_of_lt_of_parents_eq_some {i j : Fin n} {g : Fin 2 → Fin n} (hij : i < j)
    (h : P.parents j = some g) :
    P.kinship i j = (P.kinship i (g 0) + P.kinship i (g 1)) / 2 := by
  rw [kinship, dite_eq_right (not_lt.mpr hij.le), dite_eq_left hij]
  split <;> simp_all

/-- The tabular recursion for `i < j` with `j` a founder. -/
theorem kinship_of_lt_of_parents_eq_none {i j : Fin n} (hij : i < j)
    (h : P.parents j = none) : P.kinship i j = 0 := by
  rw [kinship, dite_eq_right (not_lt.mpr hij.le), dite_eq_left hij]
  split <;> simp_all

/-- The tabular recursion on the diagonal for a non-founder: `φ i i = (1 + φ f m) / 2`. -/
theorem kinship_self_of_parents_eq_some {i : Fin n} {g : Fin 2 → Fin n}
    (h : P.parents i = some g) : P.kinship i i = (1 + P.kinship (g 0) (g 1)) / 2 := by
  rw [kinship, dite_eq_right (lt_irrefl i), dite_eq_right (lt_irrefl i)]
  split <;> simp_all

/-- The tabular recursion on the diagonal for a founder: `φ i i = 1 / 2`. -/
theorem kinship_self_of_parents_eq_none {i : Fin n} (h : P.parents i = none) :
    P.kinship i i = 1 / 2 := by
  rw [kinship, dite_eq_right (lt_irrefl i), dite_eq_right (lt_irrefl i)]
  split <;> simp_all

/-- The tabular recursion for `j < i` with `i` a non-founder. -/
theorem kinship_of_gt_of_parents_eq_some {i j : Fin n} {g : Fin 2 → Fin n} (hji : j < i)
    (h : P.parents i = some g) :
    P.kinship i j = (P.kinship (g 0) j + P.kinship (g 1) j) / 2 := by
  rw [kinship, dite_eq_left hji]
  split <;> simp_all

/-- The tabular recursion for `j < i` with `i` a founder. -/
theorem kinship_of_gt_of_parents_eq_none {i j : Fin n} (hji : j < i)
    (h : P.parents i = none) : P.kinship i j = 0 := by
  rw [kinship, dite_eq_left hji]
  split <;> simp_all

/-- The tabular kinship is symmetric. -/
theorem kinship_comm (i j : Fin n) : P.kinship i j = P.kinship j i := by
  induction hs : i.val + j.val using Nat.strong_induction_on generalizing i j with
  | _ s ih =>
  rcases lt_trichotomy i j with hij | rfl | hij
  · cases hp : P.parents j with
    | none =>
      rw [P.kinship_of_lt_of_parents_eq_none hij hp, P.kinship_of_gt_of_parents_eq_none hij hp]
    | some g =>
      have h0 := P.parents_lt j g hp 0
      have h1 := P.parents_lt j g hp 1
      rw [P.kinship_of_lt_of_parents_eq_some hij hp, P.kinship_of_gt_of_parents_eq_some hij hp,
        ih _ (by rw [← hs]; simp only [Fin.lt_def] at h0; omega) i (g 0) rfl,
        ih _ (by rw [← hs]; simp only [Fin.lt_def] at h1; omega) i (g 1) rfl]
  · rfl
  · cases hp : P.parents i with
    | none =>
      rw [P.kinship_of_lt_of_parents_eq_none hij hp, P.kinship_of_gt_of_parents_eq_none hij hp]
    | some g =>
      have h0 := P.parents_lt i g hp 0
      have h1 := P.parents_lt i g hp 1
      rw [P.kinship_of_lt_of_parents_eq_some hij hp, P.kinship_of_gt_of_parents_eq_some hij hp,
        ih _ (by rw [← hs]; simp only [Fin.lt_def] at h0; omega) (g 0) j rfl,
        ih _ (by rw [← hs]; simp only [Fin.lt_def] at h1; omega) (g 1) j rfl]

/-! ### Wright's path formula -/

/-- The ancestral paths from `i`: the lists `[i = v₀, v₁, …, v_k]` with each `v_{t+1}` a parent
of `v_t` (`k ≥ 0`; the path `[i]` has no edge). -/
noncomputable def ancPaths (i : Fin n) : Finset (List (Fin n)) :=
  match h : P.parents i with
  | none => {[i]}
  | some g => insert [i] (Finset.univ.biUnion fun k : Fin 2 =>
      (ancPaths (g k)).image (List.cons i))
termination_by i.val
decreasing_by exact P.parents_lt i g h k

/-- The ancestral paths from `i` that end at `A`. -/
noncomputable def pathsTo (i A : Fin n) : Finset (List (Fin n)) :=
  (P.ancPaths i).filter fun p => p.getLast? = some A

/-- Every path in `ancPaths i` starts at `i` and is nonempty. -/
theorem head?_of_mem_ancPaths {i : Fin n} {p : List (Fin n)} (hp : p ∈ P.ancPaths i) :
    p.head? = some i := by
  rw [ancPaths] at hp
  split at hp
  · simp_all
  · simp only [Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finset.mem_image] at hp
    rcases hp with rfl | ⟨k, q, -, rfl⟩ <;> rfl

/-! ### Gene dropping: basic facts -/

/-- There are `4 ^ n` gene-dropping outcomes. -/
private theorem card_coins : Fintype.card (Coins n) = 4 ^ n := by
  simp [Coins]

/-- A founder copy is its own origin. -/
theorem origin_of_parents_eq_none {c : Fin n × Fin 2} (h : P.parents c.1 = none) (ω : Coins n) :
    P.origin ω c = c := by
  rw [origin]; split <;> simp_all

/-- A copy of a non-founder descends from the chosen copy of the corresponding parent. -/
theorem origin_of_parents_eq_some {c : Fin n × Fin 2} {g : Fin 2 → Fin n}
    (h : P.parents c.1 = some g) (ω : Coins n) :
    P.origin ω c = P.origin ω (g c.2, ω c.1 c.2) := by
  rw [origin]; split <;> simp_all

/-- Ancestors precede their descendants. -/
theorem IsAncestor.lt {a b : Fin n} (h : P.IsAncestor a b) : a < b := by
  induction h with
  | single h => obtain ⟨g, hg, k, rfl⟩ := h; exact P.parents_lt _ g hg k
  | tail _ h ih => obtain ⟨g, hg, k, rfl⟩ := h; exact ih.trans (P.parents_lt _ g hg k)

/-- A parent is an ancestor. -/
theorem isAncestor_of_parents_eq_some {i : Fin n} {g : Fin 2 → Fin n}
    (h : P.parents i = some g) (k : Fin 2) : P.IsAncestor (g k) i :=
  Relation.TransGen.single ⟨g, h, k, rfl⟩

/-- The origin of a copy of `i` depends only on the coins of `i` and its ancestors. -/
private theorem origin_congr {ω ω' : Coins n} (i : Fin n)
    (hω : ∀ x, (x = i ∨ P.IsAncestor x i) → ω x = ω' x) (k : Fin 2) :
    P.origin ω (i, k) = P.origin ω' (i, k) := by
  induction i using WellFoundedLT.induction generalizing k with
  | _ i ih =>
  cases h : P.parents i with
  | none =>
    rw [P.origin_of_parents_eq_none (c := (i, k)) h, P.origin_of_parents_eq_none (c := (i, k)) h]
  | some g =>
    rw [P.origin_of_parents_eq_some (c := (i, k)) h, P.origin_of_parents_eq_some (c := (i, k)) h]
    simp only
    rw [hω i (Or.inl rfl)]
    have hg := P.isAncestor_of_parents_eq_some h k
    refine ih (g k) (P.parents_lt i g h k) (fun x hx => hω x ?_) _
    rcases hx with rfl | hx
    · exact Or.inr hg
    · exact Or.inr (hx.trans hg)

/-- The origin of a copy of `i` is a copy of `i` or of an ancestor of `i`. -/
private theorem origin_fst (ω : Coins n) (i : Fin n) (k : Fin 2) :
    (P.origin ω (i, k)).1 = i ∨ P.IsAncestor (P.origin ω (i, k)).1 i := by
  induction i using WellFoundedLT.induction generalizing k with
  | _ i ih =>
  cases h : P.parents i with
  | none => left; rw [P.origin_of_parents_eq_none (c := (i, k)) h]
  | some g =>
    rw [P.origin_of_parents_eq_some (c := (i, k)) h]
    have hg := P.isAncestor_of_parents_eq_some h k
    rcases ih (g k) (P.parents_lt i g h k) (ω i k) with h' | h'
    · right; rw [h']; exact hg
    · right; exact h'.trans hg

/-- Flip the coin at position `(x, l)`. -/
private def flip (x : Fin n) (l : Fin 2) (ω : Coins n) : Coins n :=
  fun y m => if y = x ∧ m = l then 1 - ω y m else ω y m

private theorem flip_flip (x : Fin n) (l : Fin 2) (ω : Coins n) : flip x l (flip x l ω) = ω := by
  funext y m
  by_cases h : y = x ∧ m = l
  · simp only [flip, h, and_self, ite_true]; omega
  · simp [flip, h]

private theorem flip_apply_self (x : Fin n) (l : Fin 2) (ω : Coins n) :
    flip x l ω x l = 1 - ω x l := by simp [flip]

private theorem flip_apply_of_ne {x y : Fin n} (l : Fin 2) (ω : Coins n) (h : y ≠ x) :
    flip x l ω y = ω y := by
  funext m; simp [flip, h]

/-- Halving: for an event `E` invariant under flipping the coin `(x, l)`, the outcomes in `E`
with coin value `c` are half of `E`. -/
private theorem card_filter_coin (x : Fin n) (l : Fin 2) (E : Coins n → Prop) [DecidablePred E]
    (hE : ∀ ω, E (flip x l ω) ↔ E ω) (c : Fin 2) :
    2 * (Finset.univ.filter fun ω => ω x l = c ∧ E ω).card =
      (Finset.univ.filter fun ω => E ω).card := by
  have hbij : ∀ c : Fin 2, (Finset.univ.filter fun ω : Coins n => ω x l = c ∧ E ω).card =
      (Finset.univ.filter fun ω : Coins n => ω x l = 1 - c ∧ E ω).card := by
    intro c
    refine Finset.card_nbij' (flip x l) (flip x l) ?_ ?_ ?_ ?_
    · intro ω hω
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hω ⊢
      rw [flip_apply_self, hω.1, hE]; exact ⟨rfl, hω.2⟩
    · intro ω hω
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hω ⊢
      rw [flip_apply_self, hω.1, hE]; refine ⟨?_, hω.2⟩; omega
    · intro ω _; exact flip_flip x l ω
    · intro ω _; exact flip_flip x l ω
  have hsplit : (Finset.univ.filter fun ω : Coins n => E ω).card =
      (Finset.univ.filter fun ω : Coins n => ω x l = 0 ∧ E ω).card +
        (Finset.univ.filter fun ω : Coins n => ω x l = 1 ∧ E ω).card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1; ext ω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      constructor
      · intro h; rcases Fin.exists_fin_two.mp ⟨ω x l, rfl⟩ with h' | h'
        · exact Or.inl ⟨h', h⟩
        · exact Or.inr ⟨h', h⟩
      · rintro (h | h) <;> exact h.2
    · rw [Finset.disjoint_filter]; intro ω _ h1 h2; rw [h1.1] at h2; exact absurd h2.1 (by decide)
  rw [hsplit]
  rcases Fin.exists_fin_two.mp ⟨c, rfl⟩ with rfl | rfl
  · rw [hbij 0]; simp; ring
  · rw [hbij 1]; simp; ring


/-- Splitting the outcomes by the value of one coin. -/
private theorem card_filter_split (x : Fin n) (l : Fin 2) (F : Fin 2 → Coins n → Prop)
    [∀ c, DecidablePred (F c)] :
    (Finset.univ.filter fun ω : Coins n => F (ω x l) ω).card =
      (Finset.univ.filter fun ω : Coins n => ω x l = 0 ∧ F 0 ω).card +
        (Finset.univ.filter fun ω : Coins n => ω x l = 1 ∧ F 1 ω).card := by
  rw [← Finset.card_union_of_disjoint]
  · congr 1; ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro h; rcases Fin.exists_fin_two.mp ⟨ω x l, rfl⟩ with h' | h'
      · exact Or.inl ⟨h', h' ▸ h⟩
      · exact Or.inr ⟨h', h' ▸ h⟩
    · rintro (h | h) <;> (rw [h.1]; exact h.2)
  · rw [Finset.disjoint_filter]; intro ω _ h1 h2; rw [h1.1] at h2; exact absurd h2.1 (by decide)

private theorem flip_eq_of_lt {x i : Fin n} (l : Fin 2) (ω : Coins n) (hxi : i < x)
    (k : Fin 2) : P.origin (flip x l ω) (i, k) = P.origin ω (i, k) := by
  refine P.origin_congr i (fun y hy => flip_apply_of_ne l ω ?_) k
  rcases hy with rfl | hy
  · exact hxi.ne
  · exact (hy.lt.trans hxi).ne

/-! ### Gene dropping satisfies Malécot's recursion -/

/-- Two copies are identical by descent of themselves with probability `1`. -/
theorem ibd_self (c : Fin n × Fin 2) : P.ibd c c = 1 := by
  have h : (4 : ℝ) ^ n ≠ 0 := by positivity
  simp only [ibd, Finset.filter_true, Finset.card_univ, card_coins]
  push_cast
  exact div_self h

/-- Identity by descent is symmetric. -/
theorem ibd_comm (c d : Fin n × Fin 2) : P.ibd c d = P.ibd d c := by
  simp only [ibd, eq_comm]

/-- One step of Malécot's recursion for identity by descent. -/
theorem ibd_of_parents_eq_some {i j : Fin n} {g : Fin 2 → Fin n} (hij : j ≠ i)
    (hanc : ¬ P.IsAncestor j i) (h : P.parents j = some g) (a b : Fin 2) :
    P.ibd (i, a) (j, b) = (P.ibd (i, a) (g b, 0) + P.ibd (i, a) (g b, 1)) / 2 := by
  have hcongr : ∀ ω, P.origin (flip j b ω) (i, a) = P.origin ω (i, a) := fun ω =>
    P.origin_congr i (fun y hy => flip_apply_of_ne b ω (by
      rintro rfl; rcases hy with rfl | hy
      · exact hij rfl
      · exact hanc hy)) a
  have hE : ∀ c : Fin 2, ∀ ω, (P.origin (flip j b ω) (i, a) = P.origin (flip j b ω) (g b, c) ↔
      P.origin ω (i, a) = P.origin ω (g b, c)) := by
    intro c ω
    rw [hcongr, P.flip_eq_of_lt b ω (P.parents_lt j g h b)]
  have hrw : (Finset.univ.filter fun ω : Coins n => P.origin ω (i, a) = P.origin ω (j, b)) =
      Finset.univ.filter fun ω : Coins n => P.origin ω (i, a) = P.origin ω (g b, ω j b) := by
    ext ω; simp [P.origin_of_parents_eq_some (c := (j, b)) h]
  have h0 := card_filter_coin j b (fun ω => P.origin ω (i, a) = P.origin ω (g b, 0)) (hE 0) 0
  have h1 := card_filter_coin j b (fun ω => P.origin ω (i, a) = P.origin ω (g b, 1)) (hE 1) 1
  have hs := card_filter_split j b (fun c ω => P.origin ω (i, a) = P.origin ω (g b, c))
  simp only [ibd, hrw]
  rw [hs, ← h0, ← h1]
  have h4 : (4 : ℝ) ^ n ≠ 0 := by positivity
  push_cast
  field_simp

/-- `φ i i = (1 + F i) / 2` under gene dropping. -/
theorem geneDropKinship_self (i : Fin n) :
    P.geneDropKinship i i = (1 + P.inbreeding i) / 2 := by
  simp only [geneDropKinship, inbreeding, Fin.sum_univ_two, P.ibd_self, P.ibd_comm (i, 1) (i, 0)]
  ring

/-- The inbreeding coefficient of a founder is `0`. -/
theorem inbreeding_of_parents_eq_none {i : Fin n} (h : P.parents i = none) :
    P.inbreeding i = 0 := by
  have : (Finset.univ.filter fun ω : Coins n => P.origin ω (i, 0) = P.origin ω (i, 1)) = ∅ := by
    ext ω
    simp [P.origin_of_parents_eq_none (c := (i, 0)) h, P.origin_of_parents_eq_none (c := (i, 1)) h]
  simp [inbreeding, ibd, this]

/-- **Malécot**: the inbreeding coefficient of `i` is the kinship of its parents,
`F i = φ f m`, under gene dropping. -/
theorem inbreeding_of_parents_eq_some {i : Fin n} {g : Fin 2 → Fin n}
    (h : P.parents i = some g) : P.inbreeding i = P.geneDropKinship (g 0) (g 1) := by
  have hl : ∀ (l : Fin 2) (k : Fin 2) (c : Fin 2) ω,
      P.origin (flip i l ω) (g k, c) = P.origin ω (g k, c) :=
    fun l k c ω => P.flip_eq_of_lt l ω (P.parents_lt i g h k) c
  have hrw : (Finset.univ.filter fun ω : Coins n => P.origin ω (i, 0) = P.origin ω (i, 1)) =
      Finset.univ.filter fun ω : Coins n =>
        P.origin ω (g 0, ω i 0) = P.origin ω (g 1, ω i 1) := by
    ext ω
    simp [P.origin_of_parents_eq_some (c := (i, 0)) h, P.origin_of_parents_eq_some (c := (i, 1)) h]
  -- split on the second coin, then the first
  have hinner : ∀ c0 : Fin 2,
      2 * (Finset.univ.filter fun ω : Coins n => ω i 0 = c0 ∧
        P.origin ω (g 0, c0) = P.origin ω (g 1, ω i 1)).card =
      (Finset.univ.filter fun ω : Coins n => ω i 1 = 0 ∧
        P.origin ω (g 0, c0) = P.origin ω (g 1, 0)).card +
      (Finset.univ.filter fun ω : Coins n => ω i 1 = 1 ∧
        P.origin ω (g 0, c0) = P.origin ω (g 1, 1)).card := by
    intro c0
    rw [card_filter_coin i 0 (fun ω => P.origin ω (g 0, c0) = P.origin ω (g 1, ω i 1)) ?_ c0]
    · exact card_filter_split i 1 (fun c ω => P.origin ω (g 0, c0) = P.origin ω (g 1, c))
    · intro ω
      rw [hl, hl, show flip i 0 ω i 1 = ω i 1 by simp [flip]]
  have hcoin : ∀ c0 c1 : Fin 2,
      2 * (Finset.univ.filter fun ω : Coins n => ω i 1 = c1 ∧
        P.origin ω (g 0, c0) = P.origin ω (g 1, c1)).card =
      (Finset.univ.filter fun ω : Coins n => P.origin ω (g 0, c0) = P.origin ω (g 1, c1)).card :=
    fun c0 c1 => card_filter_coin i 1 _ (fun ω => by rw [hl, hl]) c1
  have hs := card_filter_split i 0
    (fun c ω => P.origin ω (g 0, c) = P.origin ω (g 1, ω i 1))
  have key : (4 * (Finset.univ.filter fun ω : Coins n =>
        P.origin ω (g 0, ω i 0) = P.origin ω (g 1, ω i 1)).card : ℝ) =
      ∑ c0 : Fin 2, ∑ c1 : Fin 2,
        ((Finset.univ.filter fun ω : Coins n =>
          P.origin ω (g 0, c0) = P.origin ω (g 1, c1)).card : ℝ) := by
    have e := congrArg (fun m : ℕ => (m : ℝ)) (congrArg (4 * ·) hs)
    simp only [Fin.sum_univ_two]
    have i0 := congrArg (fun m : ℕ => (m : ℝ)) (hinner 0)
    have i1 := congrArg (fun m : ℕ => (m : ℝ)) (hinner 1)
    have c00 := congrArg (fun m : ℕ => (m : ℝ)) (hcoin 0 0)
    have c01 := congrArg (fun m : ℕ => (m : ℝ)) (hcoin 0 1)
    have c10 := congrArg (fun m : ℕ => (m : ℝ)) (hcoin 1 0)
    have c11 := congrArg (fun m : ℕ => (m : ℝ)) (hcoin 1 1)
    push_cast at e i0 i1 c00 c01 c10 c11 ⊢
    linarith
  simp only [inbreeding, geneDropKinship, ibd, hrw, Fin.sum_univ_two]
  simp only [Fin.sum_univ_two] at key
  have h4 : (4 : ℝ) ^ n ≠ 0 := by positivity
  field_simp
  linarith

/-- **Malécot's recursion** under gene dropping: if `j ≠ i` is not an ancestor of `i` and has
parents `f, m`, then `φ i j = (φ i f + φ i m) / 2`. -/
theorem geneDropKinship_of_parents_eq_some {i j : Fin n} {g : Fin 2 → Fin n} (hij : j ≠ i)
    (hanc : ¬ P.IsAncestor j i) (h : P.parents j = some g) :
    P.geneDropKinship i j = (P.geneDropKinship i (g 0) + P.geneDropKinship i (g 1)) / 2 := by
  simp only [geneDropKinship, Fin.sum_univ_two, P.ibd_of_parents_eq_some hij hanc h]
  ring

/-- A founder `j ≠ i` that is not an ancestor of `i` has kinship `0` with `i`. -/
theorem geneDropKinship_of_parents_eq_none {i j : Fin n} (hij : j ≠ i)
    (hanc : ¬ P.IsAncestor j i) (h : P.parents j = none) : P.geneDropKinship i j = 0 := by
  have h0 : ∀ a b : Fin 2, P.ibd (i, a) (j, b) = 0 := by
    intro a b
    have : (Finset.univ.filter fun ω : Coins n => P.origin ω (i, a) = P.origin ω (j, b)) = ∅ := by
      ext ω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
        P.origin_of_parents_eq_none (c := (j, b)) h]
      intro he
      rcases P.origin_fst ω i a with h' | h' <;> rw [he] at h'
      · exact hij h'
      · exact hanc h'
    simp [ibd, this]
  simp [geneDropKinship, h0]

/-- Gene-dropping kinship is symmetric. -/
theorem geneDropKinship_comm (i j : Fin n) : P.geneDropKinship i j = P.geneDropKinship j i := by
  simp only [geneDropKinship, Fin.sum_univ_two, P.ibd_comm (i, _) (j, _)]
  ring

/-- The kinship coefficient computed by Malécot's recursion is the probability of identity by
descent under gene dropping. -/
theorem geneDropKinship_eq_kinship (i j : Fin n) :
    P.geneDropKinship i j = P.kinship i j := by
  induction hs : i.val + j.val using Nat.strong_induction_on generalizing i j with
  | _ s ih =>
  have lt0 : ∀ {x : Fin n} {g : Fin 2 → Fin n}, P.parents x = some g → ∀ k, (g k).val < x.val :=
    fun h k => P.parents_lt _ _ h k
  rcases lt_trichotomy i j with hij | rfl | hij
  · have hne : j ≠ i := hij.ne'
    have hanc : ¬ P.IsAncestor j i := fun h => (lt_asymm h.lt hij)
    cases hp : P.parents j with
    | none =>
      rw [P.geneDropKinship_of_parents_eq_none hne hanc hp,
        P.kinship_of_lt_of_parents_eq_none hij hp]
    | some g =>
      rw [P.geneDropKinship_of_parents_eq_some hne hanc hp,
        P.kinship_of_lt_of_parents_eq_some hij hp,
        ih _ (by have := lt0 hp 0; omega) i (g 0) rfl,
        ih _ (by have := lt0 hp 1; omega) i (g 1) rfl]
  · cases hp : P.parents i with
    | none =>
      rw [P.geneDropKinship_self, P.inbreeding_of_parents_eq_none hp,
        P.kinship_self_of_parents_eq_none hp]
      norm_num
    | some g =>
      rw [P.geneDropKinship_self, P.inbreeding_of_parents_eq_some hp,
        P.kinship_self_of_parents_eq_some hp,
        ih _ (by have := lt0 hp 0; have := lt0 hp 1; omega) (g 0) (g 1) rfl]
  · have hne : i ≠ j := hij.ne'
    have hanc : ¬ P.IsAncestor i j := fun h => (lt_asymm h.lt hij)
    rw [P.geneDropKinship_comm]
    cases hp : P.parents i with
    | none =>
      rw [P.geneDropKinship_of_parents_eq_none hne hanc hp,
        P.kinship_of_gt_of_parents_eq_none hij hp]
    | some g =>
      rw [P.geneDropKinship_of_parents_eq_some hne hanc hp,
        P.kinship_of_gt_of_parents_eq_some hij hp, P.geneDropKinship_comm j,
        P.geneDropKinship_comm j,
        ih _ (by have := lt0 hp 0; omega) (g 0) j rfl,
        ih _ (by have := lt0 hp 1; omega) (g 1) j rfl]

/-- The inbreeding coefficient computed by Malécot's recursion is the probability of identity
by descent of the two copies of `i` under gene dropping. -/
theorem inbreeding_eq_kinshipInbreeding (i : Fin n) :
    P.inbreeding i = P.kinshipInbreeding i := by
  cases hp : P.parents i with
  | none => rw [P.inbreeding_of_parents_eq_none hp, kinshipInbreeding, hp]
  | some g =>
    rw [P.inbreeding_of_parents_eq_some hp, kinshipInbreeding, hp, geneDropKinship_eq_kinship]

/-! ### Wright's path formula: proof -/

/-- The only ancestral path from a founder is `[i]`. -/
theorem mem_ancPaths_of_parents_eq_none {i : Fin n} (h : P.parents i = none)
    {p : List (Fin n)} : p ∈ P.ancPaths i ↔ p = [i] := by
  rw [ancPaths]; split <;> simp_all

/-- The ancestral paths from a non-founder: `[i]` and `i :: q` for a path `q` from a parent. -/
theorem mem_ancPaths_of_parents_eq_some {i : Fin n} {g : Fin 2 → Fin n}
    (h : P.parents i = some g) {p : List (Fin n)} :
    p ∈ P.ancPaths i ↔ p = [i] ∨ ∃ k, ∃ q ∈ P.ancPaths (g k), p = i :: q := by
  rw [ancPaths]
  split
  · simp_all
  · rename_i g' h'
    rw [h] at h'; cases h'
    simp only [Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finset.mem_image]
    constructor
    · rintro (h | ⟨k, q, hq, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨k, q, hq, rfl⟩
    · rintro (h | ⟨k, q, hq, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨k, q, hq, rfl⟩

/-- Every individual on an ancestral path from `i` is `i` or precedes it. -/
theorem le_of_mem_ancPaths {i : Fin n} {p : List (Fin n)} (hp : p ∈ P.ancPaths i) :
    ∀ v ∈ p, v ≤ i := by
  induction i using WellFoundedLT.induction generalizing p with
  | _ i ih =>
  cases h : P.parents i with
  | none =>
    rw [P.mem_ancPaths_of_parents_eq_none h] at hp; subst hp; simp
  | some g =>
    rcases (P.mem_ancPaths_of_parents_eq_some h).mp hp with rfl | ⟨k, q, hq, rfl⟩
    · simp
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact le_rfl
      · exact (ih (g k) (P.parents_lt i g h k) hq v hv).trans (P.parents_lt i g h k).le

/-- Every ancestral path from `i` starts with `i`. -/
theorem exists_eq_cons_of_mem_ancPaths {i : Fin n} {p : List (Fin n)}
    (hp : p ∈ P.ancPaths i) : ∃ q, p = i :: q := by
  have := P.head?_of_mem_ancPaths hp
  cases p with
  | nil => simp at this
  | cons a q =>
    rw [List.head?_cons, Option.some.injEq] at this
    exact ⟨q, by rw [this]⟩

/-- A path from `i` ending at `i` is `[i]`. -/
theorem eq_singleton_of_mem_ancPaths {i : Fin n} {p : List (Fin n)} (hp : p ∈ P.ancPaths i)
    (hl : p.getLast? = some i) : p = [i] := by
  cases h : P.parents i with
  | none => exact (P.mem_ancPaths_of_parents_eq_none h).mp hp
  | some g =>
    rcases (P.mem_ancPaths_of_parents_eq_some h).mp hp with h' | ⟨k, q, hq, rfl⟩
    · exact h'
    · exfalso
      obtain ⟨r, rfl⟩ := P.exists_eq_cons_of_mem_ancPaths hq
      rw [List.getLast?_cons_cons] at hl
      have := P.le_of_mem_ancPaths hq i (List.mem_of_getLast? hl)
      exact absurd (this.trans_lt (P.parents_lt i g h k)) (lt_irrefl i)

/-- The weight of a pair of paths ending at `A` in Wright's formula. -/
private noncomputable def pathTerm (A : Fin n) (p p' : List (Fin n)) : ℝ :=
  if ∀ v ∈ p, v ∈ p' → v = A then
    (1 / 2 : ℝ) ^ (p.length + p'.length - 1) * (1 + P.kinshipInbreeding A)
  else 0

/-- Wright's sum for a fixed common ancestor `A`. -/
private noncomputable def pathSum (i j A : Fin n) : ℝ :=
  ∑ p ∈ P.pathsTo i A, ∑ p' ∈ P.pathsTo j A, P.pathTerm A p p'

private theorem pathTerm_comm (A : Fin n) (p p' : List (Fin n)) :
    P.pathTerm A p p' = P.pathTerm A p' p := by
  simp only [pathTerm, add_comm p.length]
  congr 1
  exact propext ⟨fun h v hv hv' => h v hv' hv, fun h v hv hv' => h v hv' hv⟩

private theorem pathSum_comm (i j A : Fin n) : P.pathSum i j A = P.pathSum j i A := by
  rw [pathSum, pathSum, Finset.sum_comm]
  simp only [P.pathTerm_comm A]

/-- Decomposition of a sum over the paths from a founder. -/
private theorem sum_pathsTo_of_parents_eq_none {j A : Fin n} (h : P.parents j = none)
    (f : List (Fin n) → ℝ) :
    ∑ p ∈ P.pathsTo j A, f p = if A = j then f [j] else 0 := by
  have : P.pathsTo j A = if A = j then {[j]} else ∅ := by
    ext p
    simp only [pathsTo, Finset.mem_filter, P.mem_ancPaths_of_parents_eq_none h]
    split_ifs with hA
    · subst hA; simp only [Finset.mem_singleton, and_iff_left_iff_imp]; rintro rfl; rfl
    · simp only [Finset.notMem_empty, iff_false, not_and]
      rintro rfl; simp [Ne.symm hA]
  rw [this]; split_ifs <;> simp

/-- Decomposition of a sum over the paths from a non-founder (no selfing). -/
private theorem sum_pathsTo_of_parents_eq_some (hP : P.NoSelfing) {j A : Fin n} {g : Fin 2 → Fin n}
    (h : P.parents j = some g) (f : List (Fin n) → ℝ) :
    ∑ p ∈ P.pathsTo j A, f p = (if A = j then f [j] else 0) +
      ∑ k : Fin 2, ∑ q ∈ P.pathsTo (g k) A, f (j :: q) := by
  have hanc : P.ancPaths j = insert [j] (Finset.univ.biUnion fun k : Fin 2 =>
      (P.ancPaths (g k)).image (List.cons j)) := by
    ext p
    rw [P.mem_ancPaths_of_parents_eq_some h]
    simp only [Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finset.mem_image]
    constructor
    · rintro (h | ⟨k, q, hq, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨k, q, hq, rfl⟩
    · rintro (h | ⟨k, q, hq, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨k, q, hq, rfl⟩
  have hnot : [j] ∉ Finset.univ.biUnion fun k : Fin 2 =>
      (P.ancPaths (g k)).image (List.cons j) := by
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image, not_exists,
      not_and]
    intro k q hq hqj
    obtain ⟨r, rfl⟩ := P.exists_eq_cons_of_mem_ancPaths hq
    simp at hqj
  have hdisj : (Set.univ : Set (Fin 2)).PairwiseDisjoint fun k : Fin 2 =>
      (P.ancPaths (g k)).image (List.cons j) := by
    intro k _ k' _ hkk'
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro p hp hp'
    simp only [Finset.mem_image] at hp hp'
    obtain ⟨q, hq, rfl⟩ := hp
    obtain ⟨q', hq', he⟩ := hp'
    have hqq : q' = q := List.cons_injective he
    subst hqq
    have h1 := P.head?_of_mem_ancPaths hq
    have h2 := P.head?_of_mem_ancPaths hq'
    rw [h1] at h2
    have hgk : g k = g k' := Option.some_injective _ h2
    have hne := hP j g h
    rcases Fin.exists_fin_two.mp ⟨k, rfl⟩ with rfl | rfl <;>
      rcases Fin.exists_fin_two.mp ⟨k', rfl⟩ with rfl | rfl
    · exact hkk' rfl
    · exact hne hgk
    · exact hne hgk.symm
    · exact hkk' rfl
  simp only [pathsTo, Finset.sum_filter, hanc]
  rw [Finset.sum_insert hnot, Finset.sum_biUnion (by simpa using hdisj)]
  congr 1
  · simp [eq_comm]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_image (fun _ _ _ _ h => List.cons_injective h)]
    refine Finset.sum_congr rfl fun q hq => ?_
    obtain ⟨r, rfl⟩ := P.exists_eq_cons_of_mem_ancPaths hq
    rw [List.getLast?_cons_cons]

/-- `[i]` is an ancestral path from `i`. -/
theorem singleton_mem_ancPaths (i : Fin n) : [i] ∈ P.ancPaths i := by
  cases h : P.parents i with
  | none => exact (P.mem_ancPaths_of_parents_eq_none h).mpr rfl
  | some g => exact (P.mem_ancPaths_of_parents_eq_some h).mpr (Or.inl rfl)

private theorem pathTerm_cons {A j : Fin n} {p : List (Fin n)} (q : List (Fin n)) (hj : j ∉ p)
    (hp : p ≠ []) : P.pathTerm A p (j :: q) = 1 / 2 * P.pathTerm A p q := by
  have hcond : (∀ v ∈ p, v ∈ j :: q → v = A) ↔ (∀ v ∈ p, v ∈ q → v = A) := by
    constructor
    · intro h v hv hvq; exact h v hv (List.mem_cons_of_mem _ hvq)
    · intro h v hv hvq
      rcases List.mem_cons.mp hvq with rfl | hvq
      · exact absurd hv hj
      · exact h v hv hvq
  have hlen : p.length + (j :: q).length - 1 = (p.length + q.length - 1) + 1 := by
    have := List.length_pos_iff.mpr hp
    simp only [List.length_cons]; omega
  simp only [pathTerm, hcond, hlen, pow_succ]
  split_ifs <;> ring

private theorem not_mem_of_mem_pathsTo {i j A : Fin n} {p : List (Fin n)} (hij : i < j)
    (hp : p ∈ P.pathsTo i A) : j ∉ p ∧ A ≠ j ∧ p ≠ [] := by
  simp only [pathsTo, Finset.mem_filter] at hp
  refine ⟨fun hj => absurd (P.le_of_mem_ancPaths hp.1 j hj) (not_le.mpr hij), ?_, ?_⟩
  · rintro rfl
    exact absurd (P.le_of_mem_ancPaths hp.1 A (List.mem_of_getLast? hp.2)) (not_le.mpr hij)
  · rintro rfl; simp at hp

private theorem pathSum_of_lt_of_parents_eq_some (hP : P.NoSelfing) {i j A : Fin n}
    {g : Fin 2 → Fin n} (hij : i < j) (h : P.parents j = some g) :
    P.pathSum i j A = (P.pathSum i (g 0) A + P.pathSum i (g 1) A) / 2 := by
  simp only [pathSum, ← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun p hp => ?_
  obtain ⟨hj, hA, hne⟩ := P.not_mem_of_mem_pathsTo hij hp
  rw [P.sum_pathsTo_of_parents_eq_some hP h, ite_eq_right hA, zero_add, Fin.sum_univ_two]
  simp only [P.pathTerm_cons _ hj hne, ← Finset.mul_sum]
  ring

private theorem pathSum_of_lt_of_parents_eq_none {i j A : Fin n} (hij : i < j)
    (h : P.parents j = none) : P.pathSum i j A = 0 := by
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [P.sum_pathsTo_of_parents_eq_none h, ite_eq_right (P.not_mem_of_mem_pathsTo hij hp).2.1]

private theorem pathSum_self (i A : Fin n) :
    P.pathSum i i A = if A = i then 1 / 2 * (1 + P.kinshipInbreeding i) else 0 := by
  split_ifs with hA
  · subst hA
    have : P.pathsTo A A = {[A]} := by
      ext p
      simp only [pathsTo, Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hp, hl⟩; exact P.eq_singleton_of_mem_ancPaths hp hl
      · rintro rfl; exact ⟨P.singleton_mem_ancPaths A, rfl⟩
    simp [pathSum, this, pathTerm]
  · refine Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun p' hp' => ?_
    simp only [pathsTo, Finset.mem_filter] at hp hp'
    obtain ⟨q, rfl⟩ := P.exists_eq_cons_of_mem_ancPaths hp.1
    obtain ⟨q', rfl⟩ := P.exists_eq_cons_of_mem_ancPaths hp'.1
    rw [pathTerm, ite_eq_right]
    intro hc
    exact (Ne.symm hA) (hc i (List.mem_cons_self) (List.mem_cons_self))

private theorem kinship_eq_sum_pathSum (hP : P.NoSelfing) (i j : Fin n) :
    P.kinship i j = ∑ A, P.pathSum i j A := by
  induction hs : i.val + j.val using Nat.strong_induction_on generalizing i j with
  | _ s ih =>
  have lt0 : ∀ {x : Fin n} {g : Fin 2 → Fin n}, P.parents x = some g → ∀ k, (g k).val < x.val :=
    fun h k => P.parents_lt _ _ h k
  rcases lt_trichotomy i j with hij | rfl | hij
  · cases hp : P.parents j with
    | none =>
      rw [P.kinship_of_lt_of_parents_eq_none hij hp]
      simp [P.pathSum_of_lt_of_parents_eq_none hij hp]
    | some g =>
      rw [P.kinship_of_lt_of_parents_eq_some hij hp,
        ih _ (by have := lt0 hp 0; omega) i (g 0) rfl,
        ih _ (by have := lt0 hp 1; omega) i (g 1) rfl, ← Finset.sum_add_distrib,
        Finset.sum_div]
      simp only [P.pathSum_of_lt_of_parents_eq_some hP hij hp]
  · simp only [pathSum_self, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    cases hp : P.parents i with
    | none =>
      rw [P.kinship_self_of_parents_eq_none hp, kinshipInbreeding, hp]; norm_num
    | some g =>
      rw [P.kinship_self_of_parents_eq_some hp, kinshipInbreeding, hp]; ring
  · simp only [P.pathSum_comm i j]
    cases hp : P.parents i with
    | none =>
      rw [P.kinship_of_gt_of_parents_eq_none hij hp]
      simp [P.pathSum_of_lt_of_parents_eq_none hij hp]
    | some g =>
      rw [P.kinship_of_gt_of_parents_eq_some hij hp,
        ih _ (by have := lt0 hp 0; omega) (g 0) j rfl,
        ih _ (by have := lt0 hp 1; omega) (g 1) j rfl, ← Finset.sum_add_distrib,
        Finset.sum_div]
      simp only [P.pathSum_of_lt_of_parents_eq_some hP hij hp, P.pathSum_comm j]

/-- **Wright's path formula** in kinship form: `φ i j` is the sum, over common ancestors `A`
(including `i` or `j` themselves) and pairs of ancestral paths `p` from `i` to `A` and `p'` from
`j` to `A` that share no individual other than `A`, of `(1/2) ^ (n₁ + n₂ + 1) * (1 + F A)`,
where `n₁ + n₂ + 1 = p.length + p'.length - 1` is the number of individuals on the loop. -/
theorem kinship_eq_sum_paths (hP : P.NoSelfing) (i j : Fin n) :
    P.kinship i j = ∑ A, ∑ p ∈ P.pathsTo i A, ∑ p' ∈ P.pathsTo j A,
      if ∀ v ∈ p, v ∈ p' → v = A then
        (1 / 2 : ℝ) ^ (p.length + p'.length - 1) * (1 + P.kinshipInbreeding A)
      else 0 := by
  rw [P.kinship_eq_sum_pathSum hP]
  rfl

/-- **Wright's path formula** for the inbreeding coefficient (Wright 1922): if `i` has parents
`f = g 0` and `m = g 1`, then `F_i = Σ (1/2) ^ (n₁ + n₂ + 1) (1 + F_A)` over common ancestors `A`
of `f` and `m` (including `f` or `m` themselves) and pairs of ancestral paths from `f` and `m`
to `A` (with `n₁` and `n₂` edges) that share only `A`. Here `F` is the gene-dropping inbreeding
coefficient. -/
theorem inbreeding_eq_sum_paths (hP : P.NoSelfing) {i : Fin n} {g : Fin 2 → Fin n}
    (h : P.parents i = some g) :
    P.inbreeding i = ∑ A, ∑ p ∈ P.pathsTo (g 0) A, ∑ p' ∈ P.pathsTo (g 1) A,
      if ∀ v ∈ p, v ∈ p' → v = A then
        (1 / 2 : ℝ) ^ (p.length + p'.length - 1) * (1 + P.inbreeding A)
      else 0 := by
  simp only [inbreeding_eq_kinshipInbreeding]
  rw [kinshipInbreeding, h]
  exact P.kinship_eq_sum_paths hP (g 0) (g 1)

end Pedigree

end MathlibExt.Biology.StatisticalGenetics.Kinship
