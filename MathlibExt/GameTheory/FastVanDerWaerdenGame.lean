/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.Data.Finset.Sort
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

/-!
# Symmetry types of rational sets in the van der Waerden game

For a finite set of rationals, a symmetry type is a pair of distinct positions
whose erasures are related by an increasing affine map. A set with at least
four elements has at most one such type (Alpert et al., INTEGERS 26 (2026),
Article A40, Lemma 5).
-/

set_option autoImplicit false

namespace MetaMathlibExt.FastVanDerWaerdenGame

open Finset

@[expose] public section

/-- **Copies of finite sets of rationals.** Let $A$ and $B$ be finite sets of rational numbers.
$B$ is a copy of $A$ if there are rationals $a > 0$ and $b$ such that
$B = aA + b = \{ax + b : x \in A\}$.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40, Section 5. -/
def IsRatCopy (A B : Finset ℚ) : Prop :=
  ∃ a b : ℚ, 0 < a ∧ B = A.image fun x => a * x + b

/-- **Symmetric sets of a given type.** Let $S = \{s_0 < s_1 < \dots < s_{n-1}\}$ be a finite
set of $n$ rational numbers and let $i, j < n$. Then $S$ is called symmetric of type $(i, j)$ if
$i < j$ and $S \setminus \{s_i\}$ is a copy of $S \setminus \{s_j\}$.

Positions are counted from $0$, so the paper's type $(i + 1, j + 1)$ is the type $(i, j)$ here.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40,
Definition 2. -/
def IsSymmetricOfType (S : Finset ℚ) (i j : Fin S.card) : Prop :=
  i < j ∧ IsRatCopy (S.erase (S.orderEmbOfFin rfl j)) (S.erase (S.orderEmbOfFin rfl i))

/-- **Containing a homothetic copy.** Let $S$ and $M$ be finite sets of natural numbers. $M$
contains a homothetic copy of $S$ if there are a natural number $a > 0$ and an integer $b$ such
that $as + b \in M$ for every $s \in S$, that is, $aS + b \subseteq M$. This is Maker's winning
condition.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40, Section 1. -/
def ContainsCopy (S M : Finset ℕ) : Prop :=
  ∃ a : ℕ, 0 < a ∧ ∃ b : ℤ, ∀ s ∈ S, ∃ m ∈ M, (m : ℤ) = a * s + b

/-- **Maker wins within $p$ moves.** Let $S$ be a finite set of natural numbers. In the
$S$-game, Maker and Breaker alternately claim unclaimed natural numbers, and Maker wins once the
numbers Maker has claimed contain a copy $aS + b = \{as + b : s \in S\}$ of $S$, where $a$ is a
positive integer and $b$ is an integer. Let $M$ and $B$ be finite sets of natural numbers
(claimed by Maker and by Breaker) and $p$ a natural number, with Maker to move. Maker wins
within $p$ moves if $M$ already contains such a copy of $S$, or if $p \ge 1$ and there is a
number $x \notin M \cup B$ such that for every number $y \ne x$ with $y \notin M \cup B$, Maker
wins within $p - 1$ moves from the position where Maker has claimed $M \cup \{x\}$ and Breaker
has claimed $B \cup \{y\}$.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40, Sections 1
and 5 (`p`-move strategy). -/
def MakerWinsWithin (S : Finset ℕ) : ℕ → Finset ℕ → Finset ℕ → Prop
  | 0, M, _ => ContainsCopy S M
  | p + 1, M, B => ContainsCopy S M ∨
      ∃ x : ℕ, x ∉ M ∧ x ∉ B ∧
        ∀ y : ℕ, y ≠ x → y ∉ M → y ∉ B → MakerWinsWithin S p (insert x M) (insert y B)

/-- **Symmetric sets of rationals.** A finite set $S$ of rational numbers is symmetric if it is
symmetric of some type $(i, j)$ with $i, j < |S|$.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40,
Definition 2. -/
def IsSymmetric (S : Finset ℚ) : Prop :=
  ∃ i j : Fin S.card, IsSymmetricOfType S i j

end

/-- The entry at rank `k`. The lemmas below only use ranks strictly below `S.card`. -/
private def entry (S : Finset ℚ) (k : ℕ) : ℚ :=
  if hk : k < S.card then S.orderEmbOfFin rfl ⟨k, hk⟩ else 0

private theorem entry_lt {S : Finset ℚ} {k l : ℕ} (hkl : k < l) (hl : l < S.card) :
    entry S k < entry S l := by
  simpa only [entry, dite_eq_left (hkl.trans hl), dite_eq_left hl] using
    (S.orderEmbOfFin rfl).strictMono (show (⟨k, hkl.trans hl⟩ : Fin S.card) < ⟨l, hl⟩ from hkl)

/-- The original rank of an entry after erasing rank `i`. -/
private def skipRank (i k : ℕ) : ℕ :=
  if k < i then k else k + 1

private theorem skipRank_lt {n i k : ℕ} (hk : k < n - 1) : skipRank i k < n := by
  unfold skipRank
  split <;> omega

private theorem strictMono_skipRank (i : ℕ) : StrictMono (skipRank i) := by
  intro k l hkl
  unfold skipRank
  split <;> split <;> omega

private theorem entry_skipRank_mem_erase (S : Finset ℚ) (i : Fin S.card) (k : Fin (S.card - 1)) :
    entry S (skipRank i.val k.val) ∈ S.erase (S.orderEmbOfFin rfl i) := by
  rw [entry, dite_eq_left (skipRank_lt k.isLt), mem_erase]
  refine ⟨fun h ↦ ?_, S.orderEmbOfFin_mem rfl _⟩
  have he := congrArg Fin.val ((S.orderEmbOfFin rfl).injective h)
  change skipRank i.val k.val = i.val at he
  unfold skipRank at he
  split at he <;> omega

private theorem strictMono_entry_skipRank (S : Finset ℚ) (i : Fin S.card) :
    StrictMono (fun k : Fin (S.card - 1) ↦ entry S (skipRank i.val k.val)) := by
  intro k l hkl
  exact entry_lt (strictMono_skipRank i.val hkl) (skipRank_lt l.isLt)

/-- Rank matching for an increasing affine map between two erasures. -/
private def RankMatch (S : Finset ℚ) (i j : ℕ) (a b : ℚ) : Prop :=
  ∀ k < S.card - 1, a * entry S (skipRank j k) + b = entry S (skipRank i k)

private theorem rankMatch_of_image {S : Finset ℚ} {i j : Fin S.card} {a b : ℚ}
    (ha : 0 < a) (himage : S.erase (S.orderEmbOfFin rfl i) =
      (S.erase (S.orderEmbOfFin rfl j)).image (fun x ↦ a * x + b)) :
    RankMatch S i.val j.val a b := by
  have hi := card_erase_of_mem (S.orderEmbOfFin_mem rfl i)
  have ht := orderEmbOfFin_unique hi (entry_skipRank_mem_erase S i) (strictMono_entry_skipRank S i)
  have hs : (fun k : Fin (S.card - 1) ↦ a * entry S (skipRank j.val k.val) + b) =
      ⇑((S.erase (S.orderEmbOfFin rfl i)).orderEmbOfFin hi) := by
    apply orderEmbOfFin_unique hi
    · intro k
      rw [himage]
      exact mem_image.mpr ⟨_, entry_skipRank_mem_erase S j k, rfl⟩
    · intro k l hkl
      exact (add_lt_add_iff_right b).2 <|
        mul_lt_mul_of_pos_left (strictMono_entry_skipRank S j hkl) ha
  intro k hk
  exact congrFun (hs.trans ht.symm) ⟨k, hk⟩

private theorem RankMatch.before {S : Finset ℚ} {i j k : ℕ} {a b : ℚ}
    (h : RankMatch S i j a b) (hk : k < S.card - 1) (hki : k < i) (hkj : k < j) :
    a * entry S k + b = entry S k := by
  simpa only [skipRank, ite_eq_left hki, ite_eq_left hkj] using h k hk

private theorem RankMatch.shift {S : Finset ℚ} {i j k : ℕ} {a b : ℚ}
    (h : RankMatch S i j a b) (hk : k < S.card - 1) (hik : i ≤ k) (hkj : k < j) :
    a * entry S k + b = entry S (k + 1) := by
  simpa only [skipRank, ite_eq_left hkj, ite_eq_right (not_lt.mpr hik)] using h k hk

private theorem RankMatch.after {S : Finset ℚ} {i j k : ℕ} {a b : ℚ}
    (h : RankMatch S i j a b) (hk : k < S.card - 1) (hik : i ≤ k) (hjk : j ≤ k) :
    a * entry S (k + 1) + b = entry S (k + 1) := by
  simpa only [skipRank, ite_eq_right (not_lt.mpr hik), ite_eq_right (not_lt.mpr hjk)] using h k hk

private theorem affine_eq_of_eq_at {x y a b c d : ℚ} (hxy : x < y)
    (hx : a * x + b = c * x + d) (hy : a * y + b = c * y + d) : a = c ∧ b = d := by
  have hprod : (a - c) * (y - x) = 0 := by linear_combination hy - hx
  have ha := sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right (sub_ne_zero.mpr hxy.ne'))
  exact ⟨ha, by simpa [ha] using hx⟩

-- A symmetry cannot fix two entries: it moves the entry at its first erased rank.
private theorem RankMatch.endpoints {S : Finset ℚ} {i j : ℕ} {a b : ℚ}
    (h : RankMatch S i j a b) (hn : 4 ≤ S.card) (hij : i < j) (hj : j < S.card) :
    i ≤ 1 ∧ S.card - 2 ≤ j ∧ (i = 0 ∨ j = S.card - 1) := by
  have hnotId : ¬ (a = 1 ∧ b = 0) := by
    rintro ⟨rfl, rfl⟩
    exact (entry_lt (S := S) (k := i) (l := i + 1) (by omega) (by omega)).ne
      (by simpa using h.shift (k := i) (by omega) le_rfl hij)
  have hfixed (x y : ℚ) (hxy : x < y) (hx : a * x + b = x) (hy : a * y + b = y) : False :=
    hnotId (affine_eq_of_eq_at hxy (by simpa using hx) (by simpa using hy))
  refine ⟨?_, ?_, ?_⟩
  · by_contra! hi
    exact hfixed _ _ (entry_lt (by omega) (by omega))
      (h.before (k := 0) (by omega) (by omega) (by omega))
      (h.before (k := 1) (by omega) hi (by omega))
  · by_contra! hj'
    exact hfixed _ _ (entry_lt (by omega) (by omega))
      (h.after (k := S.card - 3) (by omega) (by omega) (by omega))
      (h.after (k := S.card - 2) (by omega) (by omega) (by omega))
  · by_contra! hends
    exact hfixed _ _ (entry_lt (by omega) (by omega))
      (h.before (k := 0) (by omega) (by omega) (by omega))
      (h.after (k := S.card - 2) (by omega) (by omega) (by omega))

-- The map itself determines the erased ranks, by comparing its first and last rank equations.
private theorem RankMatch.unique_for_map {S : Finset ℚ} {i j i' j' : ℕ} {a b : ℚ}
    (h : RankMatch S i j a b) (h' : RankMatch S i' j' a b) (ha : 0 < a)
    (hn : 4 ≤ S.card) (hi : i ≤ 1) (hi' : i' ≤ 1)
    (hj : S.card - 2 ≤ j) (hj' : S.card - 2 ≤ j') (hjn : j < S.card) (hjn' : j' < S.card) :
    i = i' ∧ j = j' := by
  have hinj {k l : ℕ} (hk : k < S.card) (hl : l < S.card)
      (he : entry S k = entry S l) : k = l := by
    rcases lt_trichotomy k l with hkl | hkl | hkl
    · exact ((entry_lt hkl hl).ne he).elim
    · exact hkl
    · exact ((entry_lt hkl hk).ne he.symm).elim
  have left {p q : ℕ} (m : RankMatch S p q a b) (hq : S.card - 2 ≤ q) :
      a * entry S 0 + b = entry S (skipRank p 0) := by
    have hs : skipRank q 0 = 0 := ite_eq_left (by omega)
    simpa only [hs] using m 0 (by omega)
  have right {p q : ℕ} (m : RankMatch S p q a b) (hp : p ≤ 1) :
      a * entry S (skipRank q (S.card - 2)) + b = entry S (S.card - 2 + 1) := by
    have hs : skipRank p (S.card - 2) = S.card - 2 + 1 := ite_eq_right (by omega)
    simpa only [hs] using m (S.card - 2) (by omega)
  have hle := hinj (skipRank_lt (by omega)) (skipRank_lt (by omega))
    ((left h hj).symm.trans (left h' hj'))
  have hmono : StrictMono (fun x : ℚ ↦ a * x + b) := fun _ _ hxy ↦
    (add_lt_add_iff_right b).2 (mul_lt_mul_of_pos_left hxy ha)
  have hre := hinj (skipRank_lt (by omega)) (skipRank_lt (by omega))
    (hmono.injective ((right h hi).trans (right h' hi').symm))
  unfold skipRank at hle hre
  constructor
  · split at hle <;> split at hle <;> omega
  · split at hre <;> split at hre <;> omega

-- The remaining four-point case would give a rational root of X² + X − 1 in (0, 1).
private theorem no_rat_root {c : ℚ} (hc : 0 < c) (he : c * c + c = 1) : False := by
  have hlt : c < 1 := by
    by_contra! h
    nlinarith only [he, hc, mul_nonneg (sub_nonneg.mpr h) hc.le]
  have hden : c.den * c.den = c.den := by
    have hd := congrArg Rat.den (show c * c = 1 - c by linarith only [he])
    calc
      c.den * c.den = (c * c).den := (Rat.mul_self_den c).symm
      _ = (1 - c).den := hd
      _ = c.den := Rat.natCast_sub_den 1 c
  have hden1 : c.den = 1 := Nat.eq_of_mul_eq_mul_left c.den_pos (by simpa using hden)
  have hint : c = (c.num : ℚ) := by
    calc
      c = (c.num : ℚ) / (c.den : ℚ) := (Rat.num_div_den c).symm
      _ = _ := by simp [hden1]
  rw [hint] at hc hlt
  have hp : 0 < c.num := by exact_mod_cast hc
  have hq : c.num < 1 := by exact_mod_cast hlt
  omega

private theorem not_two_middle_types {S : Finset ℚ} (hn : S.card = 4) {a b c d : ℚ}
    (hc : 0 < c) (f : RankMatch S 1 3 a b) (g : RankMatch S 0 2 c d) : False := by
  have f0 := f.before (k := 0) (by omega) (by decide) (by decide)
  have f1 := f.shift (k := 1) (by omega) (by decide) (by decide)
  have f2 := f.shift (k := 2) (by omega) (by decide) (by decide)
  have g0 := g.shift (k := 0) (by omega) (by decide) (by decide)
  have g1 := g.shift (k := 1) (by omega) (by decide) (by decide)
  have g3 := g.after (k := 2) (by omega) (by decide) (by decide)
  have h01 : entry S 0 < entry S 1 := entry_lt (by decide) (by omega)
  have h12 : entry S 1 < entry S 2 := entry_lt (by decide) (by omega)
  have hsum : a = 1 + c := by
    have hz : (a - (1 + c)) * (entry S 1 - entry S 0) = 0 := by
      linear_combination f1 - f0 - g1 + g0
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr h01.ne'))
  have hstep : entry S 3 - entry S 2 = a * (entry S 2 - entry S 1) := by
    linear_combination f1 - f2
  have hrel : a = c * (a + 1) := by
    have hz : (a - c * (a + 1)) * (entry S 2 - entry S 1) = 0 := by
      linear_combination (c - 1) * hstep - g3 + g1
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr h12.ne'))
  rw [hsum] at hrel
  exact no_rat_root hc (by nlinarith only [hrel])

/-- **Possible types of a symmetric set.** Let $S$ be a finite set of rational numbers with
$n \ge 4$ elements. If $S$ is symmetric of type $(i, j)$, with positions counted from $0$, then
$(i, j)$ is $(0, n - 1)$, $(1, n - 1)$ or $(0, n - 2)$. In the paper's one-based numbering these
are the types $(1, n)$, $(2, n)$ and $(1, n - 1)$.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40, Lemma 2
(`integers-2026-A40-lem-2`). -/
public theorem isSymmetricOfType_cases (S : Finset ℚ) (hS : 4 ≤ S.card)
    (i j : Fin S.card) (h : IsSymmetricOfType S i j) :
    (i.val = 0 ∧ j.val = S.card - 1) ∨ (i.val = 1 ∧ j.val = S.card - 1) ∨
      (i.val = 0 ∧ j.val = S.card - 2) := by
  obtain ⟨hij, a, b, ha, himage⟩ := h
  have hj_lt := j.isLt
  obtain ⟨hi, hj, hend⟩ := (rankMatch_of_image ha himage).endpoints hS hij hj_lt
  omega

/-- **Uniqueness of the symmetry type.** A finite set $S$ of rational numbers with at least
four elements is symmetric of at most one type: if $S$ is symmetric of types $(i, j)$ and
$(i', j')$, then $i = i'$ and $j = j'$.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40, Lemma 5
(`integers-2026-A40-lem-5`). -/
public theorem isSymmetricOfType_unique (S : Finset ℚ) (hS : 4 ≤ S.card)
    (i j i' j' : Fin S.card) (h : IsSymmetricOfType S i j)
    (h' : IsSymmetricOfType S i' j') :
    i = i' ∧ j = j' := by
  obtain ⟨hij, a, b, ha, himage⟩ := h
  obtain ⟨hij', c, d, hc, himage'⟩ := h'
  have f := rankMatch_of_image ha himage
  have g := rankMatch_of_image hc himage'
  obtain ⟨hi, hj, hend⟩ := f.endpoints hS hij j.isLt
  obtain ⟨hi', hj', hend'⟩ := g.endpoints hS hij' j'.isLt
  -- Both maps shift rank 1. A second shared shift determines the whole affine map.
  have h1 := (f.shift (k := 1) (by omega) hi (by omega)).trans
    (g.shift (k := 1) (by omega) hi' (by omega)).symm
  have finish (he : a = c ∧ b = d) : i = i' ∧ j = j' := by
    rcases he with ⟨rfl, rfl⟩
    obtain ⟨hii, hjj⟩ := f.unique_for_map g ha hS hi hi' hj hj' j.isLt j'.isLt
    exact ⟨Fin.ext hii, Fin.ext hjj⟩
  by_cases hz : i.val = 0 ∧ i'.val = 0
  · have h0 := (f.shift (k := 0) (by omega) (by omega) (by omega)).trans
      (g.shift (k := 0) (by omega) (by omega) (by omega)).symm
    exact finish (affine_eq_of_eq_at (entry_lt (by decide) (by omega)) h0 h1)
  by_cases ht : 2 < j.val ∧ 2 < j'.val
  · have h2 := (f.shift (k := 2) (by omega) (by omega) ht.1).trans
      (g.shift (k := 2) (by omega) (by omega) ht.2).symm
    exact finish (affine_eq_of_eq_at (entry_lt (by decide) (by omega)) h1 h2)
  -- With no second shared shift, only the mixed four-point case is left.
  have hn : S.card = 4 := by omega
  have hm : (i.val = 1 ∧ j.val = 3 ∧ i'.val = 0 ∧ j'.val = 2) ∨
      (i'.val = 1 ∧ j'.val = 3 ∧ i.val = 0 ∧ j.val = 2) := by omega
  exfalso
  rcases hm with ⟨hi₁, hj₁, hi₂, hj₂⟩ | ⟨hi₁, hj₁, hi₂, hj₂⟩
  · exact not_two_middle_types hn hc (by simpa only [hi₁, hj₁] using f)
      (by simpa only [hi₂, hj₂] using g)
  · exact not_two_middle_types hn ha (by simpa only [hi₁, hj₁] using g)
      (by simpa only [hi₂, hj₂] using f)


-- Positive affine maps preserve the order of the entries of a copy.
private theorem fastAffine_strictMono {a b : ℚ} (ha : 0 < a) :
    StrictMono (fun x : ℚ ↦ a * x + b) := fun _ _ hxy ↦
  (add_lt_add_iff_right b).2 (mul_lt_mul_of_pos_left hxy ha)

private theorem fastCopy_card_and_image {S M : Finset ℕ} (h : ContainsCopy S M) :
    S.card ≤ M.card ∧ (M.card ≤ S.card →
      IsRatCopy (S.image fun s : ℕ ↦ (s : ℚ)) (M.image fun m : ℕ ↦ (m : ℚ))) := by
  obtain ⟨a, ha, b, hcopy⟩ := h
  let A := S.image fun s : ℕ ↦ (s : ℚ)
  let C := M.image fun m : ℕ ↦ (m : ℚ)
  let f : ℚ → ℚ := fun x ↦ (a : ℚ) * x + (b : ℚ)
  have ha' : (0 : ℚ) < a := by exact_mod_cast ha
  have hsub : A.image f ⊆ C := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hu
    obtain ⟨s, hs, rfl⟩ := mem_image.mp hv
    obtain ⟨m, hm, he⟩ := hcopy s hs
    refine mem_image.mpr ⟨m, hm, ?_⟩
    change (m : ℚ) = (a : ℚ) * (s : ℚ) + (b : ℚ)
    exact_mod_cast he
  have hA : (A.image f).card = S.card := by
    rw [card_image_of_injective _ (fastAffine_strictMono ha').injective]
    exact card_image_of_injective _ Nat.cast_injective
  have hC : C.card = M.card := card_image_of_injective _ Nat.cast_injective
  constructor
  · simpa only [hA, hC] using card_le_card hsub
  · intro hle
    exact ⟨a, b, ha', (eq_of_subset_of_card_le hsub (by simpa only [hA, hC] using hle)).symm⟩

private theorem fastMove_of_small {S M B : Finset ℕ} {p : ℕ} (hM : M.card < S.card)
    (h : MakerWinsWithin S (p + 1) M B) :
    ∃ x : ℕ, x ∉ M ∧ x ∉ B ∧
      ∀ y : ℕ, y ≠ x → y ∉ M → y ∉ B → MakerWinsWithin S p (insert x M) (insert y B) := by
  change ContainsCopy S M ∨ _ at h
  exact h.resolve_left (fun hcopy ↦ (not_le_of_gt hM) (fastCopy_card_and_image hcopy).1)

private theorem fastReply_exists (M B : Finset ℕ) (x : ℕ) :
    ∃ y : ℕ, y ≠ x ∧ y ∉ M ∧ y ∉ B := by
  let D := insert x (M ∪ B)
  have hy : D.sup id + 1 ∉ D := by
    intro hmem
    have hle : D.sup id + 1 ≤ D.sup id := le_sup (f := id) hmem
    omega
  exact ⟨_, by simpa only [D, mem_insert, mem_union, not_or] using hy⟩

-- Follow one branch through the first three Maker moves; then block its completion.
private theorem fastTwoCompletions {S : Finset ℕ} (hS : S.card = 4)
    (h : MakerWinsWithin S 4 ∅ ∅) :
    ∃ (M : Finset ℕ) (x y : ℕ), M.card = 3 ∧ x ∉ M ∧ y ∉ M ∧ x ≠ y ∧
      ContainsCopy S (insert x M) ∧ ContainsCopy S (insert y M) := by
  obtain ⟨m₁, _, _, next₁⟩ := fastMove_of_small (by simp [hS]) h
  obtain ⟨b₁, h₁, hb₁M, hb₁B⟩ := fastReply_exists ∅ ∅ m₁
  let M₁ : Finset ℕ := insert m₁ ∅
  let B₁ : Finset ℕ := insert b₁ ∅
  have h₁' : MakerWinsWithin S 3 M₁ B₁ := next₁ b₁ h₁ hb₁M hb₁B
  have hc₁ : M₁.card = 1 := by simp [M₁]
  obtain ⟨m₂, hm₂, _, next₂⟩ := fastMove_of_small (by rw [hc₁, hS]; decide) h₁'
  obtain ⟨b₂, h₂, hb₂M, hb₂B⟩ := fastReply_exists M₁ B₁ m₂
  let M₂ := insert m₂ M₁
  let B := insert b₂ B₁
  have h₂' : MakerWinsWithin S 2 M₂ B := next₂ b₂ h₂ hb₂M hb₂B
  have hc₂ : M₂.card = 2 := by
    change (insert m₂ M₁).card = 2
    rw [card_insert_of_notMem hm₂, hc₁]
  obtain ⟨m₃, hm₃, _, next₃⟩ := fastMove_of_small (by rw [hc₂, hS]; decide) h₂'
  let M := insert m₃ M₂
  have hM : M.card = 3 := by
    change (insert m₃ M₂).card = 3
    rw [card_insert_of_notMem hm₃, hc₂]
  have complete {b : ℕ} (hb : b ≠ m₃) (hbM : b ∉ M₂) (hbB : b ∉ B) :
      ∃ x : ℕ, x ∉ M ∧ x ∉ insert b B ∧ ContainsCopy S (insert x M) := by
    have hw : MakerWinsWithin S 1 M (insert b B) := next₃ b hb hbM hbB
    obtain ⟨x, hxM, hxB, next⟩ := fastMove_of_small (by rw [hM, hS]; decide) hw
    obtain ⟨z, hz, hzM, hzB⟩ := fastReply_exists M (insert b B) x
    exact ⟨x, hxM, hxB, next z hz hzM hzB⟩
  obtain ⟨dummy, hd, hdM, hdB⟩ := fastReply_exists M₂ B m₃
  obtain ⟨x, hxM, hxB, hx⟩ := complete hd hdM hdB
  have hxM' : x ≠ m₃ ∧ x ∉ M₂ := by
    simpa only [M, mem_insert, not_or] using hxM
  obtain ⟨y, hyM, hyB, hy⟩ := complete hxM'.1 hxM'.2 (fun hxB' ↦ hxB (mem_insert_of_mem hxB'))
  exact ⟨M, x, y, hM, hxM, hyM, fun hxy ↦ hyB (hxy ▸ mem_insert_self x B), hx, hy⟩

-- Pull the last move back to a rank of the original set and erase it.
private theorem fastErasedRank {A T : Finset ℚ} {x a b : ℚ} (hx : x ∉ T) (ha : 0 < a)
    (h : insert x T = A.image (fun v ↦ a * v + b)) :
    ∃ i : Fin A.card, a * A.orderEmbOfFin rfl i + b = x ∧
      T = (A.erase (A.orderEmbOfFin rfl i)).image (fun v ↦ a * v + b) := by
  have hmem : x ∈ A.image (fun v ↦ a * v + b) := h ▸ mem_insert_self x T
  obtain ⟨v, hv, he⟩ := mem_image.mp hmem
  have hvr : v ∈ Set.range (A.orderEmbOfFin rfl) := by simpa using hv
  obtain ⟨i, rfl⟩ := hvr
  refine ⟨i, he, ?_⟩
  rw [image_erase (fastAffine_strictMono ha).injective, he, ← h, erase_insert hx]

private theorem fastCopy_of_common_image {U V T : Finset ℚ} {a b c d : ℚ}
    (ha : 0 < a) (hc : 0 < c)
    (hU : T = U.image (fun v ↦ a * v + b)) (hV : T = V.image (fun v ↦ c * v + d)) :
    IsRatCopy U V := by
  have hinv (u v : ℚ) (h : a * u + b = c * v + d) : a / c * u + (b - d) / c = v := by
    rw [div_mul_eq_mul_div, ← add_div, div_eq_iff hc.ne']
    linarith only [h]
  refine ⟨a / c, (b - d) / c, div_pos ha hc, ?_⟩
  ext v
  constructor
  · intro hv
    have ht : c * v + d ∈ T := hV ▸ mem_image.mpr ⟨v, hv, rfl⟩
    rw [hU] at ht
    obtain ⟨u, hu, he⟩ := mem_image.mp ht
    exact mem_image.mpr ⟨u, hu, hinv u v he⟩
  · intro hv
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hv
    have ht : a * u + b ∈ T := hU ▸ mem_image.mpr ⟨u, hu, rfl⟩
    rw [hV] at ht
    obtain ⟨w, hw, he⟩ := mem_image.mp ht
    rwa [hinv u w he.symm]

private theorem symmetric_of_winsFour {S : Finset ℕ} (hS : S.card = 4)
    (h : MakerWinsWithin S 4 ∅ ∅) : IsSymmetric (S.image fun s : ℕ => (s : ℚ)) := by
  obtain ⟨M, x, y, hM, hxM, hyM, hxy, hx, hy⟩ := fastTwoCompletions hS h
  let A := S.image fun s : ℕ ↦ (s : ℚ)
  let T := M.image fun m : ℕ ↦ (m : ℚ)
  have hA : A.card = 4 := (card_image_of_injective _ Nat.cast_injective).trans hS
  have hT : T.card = A.card - 1 := by
    rw [hA, show T.card = M.card from card_image_of_injective _ Nat.cast_injective, hM]
  obtain ⟨a, b, ha, heₓ⟩ :=
    (fastCopy_card_and_image hx).2 (by rw [card_insert_of_notMem hxM, hM, hS])
  obtain ⟨c, d, hc, heᵧ⟩ :=
    (fastCopy_card_and_image hy).2 (by rw [card_insert_of_notMem hyM, hM, hS])
  have notMem {n : ℕ} (hn : n ∉ M) : (n : ℚ) ∉ T := by
    simpa only [T, mem_image, Nat.cast_inj, exists_eq_right] using hn
  obtain ⟨i, hi, hiT⟩ := fastErasedRank (notMem hxM) ha (by simpa only [image_insert] using heₓ)
  obtain ⟨j, hj, hjT⟩ := fastErasedRank (notMem hyM) hc (by simpa only [image_insert] using heᵧ)
  have ranks {k : Fin A.card} {u v : ℚ} (hp : 0 < u)
      (he : T = (A.erase (A.orderEmbOfFin rfl k)).image (fun z ↦ u * z + v)) :
      (fun n : Fin (A.card - 1) ↦ u * entry A (skipRank k.val n.val) + v) =
        ⇑(T.orderEmbOfFin hT) := by
    apply orderEmbOfFin_unique hT
    · intro n
      exact he ▸ mem_image.mpr ⟨_, entry_skipRank_mem_erase A k n, rfl⟩
    · exact (fastAffine_strictMono hp).comp (strictMono_entry_skipRank A k)
  have hne : i ≠ j := by
    intro hij
    subst j
    have heq := (ranks ha hiT).trans (ranks hc hjT).symm
    have he0 := congrFun heq (⟨0, by omega⟩ : Fin (A.card - 1))
    have he1 := congrFun heq (⟨1, by omega⟩ : Fin (A.card - 1))
    have hlt : entry A (skipRank i.val 0) < entry A (skipRank i.val 1) :=
      entry_lt (strictMono_skipRank i.val (by decide : 0 < 1)) (skipRank_lt (by omega))
    obtain ⟨rfl, rfl⟩ := affine_eq_of_eq_at hlt he0 he1
    exact hxy (Nat.cast_injective (R := ℚ) (hi.symm.trans hj))
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact ⟨i, j, hij, fastCopy_of_common_image hc ha hjT hiT⟩
  · exact ⟨j, i, hji, fastCopy_of_common_image ha hc hiT hjT⟩

-- The common shape of Figures 4 and 5, before duplicating the branch above the root.
private structure FourFork (A : Finset ℚ) where
  u : ℚ
  x : ℚ
  a : ℚ
  b : ℚ
  y : ℚ
  c : ℚ
  d : ℚ
  nodup : [0, u, x, a, b, y, c, d].Nodup
  left₀ : IsRatCopy A {0, u, x, a}
  left₁ : IsRatCopy A {0, u, x, b}
  right₀ : IsRatCopy A {0, u, y, c}
  right₁ : IsRatCopy A {0, u, y, d}

-- A signed change of coordinates on the pattern and the board leaves the leaf scales positive.
private theorem copy_image_mul {A B : Finset ℚ} (hAB : IsRatCopy A B) (m t : ℚ) :
    IsRatCopy (A.image fun z ↦ m * z + t) (B.image fun z ↦ m * z) := by
  obtain ⟨a, b, ha, rfl⟩ := hAB
  refine ⟨a, m * b - a * t, ha, ?_⟩
  rw [image_image, image_image]
  congr 1
  funext z
  simp only [Function.comp_apply]
  ring

private def FourFork.image {A : Finset ℚ} (F : FourFork A) {m : ℚ} (hm : m ≠ 0) (t : ℚ) :
    FourFork (A.image fun z ↦ m * z + t) := by
  obtain ⟨u, x, a, b, y, c, d, hn, ha, hb, hc, hd⟩ := F
  refine ⟨m * u, m * x, m * a, m * b, m * y, m * c, m * d, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [List.map_cons, List.map_nil, mul_zero] using
      hn.map (mul_right_injective₀ hm)
  · simpa only [image_insert, image_singleton, mul_zero] using copy_image_mul ha m t
  · simpa only [image_insert, image_singleton, mul_zero] using copy_image_mul hb m t
  · simpa only [image_insert, image_singleton, mul_zero] using copy_image_mul hc m t
  · simpa only [image_insert, image_singleton, mul_zero] using copy_image_mul hd m t

-- Figure 4 works directly for every k > 0, including decreasing gaps and an arithmetic progression.
private def geometricFork (k : ℚ) (hk : 0 < k) : FourFork {0, 1, 1 + k, 1 + k + k ^ 2} := by
  let t := 1 + k
  let w := 1 + k + k ^ 2
  have ht : 1 < t := by dsimp [t]; linarith
  have ht₀ : 0 < t := by linarith
  have hkt : k < k * t := by nlinarith only [mul_pos hk (sub_pos.mpr ht)]
  have htw : t < w := by dsimp [t, w]; nlinarith only [sq_pos_of_pos hk]
  have hww : w < t * t := by dsimp [t, w]; nlinarith only [hk]
  have h0 : -1 / k < -1 / (k * t) := by
    simpa only [neg_div, neg_lt_neg_iff] using one_div_lt_one_div_of_lt hk hkt
  have h1 : -1 / (k * t) < 0 := div_neg_of_neg_of_pos (by norm_num) (mul_pos hk ht₀)
  have h2 : 0 < 1 / t := one_div_pos.mpr ht₀
  have h3 : 1 / t < 1 := (div_lt_one ht₀).mpr ht
  have h4 : 1 < w / t := (one_lt_div ht₀).mpr htw
  have h5 : w / t < t := (div_lt_iff₀ ht₀).mpr hww
  refine ⟨1, 1 / t, -1 / (k * t), w / t, t, -1 / k, w, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_false_eq_true,
      not_or]
    repeat' constructor
    all_goals (intro h; linarith only [h, h0, h1, h2, h3, h4, h5, htw])
  · change IsRatCopy {0, 1, t, w} _
    refine ⟨1 / (k * t), -1 / (k * t), by positivity, ?_⟩
    have he₁ : 1 / (k * t) * 1 + -1 / (k * t) = 0 := by ring
    have he₂ : 1 / (k * t) * t + -1 / (k * t) = 1 / t := by
      field_simp [hk.ne', ht₀.ne']; dsimp [t]; ring
    have he₃ : 1 / (k * t) * w + -1 / (k * t) = 1 := by
      field_simp [hk.ne', ht₀.ne']; dsimp [w, t]; ring
    simp only [image_insert, image_singleton, mul_zero, zero_add, he₁, he₂, he₃]
    ext z
    simp only [mem_insert, mem_singleton]
    tauto
  · change IsRatCopy {0, 1, t, w} _
    refine ⟨1 / t, 0, by positivity, ?_⟩
    have he₂ : 1 / t * t = 1 := by field_simp [ht₀.ne']
    have he₃ : 1 / t * w = w / t := by ring
    simp only [image_insert, image_singleton, mul_zero, mul_one, add_zero, he₂, he₃]
    ext z
    simp only [mem_insert, mem_singleton]
    tauto
  · change IsRatCopy {0, 1, t, w} _
    refine ⟨1 / k, -1 / k, by positivity, ?_⟩
    have he₁ : 1 / k * 1 + -1 / k = 0 := by ring
    have he₂ : 1 / k * t + -1 / k = 1 := by field_simp [hk.ne']; dsimp [t]; ring
    have he₃ : 1 / k * w + -1 / k = t := by field_simp [hk.ne']; dsimp [w, t]; ring
    simp only [image_insert, image_singleton, mul_zero, zero_add, he₁, he₂, he₃]
    ext z
    simp only [mem_insert, mem_singleton]
    tauto
  · change IsRatCopy {0, 1, t, w} {0, 1, t, w}
    exact ⟨1, 0, one_pos, by simp⟩

-- Figure 5, with its four increasing affine leaf maps.
private def zeroGeometricFork (k : ℚ) (hk : 1 < k) : FourFork {0, 1, k, k ^ 2} := by
  let t := k - 1
  have hk₀ : 0 < k := by linarith
  have ht : 0 < t := sub_pos.mpr hk
  have htk : t < k := by dsimp [t]; linarith
  have hkk : k < k ^ 2 := by nlinarith only [mul_pos hk₀ (sub_pos.mpr hk)]
  have h0 : -1 / t < -1 / k := by
    simpa only [neg_div, neg_lt_neg_iff] using one_div_lt_one_div_of_lt ht htk
  have h1 : -1 / k < 0 := div_neg_of_neg_of_pos (by norm_num) hk₀
  have h2 : 0 < 1 / k ^ 2 := by positivity
  have h3 : 1 / k ^ 2 < 1 / k := one_div_lt_one_div_of_lt hk₀ hkk
  have h4 : 1 / k < 1 := (div_lt_one hk₀).mpr hk
  have h5 : k < 1 + k := by linarith
  refine ⟨1, 1 / k, 1 / k ^ 2, k, -1 / t, -1 / k, 1 + k, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_false_eq_true,
      not_or]
    repeat' constructor
    all_goals (intro h; linarith only [h, h0, h1, h2, h3, h4, hk, h5])
  · refine ⟨1 / k ^ 2, 0, by positivity, ?_⟩
    have he₂ : 1 / k ^ 2 * k = 1 / k := by field_simp [hk₀.ne']
    have he₃ : 1 / k ^ 2 * k ^ 2 = 1 := by field_simp [hk₀.ne']
    simp only [image_insert, image_singleton, mul_zero, mul_one, add_zero, he₂, he₃]
    ext z
    simp only [mem_insert, mem_singleton]
    tauto
  · refine ⟨1 / k, 0, by positivity, ?_⟩
    have he₂ : 1 / k * k = 1 := by field_simp [hk₀.ne']
    have he₃ : 1 / k * k ^ 2 = k := by field_simp [hk₀.ne']
    simp only [image_insert, image_singleton, mul_zero, mul_one, add_zero, he₂, he₃]
    ext z
    simp only [mem_insert, mem_singleton]
    tauto
  · refine ⟨1 / (k * t), -1 / t, by positivity, ?_⟩
    have he₁ : 1 / (k * t) * 1 + -1 / t = -1 / k := by
      field_simp [hk₀.ne', ht.ne']; dsimp [t]; ring
    have he₂ : 1 / (k * t) * k + -1 / t = 0 := by field_simp [hk₀.ne', ht.ne']; ring
    have he₃ : 1 / (k * t) * k ^ 2 + -1 / t = 1 := by
      field_simp [hk₀.ne', ht.ne']; dsimp [t]; ring
    simp only [image_insert, image_singleton, mul_zero, zero_add, he₁, he₂, he₃]
    ext z
    simp only [mem_insert, mem_singleton]
    tauto
  · refine ⟨1 / t, -1 / t, by positivity, ?_⟩
    have he₁ : 1 / t * 1 + -1 / t = 0 := by ring
    have he₂ : 1 / t * k + -1 / t = 1 := by field_simp [ht.ne']; dsimp [t]; ring
    have he₃ : 1 / t * k ^ 2 + -1 / t = 1 + k := by field_simp [ht.ne']; dsimp [t]; ring
    simp only [image_insert, image_singleton, mul_zero, zero_add, he₁, he₂, he₃]
    ext z
    simp only [mem_insert, mem_singleton]
    tauto

private theorem eq_entries_four {A : Finset ℚ} (hA : A.card = 4) :
    A = {entry A 0, entry A 1, entry A 2, entry A 3} := by
  have hm (n : ℕ) (hn : n < A.card) : entry A n ∈ A := by
    rw [entry, dite_eq_left hn]
    exact A.orderEmbOfFin_mem rfl _
  ext z
  simp only [mem_insert, mem_singleton]
  constructor
  · intro hz
    have hr : z ∈ Set.range (A.orderEmbOfFin rfl) := by simpa using hz
    obtain ⟨i, rfl⟩ := hr
    have h : entry A i = A.orderEmbOfFin rfl i := by simp [entry, i.isLt]
    rw [← h]
    have hi := i.isLt
    have hs : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by omega
    rcases hs with h0 | h1 | h2 | h3
    · exact Or.inl (congrArg (entry A) h0)
    · exact Or.inr (Or.inl (congrArg (entry A) h1))
    · exact Or.inr (Or.inr (Or.inl (congrArg (entry A) h2)))
    · exact Or.inr (Or.inr (Or.inr (congrArg (entry A) h3)))
  · rintro (rfl | rfl | rfl | rfl) <;> exact hm _ (by omega)

private theorem fork_of_symmetric_four {A : Finset ℚ} (hA : A.card = 4)
    (h : IsSymmetric A) : Nonempty (FourFork A) := by
  obtain ⟨i, j, hsym⟩ := h
  have hcases := isSymmetricOfType_cases A (by omega) i j hsym
  obtain ⟨_, k, b, hk, hcopy⟩ := hsym
  have hr := rankMatch_of_image hk hcopy
  let z₀ := entry A 0
  let z₁ := entry A 1
  let z₂ := entry A 2
  let z₃ := entry A 3
  have he : A = {z₀, z₁, z₂, z₃} := eq_entries_four hA
  have h01 : z₀ < z₁ := entry_lt (by decide) (by omega)
  have h12 : z₁ < z₂ := entry_lt (by decide) (by omega)
  have h23 : z₂ < z₃ := entry_lt (by decide) (by omega)
  rcases hcases with ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩
  · -- The three consecutive gaps have common ratio k, even when k ≤ 1.
    have f₀ : k * z₀ + b = z₁ := hr.shift (k := 0) (by omega) (by omega) (by omega)
    have f₁ : k * z₁ + b = z₂ := hr.shift (k := 1) (by omega) (by omega) (by omega)
    have f₂ : k * z₂ + b = z₃ := hr.shift (k := 2) (by omega) (by omega) (by omega)
    let d := z₁ - z₀
    have hd : 0 < d := sub_pos.mpr h01
    have h₁ : d * 1 + z₀ = z₁ := by dsimp [d]; ring
    have h₂ : d * (1 + k) + z₀ = z₂ := by dsimp [d]; linear_combination f₁ - f₀
    have h₃ : d * (1 + k + k ^ 2) + z₀ = z₃ := by
      dsimp [d] at h₂ ⊢
      linear_combination f₂ - f₁ + (k + 1) * h₂
    have hf : A = ({0, 1, 1 + k, 1 + k + k ^ 2} : Finset ℚ).image (fun z ↦ d * z + z₀) := by
      rw [he]
      simp only [image_insert, image_singleton, mul_zero, zero_add, h₁, h₂, h₃]
    rw [hf]
    exact ⟨(geometricFork k hk).image hd.ne' z₀⟩
  · -- The affine rank map fixes the least point and scales the other gaps from it.
    have f₀ : k * z₀ + b = z₀ := hr.before (k := 0) (by omega) (by omega) (by omega)
    have f₁ : k * z₁ + b = z₂ := hr.shift (k := 1) (by omega) (by omega) (by omega)
    have f₂ : k * z₂ + b = z₃ := hr.shift (k := 2) (by omega) (by omega) (by omega)
    let d := z₁ - z₀
    have hd : 0 < d := sub_pos.mpr h01
    have h₁ : d * 1 + z₀ = z₁ := by dsimp [d]; ring
    have h₂ : d * k + z₀ = z₂ := by dsimp [d]; linear_combination f₁ - f₀
    have h₃ : d * k ^ 2 + z₀ = z₃ := by linear_combination f₂ - f₀ + k * h₂
    have hk₁ : 1 < k := by
      by_contra! hk₁
      nlinarith only [h₁, h₂, h12, mul_nonneg hd.le (sub_nonneg.mpr hk₁)]
    have hf : A = ({0, 1, k, k ^ 2} : Finset ℚ).image (fun z ↦ d * z + z₀) := by
      rw [he]
      simp only [image_insert, image_singleton, mul_zero, zero_add, h₁, h₂, h₃]
    rw [hf]
    exact ⟨(zeroGeometricFork k hk₁).image hd.ne' z₀⟩
  · -- The map now fixes the greatest point; reflection reverses the order of the ranks.
    have f₀ : k * z₀ + b = z₁ := hr.shift (k := 0) (by omega) (by omega) (by omega)
    have f₁ : k * z₁ + b = z₂ := hr.shift (k := 1) (by omega) (by omega) (by omega)
    have f₃ : k * z₃ + b = z₃ := by
      simpa only [show 2 + 1 = 3 by decide] using hr.after (k := 2) (by omega) (by omega) (by omega)
    have hb : k * (z₁ - z₃) = z₂ - z₃ := by linear_combination f₁ - f₃
    have ha : k * (z₀ - z₃) = z₁ - z₃ := by linear_combination f₀ - f₃
    have hk₁ : k < 1 := by
      by_contra! hk₁
      nlinarith only [hb, h12, mul_nonneg (sub_nonneg.mpr hk₁) (sub_nonneg.mpr (h12.trans h23).le)]
    let d := z₂ - z₃
    have hd : d < 0 := sub_neg.mpr h23
    have h₁ : d * 1 + z₃ = z₂ := by dsimp [d]; ring
    have hdiv (z w : ℚ) (hzw : k * (z - z₃) = w - z₃) : z = (w - z₃) / k + z₃ := by
      rw [show (w - z₃) / k = z - z₃ from (div_eq_iff hk.ne').mpr (by linarith only [hzw])]
      ring
    have h₂ : d * (1 / k) + z₃ = z₁ := by rw [hdiv _ _ hb]; dsimp [d]; ring
    have h₃ : d * (1 / k) ^ 2 + z₃ = z₀ := by rw [hdiv _ _ ha, ← h₂]; ring
    have hf : A = ({0, 1, 1 / k, (1 / k) ^ 2} : Finset ℚ).image (fun z ↦ d * z + z₃) := by
      rw [he]
      simp only [image_insert, image_singleton, mul_zero, zero_add, h₁, h₂, h₃]
      ext z
      simp only [mem_insert, mem_singleton]
      tauto
    rw [hf]
    exact ⟨(zeroGeometricFork (1 / k) ((one_lt_div hk).mpr hk₁)).image hd.ne z₃⟩

-- A reply can spoil at most one of two disjoint lists of remaining fork vertices.
private theorem forkStep {S M B : Finset ℕ} {p z : ℕ} {L R : List ℕ}
    (hn : (z :: L ++ R).Nodup)
    (hM : ∀ v ∈ z :: L ++ R, v ∉ M) (hB : ∀ v ∈ z :: L ++ R, v ∉ B)
    (left : ∀ B', (∀ v ∈ L, v ∉ insert z M) → (∀ v ∈ L, v ∉ B') →
      MakerWinsWithin S p (insert z M) B')
    (right : ∀ B', (∀ v ∈ R, v ∉ insert z M) → (∀ v ∈ R, v ∉ B') →
      MakerWinsWithin S p (insert z M) B') :
    MakerWinsWithin S (p + 1) M B := by
  obtain ⟨hz, hLR⟩ := List.nodup_cons.mp hn
  refine Or.inr ⟨z, hM z (by simp), hB z (by simp), fun w _ _ _ ↦ ?_⟩
  have hM' {Q : List ℕ} (hQ : ∀ v ∈ Q, v ∈ L ++ R) (v : ℕ) (hv : v ∈ Q) :
      v ∉ insert z M := by
    rw [mem_insert, not_or]
    exact ⟨fun he ↦ hz (he ▸ hQ v hv), hM v (List.mem_cons_of_mem _ (hQ v hv))⟩
  have hB' {Q : List ℕ} (hQ : ∀ v ∈ Q, v ∈ L ++ R) (hw : w ∉ Q) (v : ℕ) (hv : v ∈ Q) :
      v ∉ insert w B := by
    rw [mem_insert, not_or]
    exact ⟨fun he ↦ hw (he ▸ hv), hB v (List.mem_cons_of_mem _ (hQ v hv))⟩
  by_cases hw : w ∈ L
  · have hw' : w ∉ R := fun hr ↦ (List.nodup_append.mp hLR).2.2 w hw w hr rfl
    have hQ (v : ℕ) (hv : v ∈ R) : v ∈ L ++ R := List.mem_append.mpr (Or.inr hv)
    exact right _ (hM' hQ) (hB' hQ hw')
  · have hQ (v : ℕ) (hv : v ∈ L) : v ∈ L ++ R := List.mem_append.mpr (Or.inl hv)
    exact left _ (hM' hQ) (hB' hQ hw)

private theorem forkLastTwo {S M B : Finset ℕ} {x a b : ℕ}
    (hn : [x, a, b].Nodup)
    (hM : ∀ v ∈ [x, a, b], v ∉ M) (hB : ∀ v ∈ [x, a, b], v ∉ B)
    (ha : ContainsCopy S (insert a (insert x M))) (hb : ContainsCopy S (insert b (insert x M))) :
    MakerWinsWithin S 2 M B := by
  refine forkStep (p := 1) (L := [a]) (R := [b]) hn hM hB ?_ ?_
  · intro B' hM' hB'
    exact Or.inr ⟨a, hM' a (by simp), hB' a (by simp), fun _ _ _ _ ↦ ha⟩
  · intro B' hM' hB'
    exact Or.inr ⟨b, hM' b (by simp), hB' b (by simp), fun _ _ _ _ ↦ hb⟩

private theorem forkNatBranch {S B : Finset ℕ} {r u x a b y c d : ℕ}
    (hn : [u, x, a, b, y, c, d].Nodup)
    (hM : ∀ v ∈ [u, x, a, b, y, c, d], v ∉ ({r} : Finset ℕ))
    (hB : ∀ v ∈ [u, x, a, b, y, c, d], v ∉ B)
    (ha : ContainsCopy S {a, x, u, r}) (hb : ContainsCopy S {b, x, u, r})
    (hc : ContainsCopy S {c, y, u, r}) (hd : ContainsCopy S {d, y, u, r}) :
    MakerWinsWithin S 3 {r} B := by
  have htail : ([x, a, b] ++ [y, c, d]).Nodup := (List.nodup_cons.mp hn).2
  obtain ⟨hleft, hright, _⟩ := List.nodup_append.mp htail
  refine forkStep (p := 2) (L := [x, a, b]) (R := [y, c, d]) hn hM hB ?_ ?_
  · exact fun _ hM' hB' ↦ forkLastTwo hleft hM' hB' ha hb
  · exact fun _ hM' hB' ↦ forkLastTwo hright hM' hB' hc hd

-- Clear all vertex and affine-witness denominators by one positive natural scale.
private theorem forkClearDenominators (L : List ℚ) :
    ∃ D : ℕ, 0 < D ∧ ∀ v ∈ L, ∃ n : ℤ, (D : ℚ) * v = n := by
  induction L with
  | nil => exact ⟨1, Nat.one_pos, by simp⟩
  | cons v L ih =>
    obtain ⟨D, hD, hclear⟩ := ih
    refine ⟨v.den * D, Nat.mul_pos v.den_pos hD, ?_⟩
    intro w hw
    rw [List.mem_cons] at hw
    rcases hw with rfl | hw
    · have hnum : (w.den : ℚ) * w = w.num := by
        have hden : (w.den : ℚ) ≠ 0 := by exact_mod_cast w.den_pos.ne'
        simpa only [mul_comm] using (eq_div_iff hden).mp (Rat.num_div_den w).symm
      refine ⟨(D : ℤ) * w.num, ?_⟩
      push_cast
      rw [mul_right_comm, hnum, mul_comm]
    · obtain ⟨n, hn⟩ := hclear w hw
      refine ⟨(v.den : ℤ) * n, ?_⟩
      push_cast
      rw [mul_assoc, hn]

private theorem forkNatAbove (L : List ℚ) :
    ∃ K : ℕ, 0 < K ∧ ∀ v ∈ L, v < (K : ℚ) := by
  induction L with
  | nil => exact ⟨1, Nat.one_pos, by simp⟩
  | cons v L ih =>
    obtain ⟨K, hK, h⟩ := ih
    refine ⟨K + v.num.natAbs + 1, by omega, ?_⟩
    intro w hw
    rw [List.mem_cons] at hw
    rcases hw with rfl | hw
    · have hn : (w.num : ℚ) ≤ (w.num.natAbs : ℚ) := by
        simpa only [Int.cast_natCast] using
          (Int.cast_le (R := ℚ)).2 (Int.le_natAbs (a := w.num))
      have hd : (1 : ℚ) ≤ (w.den : ℚ) := by
        exact_mod_cast (show 1 ≤ w.den from w.den_pos)
      have hw' : w ≤ (w.num.natAbs : ℚ) := by
        calc
          w = (w.num : ℚ) / w.den := (Rat.num_div_den w).symm
          _ ≤ (w.num.natAbs : ℚ) := (div_le_iff₀ (by exact_mod_cast w.den_pos)).2 <|
            hn.trans (le_mul_of_one_le_right (by positivity) hd)
      push_cast
      linarith only [hw', show (0 : ℚ) ≤ K by positivity]
    · have hw' := h w hw
      push_cast
      linarith only [hw', show (0 : ℚ) ≤ v.num.natAbs by positivity]

-- Figures 4 and 5: duplicate the fork around its root before transporting it to ℕ.
private theorem winsFour_of_fork (S : Finset ℕ) {u x a b y c d : ℚ}
    (hn : [0, u, x, a, b, y, c, d].Nodup)
    (ha : IsRatCopy (S.image fun s : ℕ ↦ (s : ℚ)) {0, u, x, a})
    (hb : IsRatCopy (S.image fun s : ℕ ↦ (s : ℚ)) {0, u, x, b})
    (hc : IsRatCopy (S.image fun s : ℕ ↦ (s : ℚ)) {0, u, y, c})
    (hd : IsRatCopy (S.image fun s : ℕ ↦ (s : ℚ)) {0, u, y, d}) :
    MakerWinsWithin S 4 ∅ ∅ := by
  obtain ⟨ma, ta, hma, ea⟩ := ha
  obtain ⟨mb, tb, hmb, eb⟩ := hb
  obtain ⟨mc, tc, hmc, ec⟩ := hc
  obtain ⟨md, td, hmd, ed⟩ := hd
  let L := [u, x, a, b, y, c, d]
  have h0 : (0 : ℚ) ∉ L := (List.nodup_cons.mp hn).1
  have hL : L.Nodup := (List.nodup_cons.mp hn).2
  obtain ⟨K, hK, habove⟩ := forkNatAbove (L.flatMap fun w ↦ L.map (fun v ↦ v / w))
  let k : ℚ := K
  have hk : 0 < k := by
    dsimp [k]
    exact_mod_cast hK
  let V := 0 :: L ++ L.map (fun v ↦ k * v)
  have hV : V.Nodup := by
    refine List.nodup_cons.mpr ⟨?_, List.nodup_append.mpr ⟨hL, ?_, ?_⟩⟩
    · change (0 : ℚ) ∉ L ++ L.map (fun v ↦ k * v)
      rw [List.mem_append, not_or]
      exact ⟨h0, by
        rintro hm
        obtain ⟨v, hv, he⟩ := List.mem_map.mp hm
        exact h0 ((mul_eq_zero.mp he).resolve_left hk.ne' ▸ hv)⟩
    · exact List.Nodup.map (mul_right_injective₀ hk.ne') hL
    · intro v hv w hw hEq
      obtain ⟨w', hw', he⟩ := List.mem_map.mp hw
      rw [← he] at hEq
      have hw0 : w' ≠ 0 := fun he' ↦ h0 (he' ▸ hw')
      have hvw := habove (v / w') <| List.mem_flatMap.mpr
        ⟨w', hw', List.mem_map.mpr ⟨v, hv, rfl⟩⟩
      exact hvw.ne ((eq_div_iff hw0).2 hEq.symm).symm
  let A := [ma, ta, mb, tb, mc, tc, md, td]
  obtain ⟨D, hD, hclear⟩ := forkClearDenominators (V ++ (A ++ A.map (fun q ↦ k * q)))
  obtain ⟨T, _, hT⟩ := forkNatAbove (V.map fun v ↦ -((D : ℚ) * v))
  let f (v : ℚ) := ((D : ℚ) * v + T).num.toNat
  have hf (v : ℚ) (hv : v ∈ V) : (f v : ℚ) = (D : ℚ) * v + T := by
    obtain ⟨n, he⟩ := hclear v (List.mem_append.mpr (Or.inl hv))
    have hvT := hT (-((D : ℚ) * v)) (List.mem_map.mpr ⟨v, hv, rfl⟩)
    have hnT : 0 ≤ n + (T : ℤ) := by
      rw [he] at hvT
      have h : (0 : ℚ) ≤ (n : ℚ) + T := by linarith only [hvT]
      exact_mod_cast h
    have haff : (D : ℚ) * v + T = (↑(n + (T : ℤ)) : ℚ) := by rw [he]; push_cast; rfl
    have hcast := congrArg (fun i : ℤ ↦ (i : ℚ)) (Int.toNat_of_nonneg hnT)
    simpa only [f, haff, Rat.num_intCast, Int.cast_natCast] using hcast
  have hN : (V.map f).Nodup := hV.map_on fun v hv w hw he ↦ by
    have he' := congrArg (fun n : ℕ ↦ (n : ℚ)) he
    rw [hf v hv, hf w hw, add_right_cancel_iff] at he'
    exact mul_right_injective₀ (by exact_mod_cast hD.ne') he'
  have hcoeff (q m : ℚ) (hq : q = 1 ∨ q = k) (hm : m ∈ A) :
      ∃ n : ℤ, (D : ℚ) * (q * m) = n := by
    apply hclear
    apply List.mem_append.mpr ∘ Or.inr
    rcases hq with rfl | rfl
    · exact List.mem_append.mpr (Or.inl (by simpa using hm))
    · exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨m, hm, rfl⟩))
  have hscaled (q : ℚ) (hq : q = 1 ∨ q = k) (v : ℚ) (hv : v ∈ L) : q * v ∈ V := by
    apply List.mem_cons_of_mem
    rcases hq with rfl | rfl
    · exact List.mem_append.mpr (Or.inl (by simpa using hv))
    · exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨v, hv, rfl⟩))
  have leaf (q m t v w : ℚ) (hq : q = 1 ∨ q = k) (hm : m ∈ A) (ht : t ∈ A) (hmpos : 0 < m)
      (hv : v ∈ L) (hw : w ∈ L)
      (e : ({0, u, v, w} : Finset ℚ) =
        (S.image fun s : ℕ ↦ (s : ℚ)).image (fun s ↦ m * s + t)) :
      ContainsCopy S {f (q * w), f (q * v), f (q * u), f 0} := by
    obtain ⟨n, hn⟩ := hcoeff q m hq hm
    obtain ⟨i, hi⟩ := hcoeff q t hq ht
    have hqpos : 0 < q := by
      rcases hq with rfl | rfl
      · exact one_pos
      · exact hk
    have hnpos : 0 < n := by
      have h : 0 < (D : ℚ) * (q * m) := mul_pos (by exact_mod_cast hD) (mul_pos hqpos hmpos)
      rw [hn] at h
      exact_mod_cast h
    have hncast : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hnpos.le
    refine ⟨n.toNat, by omega, i + T, fun s hs ↦ ?_⟩
    let z : ℚ := m * (s : ℚ) + t
    have hz : z ∈ ({0, u, v, w} : Finset ℚ) := by
      rw [e]
      exact mem_image.mpr ⟨_, mem_image.mpr ⟨s, hs, rfl⟩, rfl⟩
    have hmem : q * z ∈ V := by
      simp only [mem_insert, mem_singleton] at hz
      rcases hz with he | he | he | he
      · rw [he, mul_zero]
        simp [V]
      · exact he ▸ hscaled q hq u (by simp [L])
      · exact he ▸ hscaled q hq v hv
      · exact he ▸ hscaled q hq w hw
    refine ⟨f (q * z), ?_, ?_⟩
    · simp only [mem_insert, mem_singleton] at hz ⊢
      rcases hz with he | he | he | he
      · exact Or.inr (Or.inr (Or.inr (by rw [he, mul_zero])))
      · exact Or.inr (Or.inr (Or.inl (by rw [he])))
      · exact Or.inr (Or.inl (by rw [he]))
      · exact Or.inl (by rw [he])
    · have hz' : (f (q * z) : ℚ) = (n : ℚ) * s + ((i : ℚ) + T) := by
        calc
          (f (q * z) : ℚ) = (D : ℚ) * (q * z) + T := hf _ hmem
          _ = ((D : ℚ) * (q * m)) * s + ((D : ℚ) * (q * t) + T) := by
            simp only [z, mul_add, mul_assoc, add_assoc]
          _ = _ := by rw [hn, hi]
      change (f (q * z) : ℤ) = (n.toNat : ℤ) * (s : ℤ) + (i + T)
      rw [hncast]
      exact_mod_cast hz'
  have branch (q : ℚ) (hq : q = 1 ∨ q = k) {B : Finset ℕ}
      (hn' : (L.map fun v ↦ f (q * v)).Nodup)
      (hM' : ∀ v ∈ L.map (fun v ↦ f (q * v)), v ∉ ({f 0} : Finset ℕ))
      (hB' : ∀ v ∈ L.map (fun v ↦ f (q * v)), v ∉ B) :
      MakerWinsWithin S 3 {f 0} B :=
    forkNatBranch hn' hM' hB'
      (leaf q ma ta x a hq (by simp [A]) (by simp [A]) hma (by simp [L]) (by simp [L]) ea)
      (leaf q mb tb x b hq (by simp [A]) (by simp [A]) hmb (by simp [L]) (by simp [L]) eb)
      (leaf q mc tc y c hq (by simp [A]) (by simp [A]) hmc (by simp [L]) (by simp [L]) ec)
      (leaf q md td y d hq (by simp [A]) (by simp [A]) hmd (by simp [L]) (by simp [L]) ed)
  let P := L.map f
  let Q := L.map (fun v ↦ f (k * v))
  have hNPQ : (f 0 :: P ++ Q).Nodup := by
    simpa only [V, P, Q, List.map_cons, List.map_append, List.map_map, Function.comp_def] using hN
  obtain ⟨hP, hQ, _⟩ := List.nodup_append.mp (List.nodup_cons.mp hNPQ).2
  refine forkStep (p := 3) hNPQ (by simp) (by simp) ?_ ?_
  · have hPL : L.map (fun v ↦ f (1 * v)) = P := by simp [P]
    intro B hM' hB'
    apply branch 1 (Or.inl rfl) (B := B) <;> rwa [hPL]
  · exact fun _ hM' hB' ↦ branch k (Or.inr rfl) hQ hM' hB'

/-- **Four-element sets with a four-move win are the symmetric ones.** If $S$ is a set of four
natural numbers, then, starting from the position where no number has been claimed, Maker wins
the $S$-game within $4$ moves if and only if $S$, viewed as a set of rationals, is symmetric.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40, Theorem 6
(`integers-2026-A40-thm-6`). -/
public theorem makerWinsWithin_four_iff_isSymmetric (S : Finset ℕ)
    (hS : S.card = 4) :
    MakerWinsWithin S 4 ∅ ∅ ↔ IsSymmetric (S.image fun s : ℕ => (s : ℚ)) := by
  constructor
  · exact symmetric_of_winsFour hS
  · intro h
    have hcard : (S.image fun s : ℕ ↦ (s : ℚ)).card = 4 := by
      rw [card_image_of_injective _ Nat.cast_injective, hS]
    obtain ⟨F⟩ := fork_of_symmetric_four hcard h
    exact winsFour_of_fork S F.nodup F.left₀ F.left₁ F.right₀ F.right₁

end MetaMathlibExt.FastVanDerWaerdenGame
