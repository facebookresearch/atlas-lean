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

end MetaMathlibExt.FastVanDerWaerdenGame
