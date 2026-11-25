/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import MathlibExt.Combinatorics.Additive.ConsecutiveZeroSum

/-!
# Orthogonal vectors over `ZMod 2`

The first `2 ^ a` columns form a sequence of length equal to the order of the group
`Fin a → ZMod 2`. A consecutive zero sum in that group vanishes in every row
(`exists_consecutive_orthogonal`).

For the indicator vectors of sets of natural numbers, the resulting block in `{1, …, m}`
meets each set in an even number of elements (`exists_consecutive_even_inter`).

When `a < m`, the `2 ^ m` vectors of `Fin m → ZMod 2` have only `2 ^ a` possible products with
`a` given vectors, so the difference of two vectors with equal products is a nonzero common
orthogonal vector (`exists_ne_zero_orthogonal`). Applied to the indicator vectors on
`{1, …, m}` of `a` finite sets of natural numbers, it gives a nonempty `Y ⊆ {1, …, m}` meeting
each of the sets in an even number of elements (`exists_nonempty_even_inter`).
-/

namespace MetaMathlibExt

/-- **A block of consecutive coordinates orthogonal to $a$ vectors of $\mathbb{Z}_2^m$.** Let
$\mathbb{Z}_2 = \mathbb{Z}/2\mathbb{Z}$, let $2^a \le m$ and let
$v_1, \dots, v_a \in \mathbb{Z}_2^m$, with coordinates indexed by $\{0, \dots, m - 1\}$. Then there
are indices $s \le t$ in $\{0, \dots, m - 1\}$ such that $\sum_{j = s}^{t} (v_i)_j = 0$ in
$\mathbb{Z}_2$ for every $i$; that is, the nonzero vector whose ones occupy exactly the positions
$s, \dots, t$ is orthogonal to every $v_i$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Lemma 3.2 (`integers-2024-A38-lem-3-2`). -/
public theorem exists_consecutive_orthogonal {a m : ℕ} (hm : 2 ^ a ≤ m)
    (v : Fin a → Fin m → ZMod 2) :
    ∃ s t : Fin m, s ≤ t ∧ ∀ i, ∑ j ∈ Finset.Icc s t, v i j = 0 := by
  have hblock := (consecutive_constant_eq_card (Fin a → ZMod 2)).1.2
  rw [Fintype.card_fun, ZMod.card, Fintype.card_fin] at hblock
  obtain ⟨s, t, hst, w, hw, hsum⟩ := hblock (fun j i => v i (j.castLE hm))
  refine ⟨s.castLE hm, t.castLE hm, hst, fun i => ?_⟩
  rw [← Fin.map_castLEEmb_Icc s t hm, Finset.sum_map]
  have hrow := congrFun hsum i
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply] at hrow
  exact (Finset.sum_congr rfl fun j hj => by
    simp [show w j = 1 from hw j hj]).trans hrow

/-- **A block of consecutive integers meeting $a$ given sets evenly.** Let $2^a \le m$ and let
$X_1, \dots, X_a$ be finite sets of natural numbers. Then there are integers $s, t$ with
$1 \le s \le t \le m$ such that $|\{s, s + 1, \dots, t\} \cap X_i|$ is even for every $i$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Lemma 3.3 (`integers-2024-A38-lem-3-3`). -/
public theorem exists_consecutive_even_inter {a m : ℕ} (hm : 2 ^ a ≤ m)
    (X : Fin a → Finset ℕ) :
    ∃ s t : ℕ, 1 ≤ s ∧ s ≤ t ∧ t ≤ m ∧ ∀ i, Even (Finset.Icc s t ∩ X i).card := by
  obtain ⟨s, t, hst, hsum⟩ := exists_consecutive_orthogonal hm
    fun i j => if j.val + 1 ∈ X i then (1 : ZMod 2) else 0
  refine ⟨(s.succ : ℕ), (t.succ : ℕ), Nat.succ_pos _, Nat.succ_le_succ hst, t.isLt, fun i => ?_⟩
  rw [← ZMod.natCast_eq_zero_iff_even, ← Finset.filter_mem_eq_inter, Finset.natCast_card_filter,
    ← Fin.map_valEmbedding_Icc s.succ t.succ, ← Fin.map_succEmb_Icc, Finset.sum_map, Finset.sum_map]
  exact hsum i

/-- **A nonzero vector of $\mathbb{Z}_2^m$ orthogonal to $a$ vectors when $a < m$.** Let
$\mathbb{Z}_2 = \mathbb{Z}/2\mathbb{Z}$, let $a + 1 \le m$ and let
$v_1, \dots, v_a \in \mathbb{Z}_2^m$. Then there is a nonzero $w \in \mathbb{Z}_2^m$ with
$w \cdot v_i = \sum_j w_j (v_i)_j = 0$ in $\mathbb{Z}_2$ for every $i$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Lemma 4.2 (`integers-2024-A38-lem-4-2`). -/
public theorem exists_ne_zero_orthogonal {a m : ℕ} (hm : a + 1 ≤ m)
    (v : Fin a → Fin m → ZMod 2) :
    ∃ w : Fin m → ZMod 2, w ≠ 0 ∧ ∀ i, ∑ j, w j * v i j = 0 := by
  let f (x : Fin m → ZMod 2) (i : Fin a) : ZMod 2 := ∑ j, x j * v i j
  have hnoninj : ¬ Function.Injective f := by
    intro hf
    have hcard := Fintype.card_le_of_injective f hf
    simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin] at hcard
    have hlt : 2 ^ a < 2 ^ m := Nat.pow_lt_pow_right (by decide) (Nat.lt_of_succ_le hm)
    exact (not_le_of_gt hlt) hcard
  obtain ⟨x, y, hxy, hne⟩ := Function.not_injective_iff.mp hnoninj
  refine ⟨x - y, sub_ne_zero.mpr hne, fun i => ?_⟩
  simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  exact sub_eq_zero.mpr (congrFun hxy i)

/-- **A nonempty subset of $\{1, \dots, m\}$ meeting $a$ given sets evenly.** Let $a + 1 \le m$
and let $X_1, \dots, X_a$ be finite sets of natural numbers. Then there is a nonempty set
$Y \subseteq \{1, \dots, m\}$ such that $|Y \cap X_i|$ is even for every $i$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Lemma 4.3 (`integers-2024-A38-lem-4-3`). -/
public theorem exists_nonempty_even_inter {a m : ℕ} (hm : a + 1 ≤ m)
    (X : Fin a → Finset ℕ) :
    ∃ Y : Finset ℕ, Y.Nonempty ∧ Y ⊆ Finset.Icc 1 m ∧ ∀ i, Even (Y ∩ X i).card := by
  have h01 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  -- Shift `Fin m` onto `{1, …, m}` and take the indicator vectors of the sets `X i`.
  let e : Fin m ↪ ℕ := ⟨fun j => (j : ℕ) + 1, fun j k h => Fin.ext (Nat.add_right_cancel h)⟩
  obtain ⟨w, hw, horth⟩ := exists_ne_zero_orthogonal hm
    fun i j => if e j ∈ X i then (1 : ZMod 2) else 0
  refine ⟨(Finset.univ.filter fun j => w j = 1).map e, ?_, ?_, fun i => ?_⟩
  · obtain ⟨j, hj⟩ := Function.ne_iff.mp hw
    refine ⟨e j, Finset.mem_map_of_mem e (Finset.mem_filter.mpr ⟨Finset.mem_univ j, ?_⟩)⟩
    exact (h01 (w j)).resolve_left hj
  · intro n hn
    obtain ⟨j, -, rfl⟩ := Finset.mem_map.mp hn
    exact Finset.mem_Icc.mpr ⟨Nat.le_add_left 1 j, j.isLt⟩
  · rw [← ZMod.natCast_eq_zero_iff_even, ← Finset.filter_mem_eq_inter, Finset.filter_map,
      Finset.card_map, Finset.filter_filter, Finset.natCast_card_filter]
    refine (Finset.sum_congr rfl fun j _ => ?_).trans (horth i)
    rcases h01 (w j) with h | h <;> simp [h]

end MetaMathlibExt
