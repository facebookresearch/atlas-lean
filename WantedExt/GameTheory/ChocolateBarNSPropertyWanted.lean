/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Indicator
public import Mathlib.Algebra.Group.Even
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Order.Lattice.Nat

/-! # The NS property of chocolate-bar games (Miyadera, Manabe, Singh)

Arithmetic lemmas on the `NS` property and nim-sums from R. Miyadera, H. Manabe and
A. Singh, *Generalizations of Two-Dimensional and Three-Dimensional Chocolate Bar Games*,
INTEGERS 25 (2025), Article G3. The definition of the `NS` property is taken from the
arXiv version (arXiv:2207.09134v1, Section 2); nim-sum `⊕` is `Nat.xor` (`^^^`) and
`Z≥0` is `ℕ`.

The game theorems use the published move sets: `chocolateBarGrundy` is the Grundy number of the
bar `CB(f₁, …, f_s, x₁, …, x_s, z)` of Definitions 2, 9, 10 and Section 4 (the column at width
`w` has extent `min (f t w) (x t) + 1` along axis `t`), and `heightChocolateBarGrundy` is the
Grundy number of the bar `CB(F, x₁, …, x_s, y)` of Definitions 13, 15 and 17 (the column at
`(u₁, …, u_s)` has height `min (F u) y + 1`). Both are defined on all coordinate tuples by the
mex recursion over the paper's move sets; the theorems quantify over the actual bars, i.e. the
positions with `x t ≤ f t z`, respectively `y ≤ F x`, a set closed under moves. A P-position is
a position of Grundy number `0` (Theorem 1 (i), the classical Sprague-Grundy theorem).
-/

namespace MetaMathlibExt

@[expose] public section

/-- A function `h : ℕ → ℕ` has the *NS property* if it is monotonically increasing and,
whenever `⌊z / 2^i⌋ = ⌊z' / 2^i⌋` for a natural number `i ≥ 1`, also
`⌊h z / 2^(i-1)⌋ = ⌊h z' / 2^(i-1)⌋`.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Definition 11 (text of arXiv:2207.09134v1, NS property in Section 2). -/
public def HasNSProperty (h : ℕ → ℕ) : Prop :=
  Monotone h ∧ ∀ z z' i : ℕ, 0 < i → z / 2 ^ i = z' / 2 ^ i →
    h z / 2 ^ (i - 1) = h z' / 2 ^ (i - 1)

/-- Constant functions have the NS property.

Source: characteristic lemma for the NS property of Miyadera, Manabe and Singh,
INTEGERS 25 (2025), Article G3, Definition 11. -/
public theorem hasNSProperty_const (c : ℕ) : HasNSProperty fun _ ↦ c :=
  ⟨monotone_const, fun _ _ _ _ _ ↦ rfl⟩

/-- The identity function does not have the NS property (`⌊0/2⌋ = ⌊1/2⌋` but `0 ≠ 1`).

Source: characteristic lemma for the NS property of Miyadera, Manabe and Singh,
INTEGERS 25 (2025), Article G3, Definition 11. -/
public theorem not_hasNSProperty_id : ¬ HasNSProperty id := fun h ↦ by
  have := h.2 0 1 1 Nat.one_pos rfl
  simp at this

/-- A function that is monotone and satisfies the NS condition on `[0, z]` extends to a
function with the NS property by the constant value `h z` beyond `z`.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Lemma 1 (`integers-2025-G3-lem-1`). -/
public theorem_wanted hasNSProperty_extend_const (z : ℕ) (h : ℕ → ℕ)
    (hmono : ∀ a b, a ≤ b → b ≤ z → h a ≤ h b)
    (hns : ∀ a b i : ℕ, a ≤ z → b ≤ z → 0 < i → a / 2 ^ i = b / 2 ^ i →
      h a / 2 ^ (i - 1) = h b / 2 ^ (i - 1)) :
    HasNSProperty fun x ↦ if x ≤ z then h x else h z

/-- If `⌊a / 2^k⌋ = ⌊b / 2^k⌋`, then `⌊min a c / 2^k⌋ = ⌊min b c / 2^k⌋` for every `c`.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Lemma 2 (i) (`integers-2025-G3-lem-2`). -/
public theorem_wanted min_div_two_pow_eq_of_div_two_pow_eq {a b k : ℕ}
    (hab : a / 2 ^ k = b / 2 ^ k) (c : ℕ) :
    min a c / 2 ^ k = min b c / 2 ^ k

/-- If `h` has the NS property, `k ≥ 1` and `⌊z' / 2^k⌋ = ⌊z / 2^k⌋`, then
`⌊min (h z') y / 2^(k-1)⌋ = ⌊min (h z) y / 2^(k-1)⌋` for every `y`.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Lemma 2 (ii) (`integers-2025-G3-lem-2`). -/
public theorem_wanted HasNSProperty.min_div_two_pow_eq {h : ℕ → ℕ} (hh : HasNSProperty h)
    {z z' k : ℕ} (hk : 0 < k) (hz : z' / 2 ^ k = z / 2 ^ k) (y : ℕ) :
    min (h z') y / 2 ^ (k - 1) = min (h z) y / 2 ^ (k - 1)

/-- Two-dimensional mex step: if `g` has the NS property, `x ≤ g z` and `c < x ⊕ z`, then
`c = u ⊕ z` for some `u < x`, or `c = min (g w) x ⊕ w` for some `w < z`.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Lemma 3 (a) (`integers-2025-G3-lem-3`). -/
public theorem_wanted HasNSProperty.exists_of_lt_xor {g : ℕ → ℕ} (hg : HasNSProperty g)
    {x z c : ℕ} (hx : x ≤ g z) (hc : c < x ^^^ z) :
    (∃ u < x, c = u ^^^ z) ∨ ∃ w < z, c = min (g w) x ^^^ w

/-- Three-dimensional mex step: if `g`, `h` have the NS property, `x ≤ g z`, `y ≤ h z` and
`c < x ⊕ y ⊕ z`, then `c = u ⊕ y ⊕ z` with `u < x`, or `c = x ⊕ v ⊕ z` with `v < y`, or
`c = min (g w) x ⊕ min (h w) y ⊕ w` with `w < z`.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Lemma 3 (b) (`integers-2025-G3-lem-3`). -/
public theorem_wanted HasNSProperty.exists_of_lt_xor_xor {g h : ℕ → ℕ}
    (hg : HasNSProperty g) (hh : HasNSProperty h) {x y z c : ℕ} (hx : x ≤ g z)
    (hy : y ≤ h z) (hc : c < x ^^^ y ^^^ z) :
    (∃ u < x, c = u ^^^ y ^^^ z) ∨ (∃ v < y, c = x ^^^ v ^^^ z) ∨
      ∃ w < z, c = min (g w) x ^^^ min (h w) y ^^^ w

/-- Multidimensional mex step: let `f t` (`t < m`) have the NS property, `x t ≤ f t z`, and
`c < x 0 ⊕ ⋯ ⊕ x (m-1) ⊕ z`. Then either `c` is obtained by lowering one `x i` to some
`u < x i`, or `c = min (x 0) (f 0 w) ⊕ ⋯ ⊕ min (x (m-1)) (f (m-1) w) ⊕ w` for some `w < z`.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Lemma 4 (`integers-2025-G3-lem-4`). -/
public theorem_wanted exists_of_lt_foldl_xor {m : ℕ} {f : Fin m → ℕ → ℕ}
    (hf : ∀ t, HasNSProperty (f t)) {x : Fin m → ℕ} {z c : ℕ} (hx : ∀ t, x t ≤ f t z)
    (hc : c < (List.ofFn x).foldl (· ^^^ ·) 0 ^^^ z) :
    (∃ i, ∃ u < x i, c = (List.ofFn (Function.update x i u)).foldl (· ^^^ ·) 0 ^^^ z) ∨
      ∃ w < z, c = (List.ofFn fun t ↦ min (x t) (f t w)).foldl (· ^^^ ·) 0 ^^^ w

/-- Identity (19): if `g`, `h` have the NS property, `x ≤ g z` and `y ≤ h z`, then
`{x ⊕ y ⊕ w : w < z} = {min (g w') x ⊕ min (h w') y ⊕ w' : w' < z}`.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Lemma 5, equation (19) (`integers-2025-G3-lem-5`). -/
public theorem_wanted HasNSProperty.image_xor_xor_eq {g h : ℕ → ℕ} (hg : HasNSProperty g)
    (hh : HasNSProperty h) {x y z : ℕ} (hx : x ≤ g z) (hy : y ≤ h z) :
    {c | ∃ w < z, c = x ^^^ y ^^^ w} = {c | ∃ w' < z, c = min (g w') x ^^^ min (h w') y ^^^ w'}

/-- Identity (20): if `g` has the NS property and `x ≤ g z`, then
`{x ⊕ w : w < z} = {min (g w') x ⊕ w' : w' < z}`.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Lemma 5, equation (20) (`integers-2025-G3-lem-5`). -/
public theorem_wanted HasNSProperty.image_xor_eq {g : ℕ → ℕ} (hg : HasNSProperty g)
    {x z : ℕ} (hx : x ≤ g z) :
    {c | ∃ w < z, c = x ^^^ w} = {c | ∃ w' < z, c = min (g w') x ^^^ w'}

/-- For every natural number `m ≥ 1`, the function `x ↦ ⌊x / 2^m⌋` has the NS property.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Lemma 7 (`integers-2025-G3-lem-7`). -/
public theorem_wanted hasNSProperty_div_two_pow {m : ℕ} (hm : 0 < m) :
    HasNSProperty fun x ↦ x / 2 ^ m

/-- For `z < z'`, `⌊z / 2^i⌋ = ⌊z' / 2^i⌋` if and only if `d 2^i ≤ z < z' < (d + 1) 2^i`
for some `d`.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Lemma 8 (a) (`integers-2025-G3-lem-8`). -/
public theorem_wanted div_two_pow_eq_iff_exists_block {z z' i : ℕ} (hzz' : z < z') :
    z / 2 ^ i = z' / 2 ^ i ↔ ∃ d, d * 2 ^ i ≤ z ∧ z' < (d + 1) * 2 ^ i

/-- If `⌊z / 2^i⌋ < ⌊z' / 2^i⌋`, there are `c`, `s ≥ i` and `t < 2^s` with
`z = c 2^(s+1) + t < c 2^(s+1) + 2^s ≤ z'`.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Lemma 8 (b) (`integers-2025-G3-lem-8`). -/
public theorem_wanted exists_split_of_div_two_pow_lt {z z' i : ℕ}
    (h : z / 2 ^ i < z' / 2 ^ i) :
    ∃ c s t : ℕ, i ≤ s ∧ t < 2 ^ s ∧ z = c * 2 ^ (s + 1) + t ∧
      c * 2 ^ (s + 1) + 2 ^ s ≤ z'

/-- A monotone function `f : ℕ → ℕ` with `f ≤ 1` that takes the value `1` is the indicator
of `[m, ∞)` for an even `m` if and only if it has the NS property.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Lemma 9 (`integers-2025-G3-lem-9`). -/
public theorem_wanted indicator_Ici_even_iff_hasNSProperty {f : ℕ → ℕ} (hf : Monotone f)
    (hle : ∀ x, f x ≤ 1) (hone : ∃ x, f x = 1) :
    (∃ m, Even m ∧ f = (Set.Ici m).indicator 1) ↔ HasNSProperty f

/-- Grundy number of the chocolate bar `CB(f₁, …, f_s, x₁, …, x_s, z)` with width `z`, whose
column at width `w ≤ z` extends `min (f t w) (x t) + 1` cells along axis `t`. A move either
lowers one coordinate `x i` to some `u < x i`, or cuts the width to some `w < z`, which clamps
every `x t` to `min (x t) (f t w)`; the value is the mex (least natural number not attained) of
the Grundy numbers of the positions reachable in one move. It is defined on all coordinate
tuples; the bars themselves are the positions with `x t ≤ f t z` for all `t`.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Definitions 2, 8, 9 and 10 (two functions) and Section 4, before Theorem 5
(four functions). -/
public noncomputable def chocolateBarGrundy {s : ℕ} (f : Fin s → ℕ → ℕ) (x : Fin s → ℕ)
    (z : ℕ) : ℕ :=
  sInf {m | (∀ i u, u < x i → chocolateBarGrundy f (Function.update x i u) z ≠ m) ∧
    ∀ w, w < z → chocolateBarGrundy f (fun t ↦ min (x t) (f t w)) w ≠ m}
termination_by z + ∑ t, x t
decreasing_by
  · have hlt : ∑ t, Function.update x i u t < ∑ t, x t := by
      refine Finset.sum_lt_sum (fun j _ ↦ ?_) ⟨i, Finset.mem_univ _, by simpa⟩
      by_cases hj : j = i
      · subst hj; simp only [Function.update_self]; omega
      · simp [Function.update_of_ne hj]
    omega
  · have hle : ∑ t, min (x t) (f t w) ≤ ∑ t, x t :=
      Finset.sum_le_sum fun _ _ ↦ min_le_left _ _
    omega

/-- The defining mex recursion of `chocolateBarGrundy`.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Definitions 9 and 10. -/
public theorem chocolateBarGrundy_eq {s : ℕ} (f : Fin s → ℕ → ℕ) (x : Fin s → ℕ) (z : ℕ) :
    chocolateBarGrundy f x z =
      sInf {m | (∀ i u, u < x i → chocolateBarGrundy f (Function.update x i u) z ≠ m) ∧
        ∀ w, w < z → chocolateBarGrundy f (fun t ↦ min (x t) (f t w)) w ≠ m} := by
  rw [chocolateBarGrundy]

/-- The single bitter square `CB(f, 0, …, 0, 0)` has no move, so its Grundy number is `0`.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Definitions 9 and 10. -/
public theorem chocolateBarGrundy_zero {s : ℕ} (f : Fin s → ℕ → ℕ) :
    chocolateBarGrundy f (fun _ ↦ 0) 0 = 0 := by
  rw [chocolateBarGrundy_eq]
  exact Nat.sInf_eq_zero.mpr (Or.inl ⟨fun _ u hu ↦ absurd hu (Nat.not_lt_zero u),
    fun w hw ↦ absurd hw (Nat.not_lt_zero w)⟩)

/-- Grundy number of the `(s + 1)`-dimensional chocolate bar `CB(F, x₁, …, x_s, y)`, whose
column at `(u₁, …, u_s)` (with `u t ≤ x t`) has height `min (F u) y + 1`. A move either lowers
one coordinate `x i` to some `u < x i`, which clamps the height to `min (F x') y` for the new
position `x'`, or lowers the height `y` to some `v < y`; the value is the mex of the Grundy
numbers of the positions reachable in one move. It is defined on all coordinate tuples; the bars
themselves are the positions with `y ≤ F x`.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Definitions 15, 16 and 17 (and Definition 13 with second function `0`). -/
public noncomputable def heightChocolateBarGrundy {s : ℕ} (F : (Fin s → ℕ) → ℕ)
    (x : Fin s → ℕ) (y : ℕ) : ℕ :=
  sInf {m | (∀ i u, u < x i → heightChocolateBarGrundy F (Function.update x i u)
      (min (F (Function.update x i u)) y) ≠ m) ∧
    ∀ v, v < y → heightChocolateBarGrundy F x v ≠ m}
termination_by (∑ t, x t) + y
decreasing_by
  · have hlt : ∑ t, Function.update x i u t < ∑ t, x t := by
      refine Finset.sum_lt_sum (fun j _ ↦ ?_) ⟨i, Finset.mem_univ _, by simpa⟩
      by_cases hj : j = i
      · subst hj; simp only [Function.update_self]; omega
      · simp [Function.update_of_ne hj]
    have := min_le_right (F (Function.update x i u)) y
    omega
  · omega

/-- The defining mex recursion of `heightChocolateBarGrundy`.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Definition 17. -/
public theorem heightChocolateBarGrundy_eq {s : ℕ} (F : (Fin s → ℕ) → ℕ) (x : Fin s → ℕ)
    (y : ℕ) :
    heightChocolateBarGrundy F x y =
      sInf {m | (∀ i u, u < x i → heightChocolateBarGrundy F (Function.update x i u)
          (min (F (Function.update x i u)) y) ≠ m) ∧
        ∀ v, v < y → heightChocolateBarGrundy F x v ≠ m} := by
  rw [heightChocolateBarGrundy]

/-- The single bitter cube `CB(F, 0, …, 0, 0)` has no move, so its Grundy number is `0`.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Definition 17. -/
public theorem heightChocolateBarGrundy_zero {s : ℕ} (F : (Fin s → ℕ) → ℕ) :
    heightChocolateBarGrundy F (fun _ ↦ 0) 0 = 0 := by
  rw [heightChocolateBarGrundy_eq]
  exact Nat.sInf_eq_zero.mpr (Or.inl ⟨fun _ u hu ↦ absurd hu (Nat.not_lt_zero u),
    fun v hv ↦ absurd hv (Nat.not_lt_zero v)⟩)

/-- The pass indicator of Nim with a restricted pass: `1` if `m j ≤ x j` for some pile `j`
(the pass may be used), and `0` if `x j < m j` for every pile.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Lemma 10 and Corollary 2 (the function `F`). -/
public def nimPassIndicator {s : ℕ} (m x : Fin s → ℕ) : ℕ :=
  if ∃ j, m j ≤ x j then 1 else 0

/-- The pass indicator takes values in `{0, 1}`.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Lemma 10 (the function `F`). -/
public theorem nimPassIndicator_le_one {s : ℕ} (m x : Fin s → ℕ) : nimPassIndicator m x ≤ 1 := by
  unfold nimPassIndicator; split_ifs <;> omega

/-- With positive thresholds the pass is not available from the empty position.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Lemma 10 (the function `F`). -/
public theorem nimPassIndicator_zero {s : ℕ} {m : Fin s → ℕ} (hm : ∀ i, 0 < m i) :
    nimPassIndicator m (fun _ ↦ 0) = 0 := by
  rw [nimPassIndicator, ite_eq_right_iff]
  rintro ⟨j, hj⟩
  exact absurd hj (Nat.not_le.mpr (hm j))

/-- Identity of Lemma 6: if `f t` (`t < m`) have the NS property and `x t ≤ f t z`, then
`{x 0 ⊕ ⋯ ⊕ x (m-1) ⊕ w : w < z} = {min (x 0) (f 0 w) ⊕ ⋯ ⊕ min (x (m-1)) (f (m-1) w) ⊕ w : w < z}`.
The printed left-hand nim-sum carries a stray index `j ≠ i` with `i` unbound; it is read as the
full nim-sum, as in Lemma 5 (the case of two functions), which the proof generalises.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Lemma 6 (`integers-2025-G3-lem-6`). -/
public theorem_wanted image_foldl_xor_eq_image_min {m : ℕ} {f : Fin m → ℕ → ℕ}
    (hf : ∀ t, HasNSProperty (f t)) {x : Fin m → ℕ} {z : ℕ} (hx : ∀ t, x t ≤ f t z) :
    {c | ∃ w < z, c = (List.ofFn x).foldl (· ^^^ ·) 0 ^^^ w} =
      {c | ∃ w < z, c = (List.ofFn fun t ↦ min (x t) (f t w)).foldl (· ^^^ ·) 0 ^^^ w}

/-- A monotone `f` has the NS property iff the chocolate bar `CB(f, 0, x, 0, z)` (height
function `f`, depth function `0`, depth `0`) has Grundy number `x ⊕ z` at every bar position
`x ≤ f z`.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Theorem 2 (`integers-2025-G3-thm-2`). -/
public theorem_wanted hasNSProperty_iff_chocolateBarGrundy_depth_zero {f : ℕ → ℕ}
    (hf : Monotone f) :
    HasNSProperty f ↔
      ∀ x z, x ≤ f z → chocolateBarGrundy ![f, fun _ ↦ 0] ![x, 0] z = x ^^^ z

/-- Let `F` be monotone in both variables. The sections `x ↦ F n x` and `w ↦ F w n` all have
the NS property iff the three-dimensional chocolate bar `CB(F, 0, w, x, y, 0)` (depth function
`0`, depth `0`) has Grundy number `w ⊕ x ⊕ y` at every bar position `y ≤ F w x`.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Theorem 3 (`integers-2025-G3-thm-3`). -/
public theorem_wanted sections_hasNSProperty_iff_heightChocolateBarGrundy_eq_xor
    {F : ℕ → ℕ → ℕ} (hF : Monotone fun p : ℕ × ℕ ↦ F p.1 p.2) :
    ((∀ n, HasNSProperty (F n)) ∧ ∀ n, HasNSProperty fun w ↦ F w n) ↔
      ∀ w x y, y ≤ F w x →
        heightChocolateBarGrundy (fun v ↦ F (v 0) (v 1)) ![w, x] y = w ^^^ x ^^^ y

/-- For monotone `g` and `h`, both have the NS property iff the chocolate bar with depth
`CB(g, h, x, y, z)` has Grundy number `x ⊕ y ⊕ z` at every bar position `x ≤ g z`, `y ≤ h z`.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Theorem 4 (`integers-2025-G3-thm-4`). -/
public theorem_wanted hasNSProperty_and_iff_chocolateBarGrundy_eq_xor {g h : ℕ → ℕ}
    (hg : Monotone g) (hh : Monotone h) :
    HasNSProperty g ∧ HasNSProperty h ↔
      ∀ x y z, x ≤ g z → y ≤ h z → chocolateBarGrundy ![g, h] ![x, y] z = x ^^^ y ^^^ z

/-- For monotone `f 0, …, f 3`, all four have the NS property iff the five-coordinate chocolate
bar `CB(f₁, f₂, f₃, f₄, x₁, x₂, x₃, x₄, z)` has Grundy number `x₁ ⊕ x₂ ⊕ x₃ ⊕ x₄ ⊕ z` at every
bar position `x t ≤ f t z`.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Theorem 5 (`integers-2025-G3-thm-5`). -/
public theorem_wanted forall_hasNSProperty_iff_chocolateBarGrundy_eq_xor_four
    {f : Fin 4 → ℕ → ℕ} (hf : ∀ t, Monotone (f t)) :
    (∀ t, HasNSProperty (f t)) ↔
      ∀ (x : Fin 4 → ℕ) z, (∀ t, x t ≤ f t z) →
        chocolateBarGrundy f x z = x 0 ^^^ x 1 ^^^ x 2 ^^^ x 3 ^^^ z

/-- For `F (w, x) = ⌊(w + x) / k⌋` with `k = 4m + 3`, a bar position `y ≤ F (w, x)` of
`CB(F, 0, w, x, y, 0)` is a P-position (Grundy number `0`) iff `w ⊕ x ⊕ y = 0`.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Theorem 8 (`integers-2025-G3-thm-8`). -/
public theorem_wanted heightChocolateBarGrundy_add_div_eq_zero_iff {k : ℕ} (hk : k % 4 = 3)
    {w x y : ℕ} (hy : y ≤ (w + x) / k) :
    heightChocolateBarGrundy (fun v ↦ (v 0 + v 1) / k) ![w, x] y = 0 ↔ w ^^^ x ^^^ y = 0

/-- Let `F` be monotone with `F ≤ 1`, and suppose every section `t ↦ F (x[i ↦ t])` takes the
value `1` (the hypothesis of Lemma 9, from which the corollary is derived). Then every section is
the indicator of `[m, ∞)` for an even `m` (depending on the fixed coordinates) iff
`CB(F, x₁, …, x_s, y)` has Grundy number `x₁ ⊕ ⋯ ⊕ x_s ⊕ y` at every bar position `y ≤ F x`.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Corollary 1 (`integers-2025-G3-cor-1`). -/
public theorem_wanted indicator_sections_iff_heightChocolateBarGrundy_eq_xor {s : ℕ}
    {F : (Fin s → ℕ) → ℕ} (hF : Monotone F) (hle : ∀ x, F x ≤ 1)
    (hone : ∀ (x : Fin s → ℕ) i, ∃ t, F (Function.update x i t) = 1) :
    (∀ (x : Fin s → ℕ) i, ∃ m, Even m ∧
        (fun t ↦ F (Function.update x i t)) = (Set.Ici m).indicator 1) ↔
      ∀ x y, y ≤ F x → heightChocolateBarGrundy F x y = (List.ofFn x).foldl (· ^^^ ·) 0 ^^^ y

/-- For positive thresholds `m i`, every section `t ↦ nimPassIndicator m (x[i ↦ t])` has the NS
property iff every `m i` is even.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Lemma 10 (`integers-2025-G3-lem-10`). -/
public theorem_wanted nimPassIndicator_sections_hasNSProperty_iff {s : ℕ} {m : Fin s → ℕ}
    (hm : ∀ i, 0 < m i) :
    (∀ (x : Fin s → ℕ) i, HasNSProperty fun t ↦ nimPassIndicator m (Function.update x i t)) ↔
      ∀ i, Even (m i)

/-- Nim on `s` piles with a one-time pass usable only while `m j ≤ x j` for some pile `j`,
played as the chocolate bar `CB(F, x₁, …, x_s, p)` with `F = nimPassIndicator m`: removing
stones sets `p` to `min (F x') p`, and the pass lowers `p` from `1` to `0`. For positive
thresholds, the Grundy number is `x₁ ⊕ ⋯ ⊕ x_s ⊕ p` at every position with `p ≤ F x` iff every
`m i` is even.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Corollary 2 (`integers-2025-G3-cor-2`). -/
public theorem_wanted nimPassGrundy_eq_xor_iff {s : ℕ} {m : Fin s → ℕ} (hm : ∀ i, 0 < m i) :
    (∀ (x : Fin s → ℕ) p, p ≤ nimPassIndicator m x →
        heightChocolateBarGrundy (nimPassIndicator m) x p =
          (List.ofFn x).foldl (· ^^^ ·) 0 ^^^ p) ↔
      ∀ i, Even (m i)

end

end MetaMathlibExt
