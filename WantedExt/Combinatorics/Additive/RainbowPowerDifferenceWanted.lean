/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Basic.Real.Basic

/-! # Rainbow-free colorings for `x - y = z ^ k`

Statement-only requests from Ansaldi, Cowley, Green, Kim and Rapp. A coloring `c` is
rainbow-free for `x - y = z ^ k` when no solution has `c x`, `c y`, `c z` pairwise distinct,
and exact when every color is used (`Function.Surjective c`). The digraph `G^k_p` has vertex
set `ZMod p` and edges `a → a ^ k`; two vertices lie in the same (weak) component exactly when
`a ^ k ^ m = b ^ k ^ n` for some `m n : ℕ`. Color-class sizes are `Nat.card`s of subtypes.
-/

namespace MetaMathlibExt

@[expose] public section

/-- An exact rainbow-free 3-coloring of `ℤ/pℤ` for `x - y = z ^ k` has a color class of size
one.

Source: Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free
Colorings and Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Corollary 1
(`integers-2024-A105-cor-1`). -/
public theorem_wanted exists_card_colorClass_eq_one_of_rainbowFree_powDiff
    (p k : ℕ) [Fact p.Prime] (c : ZMod p → Fin 3) (hc : Function.Surjective c)
    (hrf : ∀ x y z : ZMod p, x - y = z ^ k → ¬ (c x ≠ c y ∧ c y ≠ c z ∧ c x ≠ c z)) :
    ∃ i : Fin 3, Nat.card {a : ZMod p // c a = i} = 1

/-- In an exact rainbow-free 3-coloring of `ℤ/pℤ` for `x - y = z ^ k`, `0` is the only element
of its color class.

Source: Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free
Colorings and Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Corollary 2
(`integers-2024-A105-cor-2`). -/
public theorem_wanted eq_zero_of_color_eq_color_zero_of_rainbowFree_powDiff
    (p k : ℕ) [Fact p.Prime] (c : ZMod p → Fin 3) (hc : Function.Surjective c)
    (hrf : ∀ x y z : ZMod p, x - y = z ^ k → ¬ (c x ≠ c y ∧ c y ≠ c z ∧ c x ≠ c z))
    (a : ZMod p) (ha : c a = c 0) : a = 0

/-- A rainbow-free 3-coloring of `ℤ/nℤ` for `x - y = z ^ k` lifts to a rainbow-free coloring
`i ↦ c (i mod n)` of the positive integers.

Source: Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free
Colorings and Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Lemma 7
(`integers-2024-A105-lem-7`). -/
public theorem_wanted rainbowFree_powDiff_lift_of_zmod
    (n k : ℕ) (c : ZMod n → Fin 3)
    (hrf : ∀ x y z : ZMod n, x - y = z ^ k → ¬ (c x ≠ c y ∧ c y ≠ c z ∧ c x ≠ c z))
    (x y z : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x = y + z ^ k) :
    ¬ (c x ≠ c y ∧ c y ≠ c z ∧ c x ≠ c z)

/-- For a coloring of the positive integers that is periodic mod `n`, two positive integers
`i₁, i₂` with `gcd(|i₁ - i₂|, n) = 1` can be replaced by coprime positive integers `j₁, j₂` of
the same colors and the same distance.

Source: Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free
Colorings and Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Lemma 8
(`integers-2024-A105-lem-8`). -/
public theorem_wanted exists_coprime_same_colors_of_coprime_dist
    (n : ℕ) (c : ZMod n → Fin 3) (i₁ i₂ : ℕ) (hi₁ : 0 < i₁) (hi₂ : 0 < i₂)
    (hd : Nat.Coprime ((i₁ : ℤ) - i₂).natAbs n) :
    ∃ j₁ j₂ : ℕ, 0 < j₁ ∧ 0 < j₂ ∧ Nat.Coprime j₁ j₂ ∧ c j₁ = c i₁ ∧ c j₂ = c i₂ ∧
      ((j₁ : ℤ) - j₂).natAbs = ((i₁ : ℤ) - i₂).natAbs

/-- An exact rainbow-free 3-coloring of `ℤ/pℤ` for `x - y = z ^ k` satisfies
`c a = c (-a)`.

Source: Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free
Colorings and Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Lemma 10
(`integers-2024-A105-lem-10`). -/
public theorem_wanted color_neg_eq_of_rainbowFree_powDiff
    (p k : ℕ) [Fact p.Prime] (c : ZMod p → Fin 3) (hc : Function.Surjective c)
    (hrf : ∀ x y z : ZMod p, x - y = z ^ k → ¬ (c x ≠ c y ∧ c y ≠ c z ∧ c x ≠ c z))
    (a : ZMod p) : c (-a) = c a

/-- Every component of the digraph `G^k_p` of `a ↦ a ^ k` on `ℤ/pℤ` contains exactly one
cycle: every vertex reaches a cycle vertex, and two cycle vertices in the same component lie
on one orbit.

Source: Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free
Colorings and Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Lemma 12
(`integers-2024-A105-lem-12`). -/
public theorem_wanted powMap_component_unique_cycle (p k : ℕ) [Fact p.Prime] :
    (∀ a : ZMod p, ∃ m : ℕ, ∃ r : ℕ, 0 < r ∧ (a ^ k ^ m) ^ k ^ r = a ^ k ^ m) ∧
      ∀ a b : ZMod p, (∃ r : ℕ, 0 < r ∧ a ^ k ^ r = a) → (∃ r : ℕ, 0 < r ∧ b ^ k ^ r = b) →
        (∃ m n : ℕ, a ^ k ^ m = b ^ k ^ n) → ∃ m : ℕ, a ^ k ^ m = b

/-- For even `k > 0`, the digraph `G^k_p` has exactly two components iff every prime factor of
`p - 1` divides `k` (the source's `p - 1 = 2^{β₀} q₁^{β₁} ⋯ q_ℓ^{β_ℓ}`, `β_i ≥ 0`, where
`k = 2^{α₀} q₁^{α₁} ⋯ q_ℓ^{α_ℓ}`).

Source: Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free
Colorings and Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Proposition 1
(`integers-2024-A105-prop-1`). -/
public theorem_wanted card_powMap_components_eq_two_iff_of_even
    (p k : ℕ) [Fact p.Prime] (hk : Even k) (hk0 : 0 < k) :
    Nat.card (Quot fun a b : ZMod p => ∃ m n : ℕ, a ^ k ^ m = b ^ k ^ n) = 2 ↔
      ∀ q : ℕ, q.Prime → q ∣ p - 1 → q ∣ k

/-- For odd `k ≥ 3`, the digraph `G^k_p` has exactly three components iff `p - 1 = 2 m` with
every prime factor of `m` dividing `k`.

Source: Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free
Colorings and Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Proposition 2
(`integers-2024-A105-prop-2`). -/
public theorem_wanted card_powMap_components_eq_three_iff_of_odd
    (p k : ℕ) [Fact p.Prime] (hk : Odd k) (hk3 : 3 ≤ k) :
    Nat.card (Quot fun a b : ZMod p => ∃ m n : ℕ, a ^ k ^ m = b ^ k ^ n) = 3 ↔
      ∃ m : ℕ, p - 1 = 2 * m ∧ ∀ q : ℕ, q.Prime → q ∣ m → q ∣ k

/-- If `gcd(i, j) = g` for positive integers `i, j`, then every sufficiently large multiple of
`g` is `u i + v j` with `u, v ≥ 0`.

Source: Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free
Colorings and Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Theorem 2
(`integers-2024-A105-thm-2`). -/
public theorem_wanted exists_forall_gcd_dvd_eq_add_mul (i j : ℕ) (hi : 0 < i) (hj : 0 < j) :
    ∃ n₀ : ℕ, ∀ m : ℕ, n₀ < m → Nat.gcd i j ∣ m → ∃ u v : ℕ, m = u * i + v * j

/-- For `k ≥ 2` and `s = ⌊k / 2⌋`, every 3-coloring of the positive integers in which every
color class has upper density greater than `(4^s - 1) / (3 · 4^s)` contains a rainbow solution
of `x - y = z ^ k` in positive integers. Upper density `> δ` is rendered as: for some `ε > 0`,
infinitely many `N` have more than `(δ + ε) N` elements of the class in `[1, N]`.

Source: Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free
Colorings and Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Theorem 3
(`integers-2024-A105-thm-3`). -/
public theorem_wanted exists_rainbow_powDiff_of_upperDensity (k : ℕ) (hk : 2 ≤ k)
    (c : ℕ → Fin 3)
    (hdens : ∀ i : Fin 3, ∃ ε : ℝ, 0 < ε ∧ ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧
      ((4 : ℝ) ^ (k / 2) - 1) / (3 * 4 ^ (k / 2)) + ε <
        (((Finset.Icc 1 N).filter fun x => c x = i).card : ℝ) / N) :
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x = y + z ^ k ∧
      c x ≠ c y ∧ c y ≠ c z ∧ c x ≠ c z

/-- For odd `n` with smallest prime factor `r₁`, an exact rainbow-free 3-coloring of `ℤ/nℤ`
for `x - y = z ^ k` has a color class of size at most `n / r₁`.

Source: Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free
Colorings and Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Theorem 4
(`integers-2024-A105-thm-4`). -/
public theorem_wanted exists_card_colorClass_le_div_minFac_of_rainbowFree_powDiff
    (n k : ℕ) (hn : Odd n) (c : ZMod n → Fin 3) (hc : Function.Surjective c)
    (hrf : ∀ x y z : ZMod n, x - y = z ^ k → ¬ (c x ≠ c y ∧ c y ≠ c z ∧ c x ≠ c z)) :
    ∃ i : Fin 3, Nat.card {a : ZMod n // c a = i} ≤ n / n.minFac

/-- An exact 3-coloring of `ℤ/pℤ` is rainbow-free for `x - y = z ^ k` iff `0` is alone in its
color class, every component of `G^k_p` is monochromatic, and `c a = c (-a)` for all `a`.

Source: Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free
Colorings and Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Theorem 5
(`integers-2024-A105-thm-5`). -/
public theorem_wanted rainbowFree_powDiff_iff
    (p k : ℕ) [Fact p.Prime] (c : ZMod p → Fin 3) (hc : Function.Surjective c) :
    (∀ x y z : ZMod p, x - y = z ^ k → ¬ (c x ≠ c y ∧ c y ≠ c z ∧ c x ≠ c z)) ↔
      (∀ a : ZMod p, c a = c 0 → a = 0) ∧
        (∀ a b : ZMod p, (∃ m n : ℕ, a ^ k ^ m = b ^ k ^ n) → c a = c b) ∧
        ∀ a : ZMod p, c (-a) = c a

/-- Rainbow number for even `k`: the least `r` such that every exact `r`-coloring of `ℤ/pℤ`
contains a rainbow solution of `x - y = z ^ k` is `3` if every prime factor of `p - 1` divides
`k`, and `4` otherwise. The infimum ranges over `r ≥ 3` (a rainbow solution needs three colors; `r = 0`
would hold vacuously, as there is no map `ZMod p → Fin 0`).

Source: Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free
Colorings and Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Theorem 7
(`integers-2024-A105-thm-7`). -/
public theorem_wanted rainbowNumber_powDiff_of_even (p k : ℕ) [Fact p.Prime] (hk : Even k) :
    ((∀ q : ℕ, q.Prime → q ∣ p - 1 → q ∣ k) →
      sInf {r : ℕ | 3 ≤ r ∧ ∀ c : ZMod p → Fin r, Function.Surjective c →
        ∃ x y z : ZMod p, x - y = z ^ k ∧ c x ≠ c y ∧ c y ≠ c z ∧ c x ≠ c z} = 3) ∧
    (¬ (∀ q : ℕ, q.Prime → q ∣ p - 1 → q ∣ k) →
      sInf {r : ℕ | 3 ≤ r ∧ ∀ c : ZMod p → Fin r, Function.Surjective c →
        ∃ x y z : ZMod p, x - y = z ^ k ∧ c x ≠ c y ∧ c y ≠ c z ∧ c x ≠ c z} = 4)

/-- Rainbow number for odd `k ≥ 3` and odd primes `p`: it is `3` if `p - 1 = 2 m` with every
prime factor of `m` dividing `k`, and `4` otherwise.

Source: Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free
Colorings and Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Theorem 8
(`integers-2024-A105-thm-8`). -/
public theorem_wanted rainbowNumber_powDiff_of_odd (p k : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (hk : Odd k) (hk3 : 3 ≤ k) :
    ((∃ m : ℕ, p - 1 = 2 * m ∧ ∀ q : ℕ, q.Prime → q ∣ m → q ∣ k) →
      sInf {r : ℕ | 3 ≤ r ∧ ∀ c : ZMod p → Fin r, Function.Surjective c →
        ∃ x y z : ZMod p, x - y = z ^ k ∧ c x ≠ c y ∧ c y ≠ c z ∧ c x ≠ c z} = 3) ∧
    (¬ (∃ m : ℕ, p - 1 = 2 * m ∧ ∀ q : ℕ, q.Prime → q ∣ m → q ∣ k) →
      sInf {r : ℕ | 3 ≤ r ∧ ∀ c : ZMod p → Fin r, Function.Surjective c →
        ∃ x y z : ZMod p, x - y = z ^ k ∧ c x ≠ c y ∧ c y ≠ c z ∧ c x ≠ c z} = 4)


/-- In an exact rainbow-free coloring `c` of the positive integers with `r` colors for
`x - y = z ^ k`, the color `c 1` is dominant: every bichromatic string `i, i + 1, …, i + ℓ - 1`
(`i ≥ 1`) contains it.

Source: Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free
Colorings and Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Lemma 1
(`integers-2024-A105-lem-1`). -/
public theorem_wanted color_one_dominant_of_rainbowFree_powDiff (r k : ℕ) (c : ℕ → Fin r)
    (hc : ∀ j : Fin r, ∃ i : ℕ, 0 < i ∧ c i = j)
    (hrf : ∀ x y z : ℕ, 0 < x → 0 < y → 0 < z → x = y + z ^ k →
      ¬ (c x ≠ c y ∧ c y ≠ c z ∧ c x ≠ c z))
    (i ℓ : ℕ) (hi : 0 < i) (hbi : ((Finset.Ico i (i + ℓ)).image c).card = 2) :
    c 1 ∈ (Finset.Ico i (i + ℓ)).image c

/-- Let `c` be a rainbow-free 3-coloring of the positive integers for `x - y = z ^ k` with a
dominant color `R` (every bichromatic string contains `R`), and let `B ≠ G` be the two other
colors. If `c j = B`, then every string of color `G` at position `i` of length `ℓ` moves to a
monochromatic string of color `B` or `G` at position `i + jᵏ`, and at position `i - jᵏ` when
`jᵏ < i`.

Source: Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free
Colorings and Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Lemma 2
(`integers-2024-A105-lem-2`). -/
public theorem_wanted monochromatic_shift_of_rainbowFree_powDiff (k : ℕ) (c : ℕ → Fin 3)
    (hrf : ∀ x y z : ℕ, 0 < x → 0 < y → 0 < z → x = y + z ^ k →
      ¬ (c x ≠ c y ∧ c y ≠ c z ∧ c x ≠ c z))
    (R B G : Fin 3) (hRB : R ≠ B) (hRG : R ≠ G) (hBG : B ≠ G)
    (hdom : ∀ i ℓ : ℕ, 0 < i → ((Finset.Ico i (i + ℓ)).image c).card = 2 →
      R ∈ (Finset.Ico i (i + ℓ)).image c)
    (j : ℕ) (hj : 0 < j) (hcj : c j = B) (i ℓ : ℕ) (hi : 0 < i)
    (hG : ∀ t < ℓ, c (i + t) = G) :
    (∃ e : Fin 3, (e = B ∨ e = G) ∧ ∀ t < ℓ, c (i + j ^ k + t) = e) ∧
      (j ^ k < i → ∃ e : Fin 3, (e = B ∨ e = G) ∧ ∀ t < ℓ, c (i - j ^ k + t) = e)

/-- Zhan's small-gap lemma: if `S ⊆ ℕ` has counting function `S(n) = #(S ∩ [1, n])` with
`limsup (S(n) - n / n₀) = ∞` for an integer `n₀ ≥ 2`, then some `1 ≤ d ≤ n₀ - 1` has `j` and
`j + d` both in `S` for arbitrarily large `j`. The record's display is garbled; it is read from
arXiv:2305.15133.

Source: Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free
Colorings and Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Lemma 3
(`integers-2024-A105-lem-3`). -/
public theorem_wanted exists_small_gap_of_limsup_count (S : Set ℕ) [DecidablePred (· ∈ S)]
    (n₀ : ℕ) (hn₀ : 2 ≤ n₀)
    (hS : ∀ M : ℝ, ∀ N₀ : ℕ, ∃ n : ℕ, N₀ ≤ n ∧
      M < (((Finset.Icc 1 n).filter (· ∈ S)).card : ℝ) - n / n₀) :
    ∃ d : ℕ, 1 ≤ d ∧ d ≤ n₀ - 1 ∧ ∀ i : ℕ, ∃ j : ℕ, i < j ∧ j ∈ S ∧ j + d ∈ S

/-- If a rainbow-free 3-coloring `c` of the positive integers for `x - y = z ^ k` satisfies
`limsup (min(R(n), B(n), G(n)) - n / n₀) = ∞` for an integer `n₀ ≥ 2` (color-class counting
functions on `[1, n]`), then for every dominant color `d` the monochromatic strings of a color
other than `d` have bounded length.

Source: Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free
Colorings and Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Lemma 4
(`integers-2024-A105-lem-4`). -/
public theorem_wanted nondominant_string_length_bounded (k : ℕ) (c : ℕ → Fin 3)
    (hrf : ∀ x y z : ℕ, 0 < x → 0 < y → 0 < z → x = y + z ^ k →
      ¬ (c x ≠ c y ∧ c y ≠ c z ∧ c x ≠ c z))
    (n₀ : ℕ) (hn₀ : 2 ≤ n₀)
    (hdens : ∀ M : ℝ, ∀ N₀ : ℕ, ∃ n : ℕ, N₀ ≤ n ∧ ∀ e : Fin 3,
      M < (((Finset.Icc 1 n).filter fun x => c x = e).card : ℝ) - n / n₀)
    (d : Fin 3) (hdom : ∀ i ℓ : ℕ, 0 < i → ((Finset.Ico i (i + ℓ)).image c).card = 2 →
      d ∈ (Finset.Ico i (i + ℓ)).image c) :
    ∃ L : ℕ, ∀ i ℓ : ℕ, 0 < i → c i ≠ d → (∀ t < ℓ, c (i + t) = c i) → ℓ ≤ L

/-- Let `c` be a rainbow-free 3-coloring of the positive integers for `x - y = z ^ k` with
dominant color `R` (every bichromatic string contains `R`), and let `B ≠ G` be the two other
colors. If coprime positive `j₁, j₂` both have color `G`, then at most one of them has the
`A`-property: an infinite `B`-monochromatic arithmetic progression `i, i + jᵏ, i + 2jᵏ, …` of
positive integers. The density condition of Lemma 4 (`n₀ ≥ 2`) is added: the paper's proof
ends by contradicting Lemma 4, which needs it.

Source: Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free
Colorings and Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Lemma 5
(`integers-2024-A105-lem-5`); `A`-property as defined before Lemma 5 in arXiv:2305.15133. -/
public theorem_wanted not_both_aProperty_of_coprime (k : ℕ) (c : ℕ → Fin 3)
    (hrf : ∀ x y z : ℕ, 0 < x → 0 < y → 0 < z → x = y + z ^ k →
      ¬ (c x ≠ c y ∧ c y ≠ c z ∧ c x ≠ c z))
    (n₀ : ℕ) (hn₀ : 2 ≤ n₀)
    (hdens : ∀ M : ℝ, ∀ N₀ : ℕ, ∃ n : ℕ, N₀ ≤ n ∧ ∀ e : Fin 3,
      M < (((Finset.Icc 1 n).filter fun x => c x = e).card : ℝ) - n / n₀)
    (R B G : Fin 3) (hRB : R ≠ B) (hRG : R ≠ G) (hBG : B ≠ G)
    (hdom : ∀ i ℓ : ℕ, 0 < i → ((Finset.Ico i (i + ℓ)).image c).card = 2 →
      R ∈ (Finset.Ico i (i + ℓ)).image c)
    (j₁ j₂ : ℕ) (hj₁ : 0 < j₁) (hj₂ : 0 < j₂) (hcop : Nat.Coprime j₁ j₂)
    (hc₁ : c j₁ = G) (hc₂ : c j₂ = G) :
    ¬ ((∃ i : ℕ, 0 < i ∧ ∀ t : ℕ, c (i + t * j₁ ^ k) = B) ∧
      ∃ i : ℕ, 0 < i ∧ ∀ t : ℕ, c (i + t * j₂ ^ k) = B)

/-- Let `k ≥ 2` and let `c` be a 3-coloring of the positive integers with a dominant color `R`
satisfying the density condition of Lemma 4 (`limsup (min(R(n), B(n), G(n)) - n / n₀) = ∞`,
`n₀ ≥ 2`). If each of the two other color classes `B`, `G` contains a pair of coprime integers,
then `c` has a rainbow solution of `x - y = z ^ k` in positive integers. The paper's standing
assumption `k ≥ 2` is kept.

Source: Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free
Colorings and Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Theorem 1
(`integers-2024-A105-thm-1`). -/
public theorem_wanted exists_rainbow_powDiff_of_coprime_pairs (k : ℕ) (hk : 2 ≤ k)
    (c : ℕ → Fin 3) (n₀ : ℕ) (hn₀ : 2 ≤ n₀)
    (hdens : ∀ M : ℝ, ∀ N₀ : ℕ, ∃ n : ℕ, N₀ ≤ n ∧ ∀ e : Fin 3,
      M < (((Finset.Icc 1 n).filter fun x => c x = e).card : ℝ) - n / n₀)
    (R B G : Fin 3) (hRB : R ≠ B) (hRG : R ≠ G) (hBG : B ≠ G)
    (hdom : ∀ i ℓ : ℕ, 0 < i → ((Finset.Ico i (i + ℓ)).image c).card = 2 →
      R ∈ (Finset.Ico i (i + ℓ)).image c)
    (hB : ∃ i₁ i₂ : ℕ, 0 < i₁ ∧ 0 < i₂ ∧ Nat.Coprime i₁ i₂ ∧ c i₁ = B ∧ c i₂ = B)
    (hG : ∃ j₁ j₂ : ℕ, 0 < j₁ ∧ 0 < j₂ ∧ Nat.Coprime j₁ j₂ ∧ c j₁ = G ∧ c j₂ = G) :
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x = y + z ^ k ∧
      c x ≠ c y ∧ c y ≠ c z ∧ c x ≠ c z

/-- In an exact rainbow-free 3-coloring of `ℤ/pℤ` for `x - y = z ^ k`, for every `a ≠ 0` the
color `c a` is `aᵏ`-dominant: every bichromatic `aᵏ`-string `i aᵏ, (i + 1) aᵏ, …,
(i + ℓ - 1) aᵏ` contains it.

Source: Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free
Colorings and Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Lemma 9
(`integers-2024-A105-lem-9`). -/
public theorem_wanted color_dominant_powStrings_of_rainbowFree_zmod (p k : ℕ) [Fact p.Prime]
    (c : ZMod p → Fin 3) (hc : Function.Surjective c)
    (hrf : ∀ x y z : ZMod p, x - y = z ^ k → ¬ (c x ≠ c y ∧ c y ≠ c z ∧ c x ≠ c z))
    (a : ZMod p) (ha : a ≠ 0) (i : ZMod p) (ℓ : ℕ)
    (hbi : ((Finset.range ℓ).image fun t : ℕ => c ((i + t) * a ^ k)).card = 2) :
    c a ∈ (Finset.range ℓ).image fun t : ℕ => c ((i + t) * a ^ k)

/-- Let `f : ℤ/nℤ → ℤ/nℤ` with functional digraph `a → f a`, and let `c` be an exact rainbow-free
coloring of `ℤ/nℤ` for `x - y = f(z)`. If the (weak) component of `v`, the set of `a` with
`f^[m] a = f^[m'] v` for some `m, m'`, avoids the color `c 0`, then it is monochromatic. The
record prints the equation as `x - y = f(x)`; the paper's proof uses the solution
`(f(a), 0, a)` of `x - y = f(z)`, and the `x - y = f(x)` reading fails on small examples.

Source: Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free
Colorings and Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Lemma 11
(`integers-2024-A105-lem-11`). -/
public theorem_wanted component_monochromatic_of_rainbowFree (n t : ℕ) (f : ZMod n → ZMod n)
    (c : ZMod n → Fin t) (hc : Function.Surjective c)
    (hrf : ∀ x y z : ZMod n, x - y = f z → ¬ (c x ≠ c y ∧ c y ≠ c z ∧ c x ≠ c z))
    (v : ZMod n)
    (h0 : ∀ a : ZMod n, (∃ m m' : ℕ, f^[m] a = f^[m'] v) → c a ≠ c 0)
    (a b : ZMod n) (ha : ∃ m m' : ℕ, f^[m] a = f^[m'] v)
    (hb : ∃ m m' : ℕ, f^[m] b = f^[m'] v) :
    c a = c b

/-- Cycle vertices of `G^k_p`: for an odd prime `p` let `t` be the largest divisor of `p - 1`
coprime to `k`. A nonzero `a ∈ ℤ/pℤ` lies on a cycle of `x ↦ xᵏ` (`a^(k^m) = a` for some
`m ≥ 1`) if and only if `ord_p(a) ∣ t`. The record's trailing sentences (`t + 1` cycle vertices,
two components iff `t = 1`) are omitted.

Source: Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free
Colorings and Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Theorem 6 (after Lucheta, Miller and Reiter)
(`integers-2024-A105-thm-6`). -/
public theorem_wanted isCycleVertex_powMap_iff_orderOf_dvd (p k : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (t : ℕ) (ht : t ∣ p - 1) (htk : Nat.Coprime t k)
    (htmax : ∀ s : ℕ, s ∣ p - 1 → Nat.Coprime s k → s ≤ t) (a : ZMod p) (ha : a ≠ 0) :
    (∃ m : ℕ, 1 ≤ m ∧ a ^ (k ^ m) = a) ↔ orderOf a ∣ t

end

end MetaMathlibExt
