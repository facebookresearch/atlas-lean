/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.Rayleigh
public import Mathlib.Data.Set.Card

/-! # Decomposition of Beatty and complementary sequences (Polanco)

Statements from G. Polanco, *Decomposition of Beatty and Complementary Sequences*,
INTEGERS 25 (2025), Article A104 (arXiv:2305.15361). Beatty sets are written with
Mathlib's `beattySeq r k = ⌊k * r⌋` over positive indices `k`. For complementary
Beatty sequences `A = {⌊nα⌋}` and `B = {⌊nβ⌋}`, the paper's sequences `r n` and `c n`
count the elements of `B`, respectively `A`, strictly between `a n = ⌊nα⌋` and
`b n = ⌊nβ⌋`; by part (3) of the paper's main theorem these are the auxiliary and
skipping sequences of its MES algorithm. "Complementary Beatty sequences" is
encoded through Beatty's theorem as `Irrational α`, `1 < α` and `α⁻¹ + β⁻¹ = 1`.
-/

namespace MetaMathlibExt

@[expose] public section

open Set

/-- Beatty's theorem with its converse: for positive reals `α` and `β`, the positive
Beatty sets of `α` and `β` partition the positive integers if and only if `α` is
irrational and `α⁻¹ + β⁻¹ = 1`. Positivity of `β` is the paper's definition of a Beatty
sequence; without it the statement fails (for `0 < α < 1` the dual slope is negative).

Source: Geremias Polanco, *Decomposition of Beatty and Complementary Sequences*,
INTEGERS 25 (2025), Article A104, Theorem 1 (Beatty–Rayleigh) (`integers-2025-A104-thm-1`). -/
public theorem_wanted beatty_complementary_iff_irrational_inv_add_inv {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β) :
    (Disjoint {beattySeq α k | k > 0} {beattySeq β k | k > 0} ∧
        {beattySeq α k | k > 0} ∪ {beattySeq β k | k > 0} = {n : ℤ | 0 < n}) ↔
      (Irrational α ∧ α⁻¹ + β⁻¹ = 1)

/-- For complementary Beatty sequences with slopes `1 < α < 2` and `β`, the number
`r n` of elements of `B` strictly between `⌊nα⌋` and `⌊nβ⌋` equals `⌊(2 - α) n⌋` for
every positive integer `n`.

Source: Geremias Polanco, *Decomposition of Beatty and Complementary Sequences*,
INTEGERS 25 (2025), Article A104, Theorem 3 (`integers-2025-A104-thm-3`). -/
public theorem_wanted beatty_card_compl_between_eq_floor {α β : ℝ} (hirr : Irrational α)
    (hα1 : 1 < α) (hα2 : α < 2) (hαβ : α⁻¹ + β⁻¹ = 1) {n : ℤ} (hn : 0 < n) :
    ((Ioo (beattySeq α n) (beattySeq β n) ∩ {beattySeq β k | k > 0}).ncard : ℤ) =
      beattySeq (2 - α) n

/-- For complementary Beatty sequences with slopes `1 < α < 2` and `β`, the number
`c n` of elements of `A` strictly between `⌊nα⌋` and `⌊nβ⌋` equals `⌊(β - 2) n⌋` for
every positive integer `n`.

Source: Geremias Polanco, *Decomposition of Beatty and Complementary Sequences*,
INTEGERS 25 (2025), Article A104, Theorem 4 (`integers-2025-A104-thm-4`). -/
public theorem_wanted beatty_card_self_between_eq_floor {α β : ℝ} (hirr : Irrational α)
    (hα1 : 1 < α) (hα2 : α < 2) (hαβ : α⁻¹ + β⁻¹ = 1) {n : ℤ} (hn : 0 < n) :
    ((Ioo (beattySeq α n) (beattySeq β n) ∩ {beattySeq α k | k > 0}).ncard : ℤ) =
      beattySeq (β - 2) n

/-- Identity (7): for complementary Beatty sequences `a n = ⌊nα⌋`, `b n = ⌊nβ⌋` with
`1 < α < 2` and every positive integer `n`,
`⌊β⁻¹ (b (n - 1) + 1)⌋ - ⌊β⁻¹ a n⌋ = ⌊(2 - α) n⌋`.

Source: Geremias Polanco, *Decomposition of Beatty and Complementary Sequences*,
INTEGERS 25 (2025), Article A104, Theorem 5, identity (7) (`integers-2025-A104-thm-5`). -/
public theorem_wanted beatty_floor_inv_sub_eq_floor_two_sub {α β : ℝ} (hirr : Irrational α)
    (hα1 : 1 < α) (hα2 : α < 2) (hαβ : α⁻¹ + β⁻¹ = 1) {n : ℤ} (hn : 0 < n) :
    ⌊β⁻¹ * ((beattySeq β (n - 1) + 1 : ℤ) : ℝ)⌋ - ⌊β⁻¹ * (beattySeq α n : ℝ)⌋ =
      beattySeq (2 - α) n

/-- Identity (8): for complementary Beatty sequences `a n = ⌊nα⌋`, `b n = ⌊nβ⌋` with
`1 < α < 2` and every positive integer `n`,
`⌊α⁻¹ b n⌋ - ⌊α⁻¹ (a n + 1)⌋ = ⌊(β - 2) n⌋`.

Source: Geremias Polanco, *Decomposition of Beatty and Complementary Sequences*,
INTEGERS 25 (2025), Article A104, Theorem 5, identity (8) (`integers-2025-A104-thm-5`). -/
public theorem_wanted beatty_floor_inv_sub_eq_floor_sub_two {α β : ℝ} (hirr : Irrational α)
    (hα1 : 1 < α) (hα2 : α < 2) (hαβ : α⁻¹ + β⁻¹ = 1) {n : ℤ} (hn : 0 < n) :
    ⌊α⁻¹ * (beattySeq β n : ℝ)⌋ - ⌊α⁻¹ * ((beattySeq α n + 1 : ℤ) : ℝ)⌋ =
      beattySeq (β - 2) n

/-- For complementary Beatty sequences with slopes `1 < α < 2` and `β`, the sequence
`r n` of elements of `B` strictly between `⌊nα⌋` and `⌊nβ⌋` is a Beatty sequence with
a slope strictly between `0` and `1`.

Source: Geremias Polanco, *Decomposition of Beatty and Complementary Sequences*,
INTEGERS 25 (2025), Article A104, Corollary 3 (`integers-2025-A104-cor-3`). -/
public theorem_wanted beatty_card_compl_between_isBeatty {α β : ℝ} (hirr : Irrational α)
    (hα1 : 1 < α) (hα2 : α < 2) (hαβ : α⁻¹ + β⁻¹ = 1) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ n : ℤ, 0 < n →
      ((Ioo (beattySeq α n) (beattySeq β n) ∩ {beattySeq β k | k > 0}).ncard : ℤ) =
        beattySeq r n

/-- If `1 / (k + 1) < α < 1 / k`, every non-negative integer `t` is attained by
`⌊nα⌋` (`n ≥ 1`) exactly `k` or `k + 1` times, and both multiplicities occur for
infinitely many `t`.

Source: Geremias Polanco, *Decomposition of Beatty and Complementary Sequences*,
INTEGERS 25 (2025), Article A104, Lemma 1 (`integers-2025-A104-lem-1`). -/
public theorem_wanted beatty_floor_fiber_card_eq_or_eq_succ {α : ℝ} {k : ℕ}
    (h1 : 1 / ((k : ℝ) + 1) < α) (h2 : α < 1 / (k : ℝ)) :
    (∀ t : ℕ, {n : ℕ | 0 < n ∧ ⌊(n : ℝ) * α⌋ = t}.ncard = k ∨
        {n : ℕ | 0 < n ∧ ⌊(n : ℝ) * α⌋ = t}.ncard = k + 1) ∧
      {t : ℕ | {n : ℕ | 0 < n ∧ ⌊(n : ℝ) * α⌋ = t}.ncard = k}.Infinite ∧
      {t : ℕ | {n : ℕ | 0 < n ∧ ⌊(n : ℝ) * α⌋ = t}.ncard = k + 1}.Infinite

/-- If `1 / (k + 1) < α < 1 / k` and `β = α / (1 - α)`, then a non-negative integer `t`
is attained by `⌊nα⌋` (`n ≥ 1`) exactly `k + 1` times if and only if it is attained by
`⌊nβ⌋` exactly `k` times.

Source: Geremias Polanco, *Decomposition of Beatty and Complementary Sequences*,
INTEGERS 25 (2025), Article A104, Lemma 2 (`integers-2025-A104-lem-2`). -/
public theorem_wanted beatty_floor_fiber_card_succ_iff {α : ℝ} {k : ℕ}
    (h1 : 1 / ((k : ℝ) + 1) < α) (h2 : α < 1 / (k : ℝ)) (t : ℕ) :
    {n : ℕ | 0 < n ∧ ⌊(n : ℝ) * α⌋ = t}.ncard = k + 1 ↔
      {n : ℕ | 0 < n ∧ ⌊(n : ℝ) * (α / (1 - α))⌋ = t}.ncard = k

/-- For irrational `α` with `1 / (k + 1) < α < 1 / k`, the positive integers attained by
`⌊nα⌋` (`n ≥ 1`) exactly `k + 1` times and those attained exactly `k` times are two
positive Beatty sets.

Source: Geremias Polanco, *Decomposition of Beatty and Complementary Sequences*,
INTEGERS 25 (2025), Article A104, Corollary 1 (`integers-2025-A104-cor-1`). -/
public theorem_wanted beatty_floor_fiber_card_sets_isBeatty {α : ℝ} {k : ℕ}
    (hirr : Irrational α) (h1 : 1 / ((k : ℝ) + 1) < α) (h2 : α < 1 / (k : ℝ)) :
    ∃ γ δ : ℝ, 0 < γ ∧ 0 < δ ∧
      {t : ℤ | 0 < t ∧ {n : ℕ | 0 < n ∧ ⌊(n : ℝ) * α⌋ = t}.ncard = k + 1} =
        {beattySeq γ m | m > 0} ∧
      {t : ℤ | 0 < t ∧ {n : ℕ | 0 < n ∧ ⌊(n : ℝ) * α⌋ = t}.ncard = k} =
        {beattySeq δ m | m > 0}

/-- For irrational `α` with `1 / (k + 1) < α < 1 / k`, the sequence `⌊nα⌋` (`n ≥ 1`) is
the sortjoin of `k` copies of the non-negative integers with a Beatty set `D`: every
non-negative integer `t` is attained `k` times, plus one more time exactly when `t ∈ D`.

Source: Geremias Polanco, *Decomposition of Beatty and Complementary Sequences*,
INTEGERS 25 (2025), Article A104, Corollary 2 (`integers-2025-A104-cor-2`). -/
public theorem_wanted beatty_floor_fiber_card_eq_add_indicator {α : ℝ} {k : ℕ}
    (hirr : Irrational α) (h1 : 1 / ((k : ℝ) + 1) < α) (h2 : α < 1 / (k : ℝ)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℕ, {n : ℕ | 0 < n ∧ ⌊(n : ℝ) * α⌋ = t}.ncard =
      k + {beattySeq δ m | m > 0}.indicator (1 : ℤ → ℕ) t

/-- For complementary Beatty sequences with slopes `1 < α < 2` and `β`, let `r n` count
the elements of `B` strictly between `⌊nα⌋` and `⌊nβ⌋`. Then `r (n + 1) - r n` is `0` or
`1`, and it is `1` exactly when `⌊(n + 1)α⌋ - ⌊nα⌋ = 1`.

Source: Geremias Polanco, *Decomposition of Beatty and Complementary Sequences*,
INTEGERS 25 (2025), Article A104, Lemma 4 (`integers-2025-A104-lem-4`). -/
public theorem_wanted beatty_card_compl_between_succ_sub {α β : ℝ} (hirr : Irrational α)
    (hα1 : 1 < α) (hα2 : α < 2) (hαβ : α⁻¹ + β⁻¹ = 1) {n : ℤ} (hn : 0 < n) :
    let r : ℤ → ℤ := fun m ↦
      ((Ioo (beattySeq α m) (beattySeq β m) ∩ {beattySeq β k | k > 0}).ncard : ℤ)
    (r (n + 1) - r n = 0 ∨ r (n + 1) - r n = 1) ∧
      (r (n + 1) - r n = 1 ↔ beattySeq α (n + 1) - beattySeq α n = 1)

/-- For complementary Beatty sequences with slopes `α` and `β > 2`, let `q = ⌊β⌋` and let
`c n` count the elements of `A` strictly between `⌊nα⌋` and `⌊nβ⌋`. Then
`c (n + 1) - c n` is `q - 2` or `q - 1`, and it is `q - 2` exactly when
`⌊(n + 1)β⌋ - ⌊nβ⌋ = q`.

Source: Geremias Polanco, *Decomposition of Beatty and Complementary Sequences*,
INTEGERS 25 (2025), Article A104, Lemma 5 (`integers-2025-A104-lem-5`). -/
public theorem_wanted beatty_card_self_between_succ_sub {α β : ℝ} (hirr : Irrational β)
    (hβ : 2 < β) (hαβ : α⁻¹ + β⁻¹ = 1) {n : ℤ} (hn : 0 < n) :
    let c : ℤ → ℤ := fun m ↦
      ((Ioo (beattySeq α m) (beattySeq β m) ∩ {beattySeq α k | k > 0}).ncard : ℤ)
    (c (n + 1) - c n = ⌊β⌋ - 2 ∨ c (n + 1) - c n = ⌊β⌋ - 1) ∧
      (c (n + 1) - c n = ⌊β⌋ - 2 ↔ beattySeq β (n + 1) - beattySeq β n = ⌊β⌋)

/-- Let `α` be irrational with `(2k - 1) / k < α < (2k + 1) / (k + 1)` for an integer
`k ≥ 1`, and `α⁻¹ + β⁻¹ = 1`. Let `c n` count the elements of `A` strictly between `⌊nα⌋`
and `⌊nβ⌋` (the MES skipping sequence producing `A`), and let
`δ = -1 + 1 / (2 - 1 / (2 - ⋯ - 1 / (2 - 1 / (α - 1))))` with `k - 1` twos. Then every
non-negative integer `m` occurs among the `c n` (`n ≥ 1`) exactly `k` times if `m` lies in
the positive Beatty set of `δ` and exactly `k - 1` times otherwise. For `k = 1` this
gives `δ = 1 / (α - 1) - 1 = β - 2`, and the multiplicity is one or zero.

Source: Geremias Polanco, *Decomposition of Beatty and Complementary Sequences*,
INTEGERS 25 (2025), Article A104, Lemma 6 (`integers-2025-A104-lem-6`). -/
public theorem_wanted beatty_skipping_card_eq_add_indicator {α β : ℝ} {k : ℕ}
    (hirr : Irrational α) (hk : 1 ≤ k) (hk1 : (2 * (k : ℝ) - 1) / k < α)
    (hk2 : α < (2 * (k : ℝ) + 1) / ((k : ℝ) + 1)) (hαβ : α⁻¹ + β⁻¹ = 1) (m : ℕ) :
    {n : ℤ | 0 < n ∧
        (Ioo (beattySeq α n) (beattySeq β n) ∩ {beattySeq α j | j > 0}).ncard = m}.ncard =
      (k - 1) + {beattySeq (-1 + 1 / (fun x : ℝ ↦ 2 - 1 / x)^[k - 1] (α - 1)) j | j > 0}.indicator
        (1 : ℤ → ℕ) m

end

end MetaMathlibExt
