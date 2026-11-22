/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Fin.VecNotation
public import MathlibExt.Computability.Complexity
public import MathlibExt.GameTheory.SmithRemoteness
public import WantedExt.Combinatorics.SlowANimWanted

/-!
# Remoteness of Exact Slow `k`-NIM with `k + 1` piles

Statements from Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi,
*On Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1
(arXiv:2304.06498).

`NIM(k + 1, k)` is played on `k + 1` piles (a position is `x : Fin (k + 1) → ℕ`); a move removes
exactly one stone from each of `k` nonempty piles. This is the existing Slow`A`-Nim game
`slowANimGame (k + 1) {k}`, whose options are `slowANimMoves {k} x`. Smith's remoteness function
is `SpragueGrundy.smithRemoteness` (`MathlibExt/GameTheory/SmithRemoteness.lean`). The paper
compares positions after sorting their entries; since the game, the remoteness, and the
conditions below are invariant under permuting piles, "`R(y) ≠ m` for
every `y < x`" is equivalent to the same condition for the componentwise (`Pi`) order used here.
-/

namespace MetaMathlibExt

@[expose] public section

/-- A position `x` of `NIM(k + 1, k)` is `m`-critical: `R(x) = m` and `R(y) ≠ m` for every
position `y < x`.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Theorem 1. -/
public def IsExactSlowNimCritical (k m : ℕ) (x : Fin (k + 1) → ℕ) : Prop :=
  SpragueGrundy.smithRemoteness (slowANimGame (k + 1) {k}) x = m ∧
    ∀ y : Fin (k + 1) → ℕ, y < x → SpragueGrundy.smithRemoteness (slowANimGame (k + 1) {k}) y ≠ m

/-- The empty position is `0`-critical.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Theorem 1. -/
public theorem isExactSlowNimCritical_zero (k : ℕ) :
    IsExactSlowNimCritical k 0 (fun _ => 0) := by
  refine ⟨SpragueGrundy.smithRemoteness_of_moves_eq_empty _ _ (slowANimMoves_zero {k}), ?_⟩
  intro y hy
  exact absurd hy (not_lt_of_ge fun i => Nat.zero_le (y i))

/-- The pile kept by the M-move: the first pile holding the smallest even entry if some entry is
even, and otherwise the first pile holding a largest entry.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Section 2 (the index `e(x)`). Such a pile always exists, so the default `0` of `getD` is never
used. -/
public def exactSlowNimMRuleKept {n : ℕ} (x : Fin (n + 1) → ℕ) : Fin (n + 1) :=
  let piles := List.finRange (n + 1)
  if piles.any fun i => decide (Even (x i)) then
    (piles.find? fun i => decide (Even (x i) ∧ ∀ j, Even (x j) → x i ≤ x j)).getD 0
  else
    (piles.find? fun i => decide (∀ j, x j ≤ x i)).getD 0

/-- The M-move: keep the pile `exactSlowNimMRuleKept x` and remove one stone from every other
pile.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Sections 1.2 and 2 (the M-rule). -/
public def exactSlowNimMRuleMove {n : ℕ} (x : Fin (n + 1) → ℕ) : Fin (n + 1) → ℕ :=
  slowANimAfter x (Finset.univ.erase (exactSlowNimMRuleKept x))

/-- A position of exact slow `k`-NIM is terminal iff `k = 0` (no move uses a nonempty set of
`0` piles) or fewer than `k` piles are nonempty. This is the direct terminal test used by the
M-rule recursion, avoiding the powerset enumeration in `slowANimMoves`.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Section 1.1 (the moves of `NIM(n, k)`). -/
public theorem slowANimMoves_singleton_eq_empty_iff {n k : ℕ} (x : Fin n → ℕ) :
    slowANimMoves {k} x = ∅ ↔ k = 0 ∨ (Finset.univ.filter fun i => 0 < x i).card < k := by
  classical
  rw [slowANimMoves, Finset.image_eq_empty, Finset.filter_eq_empty_iff]
  constructor
  · intro h
    by_contra hc
    rw [not_or, not_lt] at hc
    obtain ⟨hk, hle⟩ := hc
    obtain ⟨S, hS, hcard⟩ := Finset.exists_subset_card_eq hle
    refine h (Finset.mem_univ S) ⟨Finset.card_pos.mp (by omega), by simp [hcard], fun i hi => ?_⟩
    have := (Finset.mem_filter.mp (hS hi)).2
    omega
  · rintro h S - ⟨hne, hcard, hp⟩
    rw [Finset.mem_singleton] at hcard
    rcases h with h | h
    · exact (Finset.card_pos.mpr hne).ne' (hcard.trans h)
    · have hsub : S ⊆ Finset.univ.filter fun i => 0 < x i := fun i hi =>
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp i hi⟩
      have := Finset.card_le_card hsub
      omega

/-- At most `f` steps of the M-rule in `NIM(k + 1, k)`, stopping at a terminal position.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Section 1.2 (the function `M`). -/
public def exactSlowNimMRuleLengthAux (k : ℕ) : ℕ → (Fin (k + 1) → ℕ) → ℕ
  | 0, _ => 0
  | f + 1, x =>
    if k = 0 ∨ (Finset.univ.filter fun i => 0 < x i).card < k then 0
    else 1 + exactSlowNimMRuleLengthAux k f (exactSlowNimMRuleMove x)

/-- The M-rule recursion stops exactly at terminal positions (empty move set).

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Section 1.2 (the function `M`). -/
public theorem exactSlowNimMRuleLengthAux_succ (k f : ℕ) (x : Fin (k + 1) → ℕ) :
    exactSlowNimMRuleLengthAux k (f + 1) x =
      if slowANimMoves {k} x = ∅ then 0
      else 1 + exactSlowNimMRuleLengthAux k f (exactSlowNimMRuleMove x) := by
  rw [exactSlowNimMRuleLengthAux]
  exact if_congr (slowANimMoves_singleton_eq_empty_iff x).symm rfl rfl

/-- `M(x)`: the number of moves from `x` to a terminal position when both players follow the
M-rule. Every move of `NIM(k + 1, k)` with `0 < k` removes `k` stones, so `∑ i, x i` steps
suffice.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Section 1.2 (the function `M`). -/
public def exactSlowNimMRuleLength (k : ℕ) (x : Fin (k + 1) → ℕ) : ℕ :=
  exactSlowNimMRuleLengthAux k (∑ i, x i) x

/-- The paper's example `M(3, 3, 3) = 4` in `NIM(3, 2)`.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Section 1.6 (example after Theorem 1). -/
public theorem exactSlowNimMRuleLength_three_three_three :
    exactSlowNimMRuleLength 2 ![3, 3, 3] = 4 := by
  decide +kernel

/-- The paper's example `M(3, 5, 5) = 6` in `NIM(3, 2)`.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Section 1.6 (example after Theorem 1). -/
public theorem exactSlowNimMRuleLength_three_five_five :
    exactSlowNimMRuleLength 2 ![3, 5, 5] = 6 := by
  decide +kernel

/-- Basic vectors of type (A0): `Σ z = k b`, every `z i ≤ b`, `b` even, all `z i` even.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Section 2 (basic vectors). -/
public def IsExactSlowNimBasicA0 (k b : ℕ) (z : Fin (k + 1) → ℕ) : Prop :=
  ∑ i, z i = k * b ∧ (∀ i, z i ≤ b) ∧ Even b ∧ ∀ i, Even (z i)

/-- Basic vectors of type (A1): `Σ z = k b`, every `z i ≤ b`, `b` odd, exactly one `z i` even.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Section 2 (basic vectors). -/
public def IsExactSlowNimBasicA1 (k b : ℕ) (z : Fin (k + 1) → ℕ) : Prop :=
  ∑ i, z i = k * b ∧ (∀ i, z i ≤ b) ∧ Odd b ∧ ∃! i, Even (z i)

/-- Basic vectors of type (B): `Σ z = k b + k - 1`, every `z i < b`, `b` even, all `z i` odd.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Section 2 (basic vectors). -/
public def IsExactSlowNimBasicB (k b : ℕ) (z : Fin (k + 1) → ℕ) : Prop :=
  ∑ i, z i = k * b + k - 1 ∧ (∀ i, z i < b) ∧ Even b ∧ ∀ i, Odd (z i)

/-- `B(x) = max {b(z) : z ≤ x, z basic}` for `0 < k`. Then every basic `z ≤ x` has
`b(z) ≤ k b(z) ≤ Σ z ≤ Σ x`, so the maximum is searched below `Σ x`. For `k = 0` the source
maximum does not exist (`z = 0` is basic of type (A0) for every even `b`); this definition
totalizes that degenerate case as the largest admissible `b ≤ Σ x`, and every statement below
about `B` assumes `0 < k`.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Section 2, equation (1). -/
public noncomputable def exactSlowNimBasicValue (k : ℕ) (x : Fin (k + 1) → ℕ) : ℕ :=
  open Classical in
  Nat.findGreatest (fun b => ∃ z ≤ x, IsExactSlowNimBasicA0 k b z ∨
    IsExactSlowNimBasicA1 k b z ∨ IsExactSlowNimBasicB k b z) (∑ i, x i)

/-- `B(x)` is attained: some basic vector `z ≤ x` has `b(z) = B(x)` (it supports `x`).

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Section 2, equation (1). -/
public theorem exists_supports_exactSlowNimBasicValue (k : ℕ) (x : Fin (k + 1) → ℕ) :
    ∃ z ≤ x, IsExactSlowNimBasicA0 k (exactSlowNimBasicValue k x) z ∨
      IsExactSlowNimBasicA1 k (exactSlowNimBasicValue k x) z ∨
      IsExactSlowNimBasicB k (exactSlowNimBasicValue k x) z := by
  classical
  unfold exactSlowNimBasicValue
  exact Nat.findGreatest_spec (P := fun b => ∃ z ≤ x, IsExactSlowNimBasicA0 k b z ∨
    IsExactSlowNimBasicA1 k b z ∨ IsExactSlowNimBasicB k b z) (m := 0) (Nat.zero_le _) ⟨fun _ => 0, fun i => Nat.zero_le _,
    Or.inl ⟨by simp, fun _ => le_rfl, ⟨0, rfl⟩, fun _ => ⟨0, rfl⟩⟩⟩

/-- **Theorem 1.** For `0 < k`, a position `x` of `NIM(k + 1, k)` is `m`-critical iff either
(A) `Σ x = k m`, `max x ≤ m`, all entries are even when `m` is even, and exactly one entry is
even when `m` is odd; or (B) `Σ x = k m + k - 1`, `max x < m`, `m` is even, and all entries are
odd.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Theorem 1. -/
public theorem_wanted isExactSlowNimCritical_iff {k : ℕ} (hk : 0 < k) (m : ℕ)
    (x : Fin (k + 1) → ℕ) :
    IsExactSlowNimCritical k m x ↔
      (∑ i, x i = k * m ∧ (∀ i, x i ≤ m) ∧ (Even m → ∀ i, Even (x i)) ∧
          (Odd m → ∃! i, Even (x i))) ∨
        (∑ i, x i = k * m + k - 1 ∧ (∀ i, x i < m) ∧ Even m ∧ ∀ i, Odd (x i))

/-- **Corollary 1 (i)**, Case (A). Let `x` be `m`-critical with `m` even and positive. Then `x`
is all odd or all even. If `x` is all even, some entry is `< m`; every move that reduces all
entries equal to `m` leads to an `(m - 1)`-critical position; and the M-move is such a move.
The positivity of `m` and the restriction of the move claims to even `x` are deviations; see the
audit row.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Corollary 1 (i). -/
public theorem_wanted exactSlowNim_critical_of_even {k m : ℕ} (hk : 0 < k) (hm0 : 0 < m)
    (hm : Even m) (x : Fin (k + 1) → ℕ) (hx : IsExactSlowNimCritical k m x) :
    ((∀ i, Odd (x i)) ∨ (∀ i, Even (x i))) ∧
      ((∀ i, Even (x i)) →
        (∃ i, x i < m) ∧
          (∀ y ∈ slowANimMoves {k} x, (∀ i, x i = m → y i < x i) →
            IsExactSlowNimCritical k (m - 1) y) ∧
          (∀ i, x i = m → exactSlowNimMRuleMove x i < x i) ∧
          IsExactSlowNimCritical k (m - 1) (exactSlowNimMRuleMove x))

/-- **Corollary 1 (ii).** For `2 ≤ k`, if `x` is `m`-critical with `m` odd, then `x` has a unique
even entry `x i`, and exactly one move leads to an `(m - 1)`-critical position: the move keeping
pile `i` and reducing all others, which is the M-move.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Corollary 1 (ii). -/
public theorem_wanted exactSlowNim_critical_of_odd {k m : ℕ} (hk : 2 ≤ k) (hm : Odd m)
    (x : Fin (k + 1) → ℕ) (hx : IsExactSlowNimCritical k m x) :
    ∃ i, Even (x i) ∧ (∀ j, Even (x j) → j = i) ∧
      slowANimAfter x (Finset.univ.erase i) ∈ slowANimMoves {k} x ∧
      (∀ y ∈ slowANimMoves {k} x,
        IsExactSlowNimCritical k (m - 1) y ↔ y = slowANimAfter x (Finset.univ.erase i)) ∧
      exactSlowNimMRuleMove x = slowANimAfter x (Finset.univ.erase i)

/-- **Proposition 1.** For `0 < k`, an odd position `x` (all entries odd) of `NIM(k + 1, k)` is
a P-position iff it satisfies (B) of Theorem 1 for some `m`: `Σ x = k m + k - 1`, `max x < m`,
and `m` even.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Proposition 1. -/
public theorem_wanted exactSlowNim_odd_isP_iff {k : ℕ} (hk : 0 < k) (x : Fin (k + 1) → ℕ)
    (hx : ∀ i, Odd (x i)) :
    SpragueGrundy.IsP (slowANimGame (k + 1) {k}) x ↔
      ∃ m, ∑ i, x i = k * m + k - 1 ∧ (∀ i, x i < m) ∧ Even m

/-- **Theorem 2.** For `0 < k`, `M(x) = R(x)` for every position `x` of `NIM(k + 1, k)`: the
M-rule realizes Smith's remoteness.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Theorem 2. -/
public theorem_wanted exactSlowNimMRuleLength_eq_smithRemoteness {k : ℕ} (hk : 0 < k)
    (x : Fin (k + 1) → ℕ) :
    exactSlowNimMRuleLength k x = SpragueGrundy.smithRemoteness (slowANimGame (k + 1) {k}) x

/-- **Lemma 1.** If `x` is supported by a basic vector `z ≤ x` of type (B), then `x = z` and
`B(x') = B(x) - 1` for every move `x → x'`.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Lemma 1. -/
public theorem_wanted exactSlowNimBasicValue_of_supports_basicB {k : ℕ} (hk : 0 < k)
    (x z : Fin (k + 1) → ℕ) (hzx : z ≤ x)
    (hz : IsExactSlowNimBasicB k (exactSlowNimBasicValue k x) z) :
    x = z ∧ ∀ x' ∈ slowANimMoves {k} x,
      exactSlowNimBasicValue k x' = exactSlowNimBasicValue k x - 1

/-- **Lemma 2.** If `x` is supported by a basic vector `z ≤ x` of type (A0), then every move
`x → x' = x - d(j)` (keep pile `j`) has `B(x') ≤ B(x) - 1` with `B(x')` odd, and
`B(x') = B(x) - 1` when `z j < b(z)`, or `z j = b(z)` and `z i < min(b(z), x i)` for some `i`.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Lemma 2. -/
public theorem_wanted exactSlowNimBasicValue_of_supports_basicA0 {k : ℕ} (hk : 0 < k)
    (x z : Fin (k + 1) → ℕ) (hzx : z ≤ x)
    (hz : IsExactSlowNimBasicA0 k (exactSlowNimBasicValue k x) z) (j : Fin (k + 1))
    (hj : ∀ i, i ≠ j → 0 < x i) :
    exactSlowNimBasicValue k (slowANimAfter x (Finset.univ.erase j)) ≤
        exactSlowNimBasicValue k x - 1 ∧
      Odd (exactSlowNimBasicValue k (slowANimAfter x (Finset.univ.erase j))) ∧
      (z j < exactSlowNimBasicValue k x ∨
          (z j = exactSlowNimBasicValue k x ∧
            ∃ i, z i < min (exactSlowNimBasicValue k x) (x i)) →
        exactSlowNimBasicValue k (slowANimAfter x (Finset.univ.erase j)) =
          exactSlowNimBasicValue k x - 1)

/-- **Lemma 3.** If `x` is supported by a basic vector `z ≤ x` of type (A1), then
`B(x') ≥ B(x) - 2` for every move `x → x'`, and `B(x') = B(x) - 1` for the M-move.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Lemma 3. -/
public theorem_wanted exactSlowNimBasicValue_of_supports_basicA1 {k : ℕ} (hk : 0 < k)
    (x z : Fin (k + 1) → ℕ) (hzx : z ≤ x)
    (hz : IsExactSlowNimBasicA1 k (exactSlowNimBasicValue k x) z) :
    (∀ x' ∈ slowANimMoves {k} x, exactSlowNimBasicValue k x - 2 ≤ exactSlowNimBasicValue k x') ∧
      exactSlowNimBasicValue k (exactSlowNimMRuleMove x) = exactSlowNimBasicValue k x - 1

/-- **Lemma 4.** For `0 < k`, `B(x) = R(x)` for every position `x` of `NIM(k + 1, k)`: the
basic-vector value equals Smith's remoteness.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Lemma 4. -/
public theorem_wanted exactSlowNimBasicValue_eq_smithRemoteness {k : ℕ} (hk : 0 < k)
    (x : Fin (k + 1) → ℕ) :
    exactSlowNimBasicValue k x = SpragueGrundy.smithRemoteness (slowANimGame (k + 1) {k}) x

/-- The binary encoding of natural numbers (Mathlib's `Computability.encodingNatBool`) as a
`BitstringEncoding`. A definition, not an instance; Theorem 3 installs it locally so that lists
of piles are encoded as self-delimiting binary blocks.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Theorem 3 ("integers are presented in binary"). -/
@[instance_reducible]
public def exactSlowNimBinaryNatEncoding : BitstringEncoding ℕ where
  toEncoding := Computability.encodingNatBool

/-- Smith's remoteness of a position of `NIM(k + 1, k)` given as the list of its `k + 1` pile
sizes, so that `k` is part of the input. The empty list is read as the empty game.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Theorem 3. -/
public noncomputable def exactSlowNimRemotenessOfList (l : List ℕ) : ℕ :=
  SpragueGrundy.smithRemoteness (slowANimGame l.length {l.length - 1}) fun i => l.get i

/-- **Theorem 3.** Smith's remoteness `R` of `NIM(k + 1, k)` is computable in polynomial time
even when `k` is part of the input and integers are given in binary: the map from the list of
pile sizes to `R` is `IsPolyTime` for the binary encoding of `ℕ` and the repository's
self-delimiting list encoding.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Theorem 3. -/
public theorem_wanted exactSlowNimRemoteness_isPolyTime :
    letI : BitstringEncoding ℕ := exactSlowNimBinaryNatEncoding
    ComplexityTheory.IsPolyTime exactSlowNimRemotenessOfList

end

end MetaMathlibExt
