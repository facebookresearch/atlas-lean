/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Analytical study and efficient evaluation of the Josephus function

Statements from Yunier Bello-Cruz and Roy
Quintero-Contreras, "Analytical Study and Efficient
Evaluation of the Josephus Function", *Journal of Integer
Sequences* 27 (2024), Article 24.3.8
(<https://cs.uwaterloo.ca/journals/JIS/VOL27/Cruz/cruz4.html>).

The statements use the existing Josephus survivor
function `MetaMathlibExt.josephus` (`J_k(1) = 1`,
`J_k(n+1) = (J_k(n) + k - 1) % (n+1) + 1`). Following the
paper's usage (Lemma 8: "`j ∈ [[1, k-1]]`, i.e., `n+1` is
a low extremal point"; Corollary 7: "`n_e` is a high
extremal point and `n_e + 1` is a low extremal point"), a
point `m` is *low extremal* if `J_k(m) ∈ [1, k - 1]` and
*high extremal* if `m + 1` is low extremal. The
bounded-instance statements were verified by
simulation for `2 ≤ k ≤ 9`, `n ≤ 400`; for Theorem 13
the simulation only exhibits initial fixed points
(for `n ≤ 3000`) and does not verify infinitude.

Lemma 6(b) is stated with the additional single-wrap
hypothesis `J_k(n) + k * m ≤ 2 * (n + m)`: as extracted it
fails at `k = 4`, `n = 1`, `m = 1`, where the printed
formula gives `3 > n + m` but `J_4(2) = 1` (two wraps);
with the hypothesis it holds on the whole simulation
grid. Proposition 4 carries the domain hypothesis
`1 ≤ n_p`: at `n_p = 0` the recursion anchor
`J_k(0) = 0` is a spurious fixed point for which the
fourth case fails (`J_k(1) = 1 ≠ 0`). Not stated (see the
source audit table): Lemma 8(b), 8(c), Theorem 9(b),
9(c), 9(d), and Corollaries 10, 11, which use the paper's
auxiliary functions `δ_k`, `M_k`, `a_k` and the "next
extremal point" notation, none of which are defined in
the extracted statements.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Set.Finite.Basic
public import MathlibExt.Combinatorics.Enumerative.JosephusFunction

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.JosephusWanted

/-- Low extremal point of `J_k` in the paper's sense:
`J_k(m) ∈ [1, k - 1]`. -/
def IsLowExtremal (k m : ℕ) : Prop :=
  1 ≤ MetaMathlibExt.josephus k m ∧
    MetaMathlibExt.josephus k m ≤ k - 1

/-- High extremal point of `J_k`: the point just before
a low extremal point. -/
def IsHighExtremal (k m : ℕ) : Prop := IsLowExtremal k (m + 1)

/-- **Theorem 2**: with `p := J_k(n)`, if
`p + k ∈ [[ℓ(n+1) + 1, (ℓ+1)(n+1)]]` for some
nonnegative integer `ℓ`, then
`J_k(n+1) = p + k - ℓ(n+1)`.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras,
"Analytical Study and Efficient Evaluation of the
Josephus Function", Theorem 2. -/
theorem_wanted josephus_succ_eq_sub (k n ℓ : ℕ) (hk : 2 ≤ k)
    (hn : 1 ≤ n)
    (h : ℓ * (n + 1) + 1 ≤ MetaMathlibExt.josephus k n + k ∧
      MetaMathlibExt.josephus k n + k ≤ (ℓ + 1) * (n + 1)) :
    MetaMathlibExt.josephus k (n + 1) =
      MetaMathlibExt.josephus k n + k - ℓ * (n + 1)

/-- **Proposition 4**: at a fixed point `n_p ≥ 1`
(`J_k(n_p) = n_p`), writing `s_ℓ = ℓ * (n_p + 1)`, the
value `J_k(n_p + 1)` is `k - 1` if `k ≤ n_p + 1`; `n_p + 1`
if `k = s_ℓ + 1` for some `ℓ ≥ 1`; `k₁ - 1` if
`k = s_ℓ + k₁` for some `ℓ ≥ 1` and `2 ≤ k₁ ≤ n_p`; and
`n_p` if `k = s_{ℓ+1}` for some `ℓ ≥ 1`.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras,
"Analytical Study and Efficient Evaluation of the
Josephus Function", Proposition 4. -/
theorem_wanted josephus_fixed_succ_cases (k np : ℕ)
    (hk : 2 ≤ k) (hnp : 1 ≤ np)
    (hfix : MetaMathlibExt.josephus k np = np) :
    (k ≤ np + 1 → MetaMathlibExt.josephus k (np + 1) = k - 1) ∧
    (∀ ℓ : ℕ, 1 ≤ ℓ → k = ℓ * (np + 1) + 1 →
      MetaMathlibExt.josephus k (np + 1) = np + 1) ∧
    (∀ ℓ k1 : ℕ, 1 ≤ ℓ → 2 ≤ k1 → k1 ≤ np →
      k = ℓ * (np + 1) + k1 →
        MetaMathlibExt.josephus k (np + 1) = k1 - 1) ∧
    (∀ ℓ : ℕ, 1 ≤ ℓ → k = (ℓ + 1) * (np + 1) →
      MetaMathlibExt.josephus k (np + 1) = np)

/-- **Proposition 4**, final clause: for `n_p ≥ k - 1`,
`J_k(n_p) = n_p` if and only if `J_k(n_p + 1) = k - 1`.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras,
"Analytical Study and Efficient Evaluation of the
Josephus Function", Proposition 4. -/
theorem_wanted josephus_eq_self_iff (k np : ℕ) (hk : 2 ≤ k)
    (hnp : k - 1 ≤ np) :
    MetaMathlibExt.josephus k np = np ↔
      MetaMathlibExt.josephus k (np + 1) = k - 1

/-- **Lemma 6**(a): with `p := J_k(n)`, if
`p + k * m ≤ n + m` then `J_k(n + m) = p + k * m`.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras,
"Analytical Study and Efficient Evaluation of the
Josephus Function", Lemma 6. -/
theorem_wanted josephus_add_eq_of_le (k n m : ℕ) (hk : 2 ≤ k)
    (hn : 1 ≤ n)
    (h : MetaMathlibExt.josephus k n + k * m ≤ n + m) :
    MetaMathlibExt.josephus k (n + m) =
      MetaMathlibExt.josephus k n + k * m

/-- **Lemma 6**(b), with the single-wrap hypothesis (see
the module docstring): if `m` is the smallest nonnegative
integer with `J_k(n) + k * m > n + m` and moreover
`J_k(n) + k * m ≤ 2 * (n + m)`, then
`J_k(n + m) = J_k(n) + k * m - (n + m)`.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras,
"Analytical Study and Efficient Evaluation of the
Josephus Function", Lemma 6. -/
theorem_wanted josephus_add_eq_sub_of_minimal (k n m : ℕ)
    (hk : 2 ≤ k) (hn : 1 ≤ n)
    (hmin : (∀ m' : ℕ, m' < m →
        MetaMathlibExt.josephus k n + k * m' ≤ n + m') ∧
      n + m < MetaMathlibExt.josephus k n + k * m)
    (hwrap : MetaMathlibExt.josephus k n + k * m ≤ 2 * (n + m)) :
    MetaMathlibExt.josephus k (n + m) =
      MetaMathlibExt.josephus k n + k * m - (n + m)

/-- **Corollary 7**: `2k - 2` is always an extremal point;
precisely, if `J_k(2k - 2) ≤ k - 1` then `2k - 3` is a
high extremal point and `2k - 2` is low extremal, and if
`J_k(2k - 2) > k - 1` then `2k - 2` is a high extremal
point and `2k - 1` is low extremal.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras,
"Analytical Study and Efficient Evaluation of the
Josephus Function", Corollary 7. -/
theorem_wanted extremal_two_mul_sub (k : ℕ) (hk : 2 ≤ k) :
    (MetaMathlibExt.josephus k (2 * k - 2) ≤ k - 1 →
      IsHighExtremal k (2 * k - 3) ∧
        IsLowExtremal k (2 * k - 2)) ∧
    (k - 1 < MetaMathlibExt.josephus k (2 * k - 2) →
      IsHighExtremal k (2 * k - 2) ∧
        IsLowExtremal k (2 * k - 1))

/-- **Lemma 8**(a): if `j := J_k(n + 1) ∈ [[1, k - 1]]`
(so `n + 1` is a low extremal point), the nonnegative
solutions of `j + k * m ≤ n + 1 + m` are exactly
`m ≤ ⌊(n - (j - 1)) / (k - 1)⌋`, and that bound is at
least `1` when `n ≥ k - 2 + j`.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras,
"Analytical Study and Efficient Evaluation of the
Josephus Function", Lemma 8. -/
theorem_wanted shift_le_iff_le_div (k n : ℕ) (hk : 2 ≤ k)
    (hj : MetaMathlibExt.josephus k (n + 1) ≤ k - 1) :
    (∀ m : ℕ, MetaMathlibExt.josephus k (n + 1) + k * m ≤ n + 1 + m ↔
      m ≤ (n - (MetaMathlibExt.josephus k (n + 1) - 1)) / (k - 1)) ∧
    (k - 2 + MetaMathlibExt.josephus k (n + 1) ≤ n →
      1 ≤ (n - (MetaMathlibExt.josephus k (n + 1) - 1)) / (k - 1))

/-- **Theorem 9**(a): if `n_e ≥ 2k - 3` is a high
extremal point and `j := J_k(n_e + 1)`, then
`J_k(n_e + 1 + m) = j + k * m` for all
`m ≤ ⌊(n_e - (j - 1)) / (k - 1)⌋`.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras,
"Analytical Study and Efficient Evaluation of the
Josephus Function", Theorem 9. -/
theorem_wanted josephus_add_eq_of_high (k ne m : ℕ)
    (hk : 2 ≤ k) (hne : 2 * k - 3 ≤ ne)
    (hhigh : IsHighExtremal k ne)
    (hm : m ≤ (ne - (MetaMathlibExt.josephus k (ne + 1) - 1)) / (k - 1)) :
    MetaMathlibExt.josephus k (ne + 1 + m) =
      MetaMathlibExt.josephus k (ne + 1) + k * m

/-- **Theorem 13**: the Josephus function `J_k` has
infinitely many fixed points.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras,
"Analytical Study and Efficient Evaluation of the
Josephus Function", Theorem 13. -/
theorem_wanted infinite_fixedPoints (k : ℕ) (hk : 2 ≤ k) :
    {n : ℕ | MetaMathlibExt.josephus k n = n}.Infinite

end MathlibExt.NumberTheory.JosephusWanted
