/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.Parity

/-!
# Fried's alternating binomial identity

For integers `a` and `b` let `C a b` be the binomial coefficient `a.toNat.choose b.toNat` when
`0 ≤ a` and `0 ≤ b`, and `0` otherwise. For natural numbers `n`, `r`, `s` with `r ≤ n` and
`s ≤ 2 * r`, with all arguments computed in `ℤ`,
`∑ k ∈ Finset.range (n + 1), (-1) ^ k * C n k * C (2n - 2r) (n - k) * C (n - k) (n - 2r + s) *
C (2r - k - s) (n - s) = (-1) ^ n * C n (2r - n) * C (2n - 2r) (n - s)`
(`MetaMathlibExt.fried_alternating_binomial_identity`).

## Proof outline

At most one term of the sum is nonzero, the one with `k = 2r - n`. If `k < 2r - n`, then
`n - k > 2n - 2r`, so `C (2n - 2r) (n - k) = 0`; if `k > 2r - n`, then `n - s > 2r - k - s`, so
`C (2r - k - s) (n - s) = 0`. When `2r < n` every term vanishes, and so does `C n (2r - n)`.
Otherwise `k = 2r - n` lies in the range of summation, its sign `(-1) ^ (2r - n)` is `(-1) ^ n`,
its factor `C (2n - 2r) (2n - 2r)` is `1`, and its remaining factors
`C (2n - 2r) (n - 2r + s) * C (n - s) (n - s)` equal `C (2n - 2r) (n - s)`: by the symmetry
`C a b = C a (a - b)` when `s ≤ n`, and because both sides vanish when `s > n`.

## Implementation notes

`fried_alternating_binomial_identity` keeps the full name, the statement and the docstring it had
as a wanted theorem in `WantedExt.Combinatorics.Enumerative.TenOeisConjecturesWanted`. Neither
hypothesis is needed for the identity: the proof does not use `s ≤ 2 * r`, and when `r > n` both
sides vanish because `2n - 2r < 0`. Both are kept so that the statement stays the one of its
source, and the unused-variables linter is turned off for this declaration because of
`s ≤ 2 * r`.

## References

The theorem's docstring cites its source, Sela Fried's *Proofs of Ten Conjectures From the OEIS*
(Journal of Integer Sequences, 2026). The proof here is self-contained.
-/

namespace MetaMathlibExt

@[expose] public section

set_option linter.unusedVariables false in
/-- **Fried's alternating binomial identity.** For integers $a$ and $b$ let $\binom{a}{b}$ be the
binomial coefficient when $a, b \ge 0$ (so $0$ when $b > a$), and $0$ when $a < 0$ or $b < 0$.
For natural numbers $n$, $r$, $s$ with $r \le n$ and $s \le 2r$, with all arguments computed in
the integers,
$$\sum_{k=0}^{n} (-1)^k \binom{n}{k} \binom{2n-2r}{n-k} \binom{n-k}{n-2r+s}
\binom{2r-k-s}{n-s} = (-1)^n \binom{n}{2r-n} \binom{2n-2r}{n-s}.$$

Source: Sela Fried, *Proofs of Ten Conjectures From the OEIS*, Journal of Integer Sequences 29
(2026), Article 26.1.8, Lemma 1 (`jis-2026-26.1.8-lem-1`). -/
theorem fried_alternating_binomial_identity (n r s : ℕ) (hr : r ≤ n)
    (hs : s ≤ 2 * r) :
    let C : ℤ → ℤ → ℤ := fun a b => if 0 ≤ a ∧ 0 ≤ b then (a.toNat.choose b.toNat : ℤ) else 0
    ∑ k ∈ Finset.range (n + 1),
        (-1) ^ k * C n k * C (2 * n - 2 * r) (n - k) * C (n - k) (n - 2 * r + s) *
          C (2 * r - k - s) (n - s) =
      (-1) ^ n * C n (2 * r - n) * C (2 * n - 2 * r) (n - s) := by
  intro C
  -- `C a b` vanishes when `a < b` or `b < 0`; together these cover `a < 0`.
  have hC0 : ∀ a b : ℤ, a < b ∨ b < 0 → C a b = 0 := by
    intro a b h
    simp only [C]
    split_ifs with hab
    · have hlt : a.toNat < b.toNat := by omega
      simp [Nat.choose_eq_zero_of_lt hlt]
    · rfl
  have hCself : ∀ a : ℤ, 0 ≤ a → C a a = 1 := by
    intro a ha
    simp [C, ha]
  -- The symmetry `C a b = C a (a - b)` holds for `0 ≤ a`, including the vanishing cases.
  have hCsymm : ∀ a b : ℤ, 0 ≤ a → C a b = C a (a - b) := by
    intro a b ha
    by_cases hb : 0 ≤ b ∧ b ≤ a
    · have hab : 0 ≤ a - b := by omega
      have hsub : (a - b).toNat = a.toNat - b.toNat := by omega
      simp only [C, ha, hb.1, hab, and_self, ↓reduceIte, hsub]
      rw [Nat.choose_symm (by omega)]
    · rw [hC0 a b (by omega), hC0 a (a - b) (by omega)]
  -- Every term with `k ≠ 2r - n` vanishes.
  have hterm : ∀ k : ℕ, (k : ℤ) ≠ 2 * r - n →
      (-1) ^ k * C n k * C (2 * n - 2 * r) (n - k) * C (n - k) (n - 2 * r + s) *
        C (2 * r - k - s) (n - s) = 0 := by
    intro k hk
    rcases lt_or_gt_of_ne hk with hk | hk
    · rw [hC0 (2 * n - 2 * r) (n - k) (Or.inl (by omega))]
      simp
    · rw [hC0 (2 * r - k - s) (n - s) (by omega)]
      simp
  rcases lt_or_ge (2 * r) n with h2r | h2r
  · -- No term survives, and `C n (2r - n) = 0`.
    rw [Finset.sum_eq_zero (fun k _ => hterm k (by omega)),
      hC0 n (2 * r - n) (Or.inr (by omega))]
    simp
  · -- Only the term `k = 2r - n` survives.
    obtain ⟨j, hj⟩ : ∃ j : ℕ, (j : ℤ) = 2 * r - n := ⟨2 * r - n, by omega⟩
    rw [Finset.sum_eq_single_of_mem j (Finset.mem_range.2 (by omega))
      (fun k _ hk => hterm k (by omega))]
    have hsign : (-1 : ℤ) ^ j = (-1) ^ n := by
      rw [show n = j + 2 * (n - r) by omega, pow_add,
        Even.neg_one_pow (α := ℤ) (even_two_mul (n - r)), mul_one]
    rw [hsign, ← hj, show (n : ℤ) - j = 2 * n - 2 * r by omega,
      show 2 * (r : ℤ) - j - s = n - s by omega, hCself _ (by omega), mul_one]
    rcases le_or_gt s n with hsn | hsn
    · rw [hCself _ (by omega), mul_one, hCsymm (2 * n - 2 * r) (n - 2 * r + s) (by omega),
        show 2 * (n : ℤ) - 2 * r - (n - 2 * r + s) = n - s by omega]
    · rw [hC0 (n - s) (n - s) (Or.inr (by omega)),
        hC0 (2 * n - 2 * r) (n - s) (Or.inr (by omega))]
      simp

end

end MetaMathlibExt
