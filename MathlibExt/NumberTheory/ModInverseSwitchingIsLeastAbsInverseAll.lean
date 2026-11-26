/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModInverseSwitching

/-!
# Every switching inverse is a least absolute inverse

For Euclidean switching data `(r, s, N)`, every `s i` is the least absolute inverse of `r i`
modulo `r (i - 1)` (`isLeastAbsInverse_all`), by descending induction from `s (N + 1) = 1`
via `isLeastAbsInverse_succ_imp`.

Source: Spiros Konstantogiannis, "The Euclidean Algorithm as a Sequence of Modular Inverse
Switching Formulas", Corollary 1.
-/

@[expose] public section

namespace MathlibExt.NumberTheory.ModInverseSwitchingWanted

-- Descending induction: the bound `i + d = N + 1` counts down to `i = N + 1`.
private theorem isLeastAbsInverse_all.aux {r : ℕ → ℕ} {s : ℕ → ℤ} {N : ℕ}
    (hseq : IsEuclidSwitchSeq r s N) (d i : ℕ)
    (hi : i + d = N + 1) (hi1 : 1 ≤ i) :
    IsLeastAbsInverse (s i) (r i : ℤ) (r (i - 1)) := by
  induction d generalizing i with
  | zero =>
    have hN1 : i = N + 1 := by omega
    subst hN1
    rw [Nat.add_sub_cancel]
    obtain ⟨_, _, hdesc, hlast, _, hs, _⟩ := hseq
    have h := hdesc N le_rfl
    rw [hlast] at h
    rw [hs, hlast]
    refine ⟨by simp, by omega, by omega⟩
  | succ d ih =>
    have hiN : i ≤ N := by omega
    have hnext := ih (i + 1) (by omega) (by omega)
    rw [Nat.add_sub_cancel] at hnext
    exact isLeastAbsInverse_succ_imp r s N hseq i hi1 hiN hnext

/-- **Every switching inverse is a least absolute inverse.** Let $(r_i)$, $(s_i)$ and $N$ be
Euclidean switching data. Then for every $i$ with $1 \le i \le N + 1$, $s_i$ is the least
absolute inverse of $r_i$ modulo $r_{i-1}$.

Source: Spiros Konstantogiannis, "The Euclidean Algorithm as a
Sequence of Modular Inverse Switching Formulas", Corollary 1. -/
theorem isLeastAbsInverse_all
    (r : ℕ → ℕ) (s : ℕ → ℤ) (N : ℕ) (hseq : IsEuclidSwitchSeq r s N) :
    ∀ i : ℕ, 1 ≤ i → i ≤ N + 1 →
      IsLeastAbsInverse (s i) (r i : ℤ) (r (i - 1)) := by
  intro i hi1 hi2
  exact isLeastAbsInverse_all.aux hseq (N + 1 - i) i (by omega) hi1

end MathlibExt.NumberTheory.ModInverseSwitchingWanted
