/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Tactic.Ring

/-! # Finite differences of Rascal numbers -/

@[expose] public section

namespace MathlibExt.Combinatorics.Enumerative.RascalNumbersWanted

/-- **Rascal numbers on the integers.** For integers $n$ and $k$, the Rascal number $R_{n,k}$ is
$k(n-k) + 1$ if $0 \le k \le n$, and $0$ otherwise.

Gibbs and Miceli define $R_{n,k}$ by the diamond recurrence of Angorro et al., with value $0$
outside $0 \le k \le n$; Angorro et al. proved that it equals $k(n-k) + 1$ in that range. -/
def rascalZ (n k : ℤ) : ℤ :=
  if 0 ≤ k ∧ k ≤ n then k * (n - k) + 1 else 0

/-- **Vanishing higher finite differences of Rascal numbers.** For natural numbers $n$, $k$ and
$r$ with $k \le n$ and $r \ge 2$, the Rascal numbers satisfy
$\sum_{j=0}^{r} (-1)^{r-j} \binom{r}{j} R_{n+j,k} = 0$.

For $k \le n$ the value $R_{n+j,k}$ is a linear function of $j$, and the sum is its $r$-th
finite difference.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Theorem 12. -/
theorem sum_negOnePow_choose_rascalZ (n k r : ℕ)
    (hkn : k ≤ n) (hr : 2 ≤ r) :
    ∑ j ∈ Finset.range (r + 1),
        (-1 : ℤ) ^ (r - j) * (Nat.choose r j : ℤ) *
          rascalZ ((n + j : ℕ) : ℤ) (k : ℤ) = 0 := by
  let f (j : ℕ) := rascalZ ((n + j : ℕ) : ℤ) k
  have hdiff : fwdDiff 1 f = fun _ => (k : ℤ) := by
    funext j
    simp (disch := omega) only [fwdDiff, f, rascalZ, ite_eq_left, Nat.cast_add,
      Nat.cast_one]
    ring
  have hzero : (fwdDiff 1)^[r] f = fun _ => (0 : ℤ) := by
    rw [show r = r - 2 + 1 + 1 by omega, Function.iterate_succ_apply, hdiff,
      Function.iterate_succ_apply, fwdDiff_const]
    exact Function.iterate_fixed (fwdDiff_const (1 : ℕ) (0 : ℤ)) _
  simpa [f, fwdDiff_iter_eq_sum_shift, zsmul_eq_mul] using congrFun hzero 0

end MathlibExt.Combinatorics.Enumerative.RascalNumbersWanted
