/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Tactic.Linarith

/-!
# Binomial inversion

Two real sequences `(u_n)` and `(v_n)` satisfy `u_n = ∑_{k=0}^{n} C(n,k) v_k` for every `n` if and
only if they satisfy `v_n = ∑_{k=0}^{n} (-1)^{n-k} C(n,k) u_k` for every `n`.

The proof goes through Mathlib's forward differences. By `fwdDiff_iter_eq_sum_shift`, the `n`-th
forward difference `Δ_[1]^[n] u 0` of `u` at `0` is `∑_{k=0}^{n} (-1)^{n-k} C(n,k) u_k`, and by the
Gregory-Newton formula `shift_eq_sum_fwdDiff_iter`, `u_n = ∑_{k=0}^{n} C(n,k) Δ_[1]^[k] u 0`. So
the second family of identities gives the first. Conversely, a sequence `(v_n)` is determined by
its binomial transform `n ↦ ∑_{k=0}^{n} C(n,k) v_k` (by strong induction on `n`, since the term
`k = n` is `v_n`), so the first family of identities forces `v_n = Δ_[1]^[n] u 0`.

## References

* Bakir Farhi, *q-analogues of sums of consecutive powers of natural numbers and extended Carlitz
  q-Bernoulli numbers and polynomials*, arXiv:2501.02499v1 (2025), Lemma 2.3. The preprint uses it
  to prove its characterization of Carlitz-type q-polynomial sequences (Theorem 2.2).
-/

namespace MetaMathlibExt

open Finset fwdDiff

/-- **Binomial inversion.** For real sequences $(u_n)$ and $(v_n)$, the identities
$u_n = \sum_{k=0}^{n} \binom{n}{k} v_k$ hold for all natural numbers $n$ if and only if the
identities $v_n = \sum_{k=0}^{n} (-1)^{n-k} \binom{n}{k} u_k$ hold for all natural numbers $n$.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Lemma 2.2
(`integers-2026-A85-lem-2-2`). -/
public theorem binomial_inversion_iff (u v : ℕ → ℝ) :
    (∀ n, u n = ∑ k ∈ range (n + 1), (n.choose k : ℝ) * v k) ↔
      ∀ n, v n = ∑ k ∈ range (n + 1), (-1 : ℝ) ^ (n - k) * (n.choose k : ℝ) * u k := by
  -- The `n`-th forward difference of `u` at `0` is the alternating sum.
  have hdiff : ∀ n, Δ_[1]^[n] u 0 =
      ∑ k ∈ range (n + 1), (-1 : ℝ) ^ (n - k) * (n.choose k : ℝ) * u k := fun n => by
    rw [fwdDiff_iter_eq_sum_shift]
    refine sum_congr rfl fun k _ => ?_
    simp [zsmul_eq_mul]
  -- The Gregory-Newton formula expands `u` in its forward differences at `0`.
  have hnewton : ∀ n, u n = ∑ k ∈ range (n + 1), (n.choose k : ℝ) * Δ_[1]^[k] u 0 := fun n => by
    simpa [nsmul_eq_mul] using shift_eq_sum_fwdDiff_iter 1 u n 0
  constructor
  · -- Both `v` and the forward differences of `u` have binomial transform `u`, so they agree.
    intro hu n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      have h := (hu n).symm.trans (hnewton n)
      rw [sum_range_succ, sum_range_succ, Nat.choose_self, Nat.cast_one, one_mul, one_mul,
        sum_congr rfl fun k hk => by rw [ih k (mem_range.mp hk), ← hdiff k]] at h
      linarith [hdiff n]
  · intro hv n
    rw [hnewton n]
    exact sum_congr rfl fun k _ => by rw [hdiff k, hv k]

end MetaMathlibExt
