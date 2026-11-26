/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import MathlibExt.NumberTheory.LucasSequence
public import MathlibExt.NumberTheory.Recurrences.LucasAlternatingSquaredBinomialSum
public import MathlibExt.NumberTheory.SecondOrderGenValueTrivialFamilies
public import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Two-sided binomial sums of products of Lucas sequences

This module proves four central-binomial identities for products of the two-sided sequences
`secondOrderBiSeq p 0 1` and `secondOrderBiSeq p 2 p` with arbitrary integer shifts.

Source: John M. Campbell and Emrah Kılıç, *Binomial Sums Involving Second-Order Linearly
Recurrent Sequences*, The Fibonacci Quarterly 62 (2024), no. 1, 57–64.
-/

namespace MetaMathlibExt

open Finset

private def central (n : ℕ) (f : ℤ → ℤ) (x : ℤ) : ℤ :=
  ∑ k ∈ range (2 * n + 1), ((2 * n).choose k : ℤ) * f ((k : ℤ) - n + x)

private def average (f : ℤ → ℤ) (x : ℤ) : ℤ :=
  f (x - 1) + 2 * f x + f (x + 1)

private theorem binomial_step (N : ℕ) (f : ℤ → ℤ) (x : ℤ) :
    (∑ k ∈ range (N + 2), ((N + 1).choose k : ℤ) * f (k + x)) =
      (∑ k ∈ range (N + 1), (N.choose k : ℤ) * f (k + x)) +
        ∑ k ∈ range (N + 1), (N.choose k : ℤ) * f (k + (x + 1)) := by
  simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_comm 1 x] using
    sum_choose_succ_mul (fun i _ => f ((i : ℤ) + x)) N

private theorem central_step (n : ℕ) (f : ℤ → ℤ) (x : ℤ) :
    central (n + 1) f x = central n (average f) x := by
  unfold central
  rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega]
  simp only [Nat.cast_add, Nat.cast_one]
  have he (k : ℕ) : (k : ℤ) - ((n : ℤ) + 1) + x = k + (x - n - 1) := by ring
  simp_rw [he]
  rw [binomial_step (2 * n + 1), binomial_step (2 * n), binomial_step (2 * n),
    ← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun k _ => ?_
  dsimp [average]
  have h0 : (k : ℤ) + (x - n - 1) = (k : ℤ) - n + x - 1 := by ring
  have h1 : (k : ℤ) + (x - n - 1 + 1) = (k : ℤ) - n + x := by ring
  have h2 : (k : ℤ) + (x - n - 1 + 1 + 1) = (k : ℤ) - n + x + 1 := by ring
  rw [h0, h1, h2]
  ring

private theorem recurrence_eq (p : ℤ) (f g : ℤ → ℤ)
    (hf : ∀ k, f (k + 2) = p * f (k + 1) + f k)
    (hg : ∀ k, g (k + 2) = p * g (k + 1) + g k)
    (h0 : f 0 = g 0) (h1 : f 1 = g 1) (k : ℤ) : f k = g k := by
  have h : f k = g k ∧ f (k + 1) = g (k + 1) := by
    refine Int.inductionOn' k 0 ⟨h0, h1⟩ ?_ ?_
    · intro i _ hi
      refine ⟨hi.2, ?_⟩
      simp only [add_assoc, one_add_one_eq_two, hf, hg, hi.1, hi.2]
    · intro i _ hi
      refine ⟨?_, by simpa using hi.1⟩
      have hfi := hf (i - 1)
      have hgi := hg (i - 1)
      simp only [sub_add_cancel] at hfi hgi
      have he : i - 1 + 2 = i + 1 := by omega
      rw [he] at hfi hgi
      linear_combination hgi - hfi + hi.2 - p * hi.1
  exact h.1

private theorem companion (p t : ℤ) :
    secondOrderBiSeq p 2 p t =
      2 * secondOrderBiSeq p 0 1 (t + 1) - p * secondOrderBiSeq p 0 1 t := by
  symm
  apply recurrence_eq p _ _ _ (secondOrderBiSeq_add_two p 2 p) _ _ t
  · intro k
    have h0 := secondOrderBiSeq_add_two p 0 1 k
    have h1 := secondOrderBiSeq_add_two p 0 1 (k + 1)
    norm_num only [add_assoc] at h0 h1 ⊢
    linear_combination 2 * h1 - p * h0
  · simp
  · norm_num [secondOrderBiSeq, secondOrderFwd]
    ring

private def bracket (f g : ℤ → ℤ) (m r : ℤ) : ℤ :=
  f (m - 1) * g (r - 1) + 2 * f m * g r + f (m + 1) * g (r + 1)

private theorem bracket_UU (p m r : ℤ) :
    bracket (secondOrderBiSeq p 0 1) (secondOrderBiSeq p 0 1) m r =
      secondOrderBiSeq p 2 p (m + r) := by
  apply recurrence_eq p _ _ _ _ _ _ m
  · intro k
    dsimp [bracket]
    have he : k + 2 - 1 = k + 1 := by omega
    rw [he]
    have h := secondOrderBiSeq_add_two p 0 1 (k - 1)
    rw [show k - 1 + 2 = k + 1 by omega, sub_add_cancel] at h
    have h0 := secondOrderBiSeq_add_two p 0 1 k
    have h1 := secondOrderBiSeq_add_two p 0 1 (k + 1)
    norm_num only [add_assoc, add_sub_cancel_right] at h0 h1 ⊢
    linear_combination secondOrderBiSeq p 0 1 (r - 1) * h +
      2 * secondOrderBiSeq p 0 1 r * h0 + secondOrderBiSeq p 0 1 (r + 1) * h1
  · intro k
    simpa only [add_right_comm] using secondOrderBiSeq_add_two p 2 p (k + r)
  · dsimp [bracket]
    simp only [zero_add, zero_mul, add_zero]
    have hn : secondOrderBiSeq p 0 1 (-1) = 1 :=
      by simpa using (secondOrderBiSeq_small p 0 1).2.2.2
    rw [hn, one_mul, one_mul, companion]
    have h := secondOrderBiSeq_add_two p 0 1 (r - 1)
    rw [show r - 1 + 2 = r + 1 by omega, sub_add_cancel] at h
    linear_combination -h
  · dsimp [bracket]
    simp only [zero_mul, zero_add]
    rw [companion]
    have h := secondOrderBiSeq_add_two p 0 1 r
    rw [show 1 + r + 1 = r + 2 by omega, add_comm 1 r]
    rw [(secondOrderBiSeq_small p 0 1).2.2.1]
    simp only [mul_one, add_zero]
    linear_combination -2 * h

private theorem companion_twice (p t : ℤ) :
    2 * secondOrderBiSeq p 2 p (t + 1) - p * secondOrderBiSeq p 2 p t =
      (p ^ 2 + 4) * secondOrderBiSeq p 0 1 t := by
  rw [companion, companion]
  norm_num only [add_assoc]
  linear_combination 4 * secondOrderBiSeq_add_two p 0 1 t

private theorem bracket_UV (p m r : ℤ) :
    bracket (secondOrderBiSeq p 0 1) (secondOrderBiSeq p 2 p) m r =
      (p ^ 2 + 4) * secondOrderBiSeq p 0 1 (m + r) := by
  calc
    _ = 2 * bracket (secondOrderBiSeq p 0 1) (secondOrderBiSeq p 0 1) m (r + 1) -
        p * bracket (secondOrderBiSeq p 0 1) (secondOrderBiSeq p 0 1) m r := by
      simp only [bracket, companion, sub_add_cancel, add_sub_cancel_right, add_assoc]
      ring
    _ = _ := by
      rw [bracket_UU, bracket_UU, ← add_assoc, companion_twice]

private theorem bracket_VV (p m r : ℤ) :
    bracket (secondOrderBiSeq p 2 p) (secondOrderBiSeq p 2 p) m r =
      (p ^ 2 + 4) * secondOrderBiSeq p 2 p (m + r) := by
  calc
    _ = 4 * bracket (secondOrderBiSeq p 0 1) (secondOrderBiSeq p 0 1) (m + 1) (r + 1) -
        2 * p * bracket (secondOrderBiSeq p 0 1) (secondOrderBiSeq p 0 1) (m + 1) r -
        2 * p * bracket (secondOrderBiSeq p 0 1) (secondOrderBiSeq p 0 1) m (r + 1) +
        p ^ 2 * bracket (secondOrderBiSeq p 0 1) (secondOrderBiSeq p 0 1) m r := by
      simp only [bracket, companion, sub_add_cancel, add_sub_cancel_right, add_assoc]
      ring
    _ = _ := by
      simp only [bracket_UU]
      rw [show m + 1 + (r + 1) = m + r + 2 by ring,
        show m + 1 + r = m + r + 1 by ring, ← add_assoc]
      linear_combination 4 * secondOrderBiSeq_add_two p 2 p (m + r)

private theorem bracket_VU (p m r : ℤ) :
    bracket (secondOrderBiSeq p 2 p) (secondOrderBiSeq p 0 1) m r =
      (p ^ 2 + 4) * secondOrderBiSeq p 0 1 (m + r) := by
  rw [show bracket (secondOrderBiSeq p 2 p) (secondOrderBiSeq p 0 1) m r =
    bracket (secondOrderBiSeq p 0 1) (secondOrderBiSeq p 2 p) r m by dsimp [bracket]; ring,
    bracket_UV, add_comm r m]

private theorem two_step_average (p a b t : ℤ) :
    secondOrderBiSeq p a b (t - 2) + 2 * secondOrderBiSeq p a b t +
      secondOrderBiSeq p a b (t + 2) = (p ^ 2 + 4) * secondOrderBiSeq p a b t := by
  have h0 := secondOrderBiSeq_add_two p a b (t - 2)
  have h1 := secondOrderBiSeq_add_two p a b (t - 1)
  have h2 := secondOrderBiSeq_add_two p a b t
  rw [sub_add_cancel, show t - 2 + 1 = t - 1 by omega] at h0
  rw [show t - 1 + 2 = t + 1 by omega, sub_add_cancel] at h1
  linear_combination h2 + p * h1 - h0

private theorem central_scale (n : ℕ) (f : ℤ → ℤ) (c x : ℤ) :
    central n (fun k => c * f k) x = c * central n f x := by
  unfold central
  rw [mul_sum]
  refine sum_congr rfl fun k _ => ?_
  ring

private theorem central_eigen (q : ℤ) (g : ℤ → ℤ)
    (hg : ∀ x, average g x = q * g x) (n : ℕ) (x : ℤ) :
    central n g x = q ^ n * g x := by
  induction n with
  | zero => simp [central]
  | succ n ih =>
    rw [central_step, show average g = (fun x => q * g x) from funext hg,
      central_scale, ih, pow_succ]
    ring

private theorem central_of_average (q : ℤ) (f g : ℤ → ℤ)
    (hf : ∀ x, average f x = g x) (hg : ∀ x, average g x = q * g x)
    (n : ℕ) (hn : 0 < n) (x : ℤ) : central n f x = q ^ (n - 1) * g x := by
  cases n with
  | zero => omega
  | succ n =>
    rw [central_step, show average f = g from funext hf, central_eigen q g hg]
    simp

private theorem central_interval (n : ℕ) (f : ℤ → ℤ) :
    (∑ k ∈ Icc (-(n : ℤ)) n, ((2 * n).choose (n + k).toNat : ℤ) * f k) =
      central n f 0 := by
  unfold central
  refine sum_nbij' (fun k : ℤ => ((n : ℤ) + k).toNat)
    (fun k : ℕ => (k : ℤ) - n) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    simp only [mem_Icc] at hk
    simp only [mem_range]
    omega
  · intro k hk
    simp only [mem_range] at hk
    simp only [mem_Icc]
    omega
  · intro k hk
    simp only [mem_Icc] at hk
    omega
  · intro k _
    omega
  · intro k hk
    simp only [mem_Icc] at hk
    have he : (((n : ℤ) + k).toNat : ℤ) - n + 0 = k := by omega
    rw [he]

private theorem product_sum (p a b c : ℤ) (f g : ℤ → ℤ)
    (hb : ∀ m r, bracket f g m r = c * secondOrderBiSeq p a b (m + r))
    (n : ℕ) (hn : 0 < n) (m r : ℤ) :
    (∑ k ∈ Icc (-(n : ℤ)) n, ((2 * n).choose (n + k).toNat : ℤ) *
      f (k + m) * g (k + r)) =
      (p ^ 2 + 4) ^ (n - 1) * c * secondOrderBiSeq p a b (m + r) := by
  simp_rw [mul_assoc]
  rw [central_interval]
  have hf (x : ℤ) : average (fun k => f (k + m) * g (k + r)) x =
      c * secondOrderBiSeq p a b (2 * x + (m + r)) := by
    convert hb (x + m) (x + r) using 1
    · dsimp [average, bracket]
      have hsub (z : ℤ) : x - 1 + z = x + z - 1 := by ring
      have hadd (z : ℤ) : x + 1 + z = x + z + 1 := by ring
      rw [hsub m, hsub r, hadd m, hadd r]
      ring
    · congr 2
      ring
  have hg (x : ℤ) :
      average (fun k => c * secondOrderBiSeq p a b (2 * k + (m + r))) x =
        (p ^ 2 + 4) * (c * secondOrderBiSeq p a b (2 * x + (m + r))) := by
    dsimp [average]
    rw [show 2 * (x - 1) + (m + r) = (2 * x + (m + r)) - 2 by ring,
      show 2 * (x + 1) + (m + r) = (2 * x + (m + r)) + 2 by ring]
    linear_combination c * two_step_average p a b (2 * x + (m + r))
  simpa using central_of_average (p ^ 2 + 4)
    (fun k => f (k + m) * g (k + r))
    (fun k => c * secondOrderBiSeq p a b (2 * k + (m + r))) hf hg n hn 0

@[expose] public section

/-- **Two-sided binomial sums of products of Lucas sequences.** Let $p$ be an integer, let $U$
and $V$ be the two-sided second-order sequences for $p$ with $U_0 = 0$, $U_1 = 1$, $V_0 = 2$ and
$V_1 = p$, both satisfying $X_{j+1} = p X_j + X_{j-1}$ for every integer $j$, and put
$\Delta = p^2 + 4$. Then for every natural number $n > 0$ and all integers $m$ and $r$,
$$\sum_{k=-n}^{n} \binom{2n}{n+k} U_{k+m} U_{k+r} = \Delta^{n-1} V_{m+r},$$
$$\sum_{k=-n}^{n} \binom{2n}{n+k} V_{k+m} V_{k+r} = \Delta^{n} V_{m+r},$$
$$\sum_{k=-n}^{n} \binom{2n}{n+k} U_{k+m} V_{k+r} = \Delta^{n} U_{m+r},$$
$$\sum_{k=-n}^{n} \binom{2n}{n+k} V_{k+m} U_{k+r} = \Delta^{n} U_{m+r}.$$

Source: John M. Campbell and Emrah Kılıç, *Binomial Sums Involving Second-Order Linearly Recurrent
Sequences*, The Fibonacci Quarterly 62 (2024), Article 62-1/campbell10202023, Proposition 3.2. -/
public theorem secondOrderBiSeq_sum_central_choose_mul (p : ℤ) (n : ℕ) (hn : 0 < n)
    (m r : ℤ) :
    (∑ k ∈ Finset.Icc (-(n : ℤ)) n, ((2 * n).choose (n + k).toNat : ℤ) *
        secondOrderBiSeq p 0 1 (k + m) * secondOrderBiSeq p 0 1 (k + r) =
      (p ^ 2 + 4) ^ (n - 1) * secondOrderBiSeq p 2 p (m + r)) ∧
    (∑ k ∈ Finset.Icc (-(n : ℤ)) n, ((2 * n).choose (n + k).toNat : ℤ) *
        secondOrderBiSeq p 2 p (k + m) * secondOrderBiSeq p 2 p (k + r) =
      (p ^ 2 + 4) ^ n * secondOrderBiSeq p 2 p (m + r)) ∧
    (∑ k ∈ Finset.Icc (-(n : ℤ)) n, ((2 * n).choose (n + k).toNat : ℤ) *
        secondOrderBiSeq p 0 1 (k + m) * secondOrderBiSeq p 2 p (k + r) =
      (p ^ 2 + 4) ^ n * secondOrderBiSeq p 0 1 (m + r)) ∧
    ∑ k ∈ Finset.Icc (-(n : ℤ)) n, ((2 * n).choose (n + k).toNat : ℤ) *
        secondOrderBiSeq p 2 p (k + m) * secondOrderBiSeq p 0 1 (k + r) =
      (p ^ 2 + 4) ^ n * secondOrderBiSeq p 0 1 (m + r) := by
  have hpow : (p ^ 2 + 4) ^ (n - 1) * (p ^ 2 + 4) = (p ^ 2 + 4) ^ n := by
    rw [← pow_succ]
    congr 1
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using product_sum p 2 p 1 (secondOrderBiSeq p 0 1)
      (secondOrderBiSeq p 0 1) (fun m r => by simpa using bracket_UU p m r) n hn m r
  · simpa only [hpow] using product_sum p 2 p (p ^ 2 + 4) (secondOrderBiSeq p 2 p)
      (secondOrderBiSeq p 2 p) (bracket_VV p) n hn m r
  · simpa only [hpow] using product_sum p 0 1 (p ^ 2 + 4) (secondOrderBiSeq p 0 1)
      (secondOrderBiSeq p 2 p) (bracket_UV p) n hn m r
  · simpa only [hpow] using product_sum p 0 1 (p ^ 2 + 4) (secondOrderBiSeq p 2 p)
      (secondOrderBiSeq p 0 1) (bracket_VU p) n hn m r

end

end MetaMathlibExt
