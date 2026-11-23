/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Algebra.Ring.GeomSum

/-!
# The Alon–Matias–Szegedy estimator for the frequency moment `F_k`

For a stream `a₁, …, a_m` and `k ≥ 1`, Alon, Matias and Szegedy pick a position `p` uniformly at
random, let `r = #{q ≥ p : a_q = a_p}` be the number of occurrences of `a_p` from position `p` on,
and output `X = m (r^k - (r - 1)^k)`. Then `E[X] = F_k` and `E[X²] ≤ k F₁ F_{2k-1}`, and
`F₁ F_{2k-1} ≤ n^{1-1/k} F_k²` for `n` symbols, so the mean of `8 k n^{1-1/k} / λ²` copies is a
`(1 ± λ)`-approximation with probability at least `7 / 8` (N. Alon, Y. Matias and M. Szegedy,
"The space complexity of approximating the frequency moments", J. Comput. System Sci. 58 (1999)
137–147, proof of Theorem 2.1).

The expectation over the uniform position is written as the average `(1 / m) ∑_p`.

## Main results

- `suffixCount`, `basicEstimator`: the quantities `r` and `X`.
- `sum_suffixCount`: the multiset of the `r`'s is the union over symbols `i` of `{1, …, mᵢ}`.
- `average_basicEstimator`: `E[X] = F_k`.
- `average_basicEstimator_sq_le`: `E[X²] ≤ k F₁ F_{2k-1}`.
- `sum_mul_sum_pow_le`, `sum_mul_sum_le_rpow`: the inequality `F₁ F_{2k-1} ≤ n^{1-1/k} F_k²`.
-/

@[expose] public section

open Finset

namespace MathlibExt.Probability.Streaming.AMS

variable {ι : Type*} [DecidableEq ι]

/-- **Suffix count of a stream position.** For a stream `l = (a₀, …, a_{m-1})` and a position
`p`, the number `r = #{q ≥ p : a_q = a_p}` of occurrences of `a_p` from position `p` on (N. Alon,
Y. Matias and M. Szegedy, J. Comput. System Sci. 58 (1999), proof of Theorem 2.1). -/
def suffixCount (l : List ι) (p : Fin l.length) : ℕ := (l.drop p).count l[p]

/-- **The AMS basic estimator of `F_k`.** For a stream `l` of length `m` and a position `p`, the
value `X = m (r^k - (r - 1)^k)` with `r` the suffix count of `p` (N. Alon, Y. Matias and
M. Szegedy, J. Comput. System Sci. 58 (1999), proof of Theorem 2.1). -/
noncomputable def basicEstimator (k : ℕ) (l : List ι) (p : Fin l.length) : ℝ :=
  l.length * ((suffixCount l p : ℝ) ^ k - ((suffixCount l p : ℝ) - 1) ^ k)

/-- **Suffix counts enumerate each multiplicity once.** For every `g : ℕ → ℝ` and stream `l`,
`∑_p g(r_p) = ∑ᵢ ∑_{r=1}^{mᵢ} g(r)`: the suffix counts of the positions holding symbol `i` are
exactly `1, …, mᵢ`. This is the regrouping behind the computation of `E[X]` and `E[X²]` in
N. Alon, Y. Matias and M. Szegedy, J. Comput. System Sci. 58 (1999), proof of Theorem 2.1. -/
theorem sum_suffixCount [Fintype ι] (g : ℕ → ℝ) (l : List ι) :
    ∑ p : Fin l.length, g (suffixCount l p) =
      ∑ i, ∑ r ∈ range (l.count i), g (r + 1) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have hs : ∀ q : Fin t.length, suffixCount (a :: t) q.succ = suffixCount t q := by
      intro q
      simp [suffixCount, Fin.val_succ]
    have h0 : suffixCount (a :: t) (0 : Fin (t.length + 1)) = t.count a + 1 := by
      simp [suffixCount]
    have hcount : ∀ i, ∑ r ∈ range ((a :: t).count i), g (r + 1) =
        ∑ r ∈ range (t.count i), g (r + 1) + if i = a then g (t.count a + 1) else 0 := by
      intro i
      by_cases h : i = a
      · subst h; simp [List.count_cons_self, Finset.sum_range_succ]
      · simp [Ne.symm h, h]
    calc ∑ p : Fin (t.length + 1), g (suffixCount (a :: t) p)
        = g (suffixCount (a :: t) 0) + ∑ q : Fin t.length, g (suffixCount (a :: t) q.succ) :=
          Fin.sum_univ_succ _
      _ = g (t.count a + 1) + ∑ i, ∑ r ∈ range (t.count i), g (r + 1) := by
          rw [h0]; simp only [hs]; rw [ih]
      _ = ∑ i, ∑ r ∈ range ((a :: t).count i), g (r + 1) := by
          simp only [hcount, Finset.sum_add_distrib, Finset.sum_ite_eq', mem_univ, ite_true]
          ring

private theorem sum_range_pow_sub (k : ℕ) (hk : 1 ≤ k) (M : ℕ) :
    ∑ r ∈ range M, (((r + 1 : ℕ) : ℝ) ^ k - (((r + 1 : ℕ) : ℝ) - 1) ^ k) = (M : ℝ) ^ k := by
  have := Finset.sum_range_sub (fun r : ℕ => ((r : ℝ)) ^ k) M
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at this ⊢
  rw [this]
  simp [zero_pow (by omega : k ≠ 0)]

/-- `a^k - b^k ≤ k a^{k-1} (a - b)` for `0 ≤ b ≤ a`. -/
private theorem pow_sub_pow_le (k : ℕ) {a b : ℝ} (hb : 0 ≤ b) (hab : b ≤ a) :
    a ^ k - b ^ k ≤ k * a ^ (k - 1) * (a - b) := by
  rw [← geom_sum₂_mul]
  have ha : 0 ≤ a := hb.trans hab
  refine mul_le_mul_of_nonneg_right ?_ (sub_nonneg.2 hab)
  calc ∑ i ∈ range k, a ^ i * b ^ (k - 1 - i) ≤ ∑ _i ∈ range k, a ^ (k - 1) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ k - 1 := by simp at hi; omega
        calc a ^ i * b ^ (k - 1 - i) ≤ a ^ i * a ^ (k - 1 - i) :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb hab _) (pow_nonneg ha _)
          _ = a ^ (k - 1) := by rw [← pow_add]; congr 1; omega
    _ = k * a ^ (k - 1) := by simp

/-- **The AMS estimator is unbiased for `F_k`.** For `k ≥ 1` and every stream `l` of length `m`,
the average of `X = m (r_p^k - (r_p - 1)^k)` over the `m` positions `p` is
`F_k = ∑ᵢ mᵢ^k`: if `p` is uniform, `E[X] = F_k` (N. Alon, Y. Matias and M. Szegedy, J. Comput.
System Sci. 58 (1999), proof of Theorem 2.1). For the empty stream both sides are `0`. -/
theorem average_basicEstimator [Fintype ι] (k : ℕ) (hk : 1 ≤ k) (l : List ι) :
    (1 / l.length : ℝ) * ∑ p, basicEstimator k l p = ∑ i, (l.count i : ℝ) ^ k := by
  rcases Nat.eq_zero_or_pos l.length with h | h
  · have : l = [] := List.length_eq_zero_iff.1 h
    subst this
    simp [zero_pow (by omega : k ≠ 0)]
  have hm : (l.length : ℝ) ≠ 0 := by exact_mod_cast h.ne'
  simp only [basicEstimator]
  rw [← Finset.mul_sum, ← mul_assoc, one_div_mul_cancel hm, one_mul]
  have := sum_suffixCount (fun r : ℕ => ((r : ℝ)) ^ k - ((r : ℝ) - 1) ^ k) l
  rw [this]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact sum_range_pow_sub k hk _

/-- **Second moment of the AMS estimator.** For `k ≥ 1` and every stream `l` of length `m`, the
average of `X²` over the `m` positions is at most `k F₁ F_{2k-1} = k m ∑ᵢ mᵢ^{2k-1}` (N. Alon,
Y. Matias and M. Szegedy, J. Comput. System Sci. 58 (1999), proof of Theorem 2.1, using
`a^k - b^k ≤ (a - b) k a^{k-1}`). -/
theorem average_basicEstimator_sq_le [Fintype ι] (k : ℕ) (hk : 1 ≤ k) (l : List ι) :
    (1 / l.length : ℝ) * ∑ p, basicEstimator k l p ^ 2 ≤
      k * l.length * ∑ i, (l.count i : ℝ) ^ (2 * k - 1) := by
  rcases Nat.eq_zero_or_pos l.length with h | h
  · have : l = [] := List.length_eq_zero_iff.1 h
    subst this
    simp
  have hm : (l.length : ℝ) ≠ 0 := by exact_mod_cast h.ne'
  set d : ℕ → ℝ := fun r => (r : ℝ) ^ k - ((r : ℝ) - 1) ^ k with hd
  have hX : ∀ p, basicEstimator k l p ^ 2 = (l.length : ℝ) ^ 2 * d (suffixCount l p) ^ 2 := by
    intro p; simp only [basicEstimator, hd]; ring
  simp_rw [hX]
  rw [← Finset.mul_sum, ← mul_assoc, sq (l.length : ℝ), ← mul_assoc, one_div_mul_cancel hm,
    one_mul]
  have := sum_suffixCount (fun r => d r ^ 2) l
  rw [this]
  have key : ∀ i, ∑ r ∈ range (l.count i), d (r + 1) ^ 2 ≤
      k * (l.count i : ℝ) ^ (2 * k - 1) := by
    intro i
    set M := l.count i
    -- Each term: `d(r+1)² ≤ k M^{k-1} d(r+1)` for `r + 1 ≤ M`, and `∑ d(r+1) = M^k`.
    have hterm : ∀ r ∈ range M, d (r + 1) ^ 2 ≤ (k * (M : ℝ) ^ (k - 1)) * d (r + 1) := by
      intro r hr
      have hrM : ((r + 1 : ℕ) : ℝ) ≤ M := by exact_mod_cast (Finset.mem_range.1 hr)
      have hr0 : (0 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) - 1 := by
        push_cast; linarith [(r.cast_nonneg : (0:ℝ) ≤ r)]
      have hdnn : 0 ≤ d (r + 1) := by
        simp only [hd]
        exact sub_nonneg.2 (pow_le_pow_left₀ hr0 (by linarith) k)
      have hdle : d (r + 1) ≤ k * (M : ℝ) ^ (k - 1) := by
        simp only [hd]
        calc ((r + 1 : ℕ) : ℝ) ^ k - (((r + 1 : ℕ) : ℝ) - 1) ^ k
            ≤ k * ((r + 1 : ℕ) : ℝ) ^ (k - 1) * (((r + 1 : ℕ) : ℝ) - (((r + 1 : ℕ) : ℝ) - 1)) :=
              pow_sub_pow_le k hr0 (by linarith)
          _ = k * ((r + 1 : ℕ) : ℝ) ^ (k - 1) := by ring
          _ ≤ k * (M : ℝ) ^ (k - 1) :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hrM _) (by positivity)
      rw [sq]
      exact mul_le_mul_of_nonneg_right hdle hdnn
    calc ∑ r ∈ range M, d (r + 1) ^ 2 ≤ ∑ r ∈ range M, (k * (M : ℝ) ^ (k - 1)) * d (r + 1) :=
          Finset.sum_le_sum hterm
      _ = k * (M : ℝ) ^ (k - 1) * (M : ℝ) ^ k := by
          rw [← Finset.mul_sum]
          congr 1
          simpa [hd] using sum_range_pow_sub k hk M
      _ = k * (M : ℝ) ^ (2 * k - 1) := by
          rw [mul_assoc, ← pow_add]; congr 2; omega
  calc (l.length : ℝ) * ∑ i, ∑ r ∈ range (l.count i), d (r + 1) ^ 2
      ≤ l.length * ∑ i, k * (l.count i : ℝ) ^ (2 * k - 1) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => key i) (by positivity)
    _ = k * l.length * ∑ i, (l.count i : ℝ) ^ (2 * k - 1) := by
        rw [← Finset.mul_sum]; ring

/-- **The moment inequality `F₁ F_{2k-1} ≤ n^{1-1/k} F_k²`, polynomial form.** For nonnegative
reals `x₁, …, x_n` and `k ≥ 1`,
`((∑ xᵢ) (∑ xᵢ^{2k-1}))^k ≤ n^{k-1} (∑ xᵢ^k)^{2k}` (the `k`-th power of the "Fact" in the proof
of Theorem 2.1 of N. Alon, Y. Matias and M. Szegedy, J. Comput. System Sci. 58 (1999), which is
stated there for positive reals). The proof is the source's: `max xᵢ^k ≤ ∑ xᵢ^k` and the power
mean inequality `(∑ xᵢ / n)^k ≤ ∑ xᵢ^k / n`. -/
theorem sum_mul_sum_pow_le {σ : Type*} [Fintype σ] (x : σ → ℝ) (hx : ∀ i, 0 ≤ x i) (k : ℕ)
    (hk : 1 ≤ k) :
    ((∑ i, x i) * ∑ i, x i ^ (2 * k - 1)) ^ k ≤
      (Fintype.card σ : ℝ) ^ (k - 1) * (∑ i, x i ^ k) ^ (2 * k) := by
  set Fk := ∑ i, x i ^ k with hFk
  have hFk0 : 0 ≤ Fk := Finset.sum_nonneg fun i _ => pow_nonneg (hx i) k
  rcases isEmpty_or_nonempty σ with hσ | hσ
  · simp only [univ_eq_empty, sum_empty, zero_mul, zero_pow (by omega : k ≠ 0)]
    positivity
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image univ x univ_nonempty
  set M := x j
  have hM0 : 0 ≤ M := hx j
  have hMk : M ^ k ≤ Fk :=
    Finset.single_le_sum (f := fun i => x i ^ k) (fun i _ => pow_nonneg (hx i) k) (mem_univ j)
  -- `F_{2k-1} ≤ M^{k-1} F_k`.
  have h2k : ∑ i, x i ^ (2 * k - 1) ≤ M ^ (k - 1) * Fk := by
    rw [hFk, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have : x i ^ (2 * k - 1) = x i ^ (k - 1) * x i ^ k := by rw [← pow_add]; congr 1; omega
    rw [this]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hx i) (hj i (mem_univ i)) _)
      (pow_nonneg (hx i) k)
  -- `(∑ x)^k ≤ n^{k-1} F_k` (power mean).
  have hn : (0 : ℝ) < Fintype.card σ := by exact_mod_cast Fintype.card_pos
  have hpm : (∑ i, x i) ^ k ≤ (Fintype.card σ : ℝ) ^ (k - 1) * Fk := by
    have hmean := Real.pow_arith_mean_le_arith_mean_pow univ (fun _ => (1 / Fintype.card σ : ℝ))
      x (fun _ _ => by positivity) (by simp [Finset.card_univ]) (fun i _ => hx i) k
    rw [← Finset.mul_sum, ← Finset.mul_sum, mul_pow] at hmean
    have hk' : (Fintype.card σ : ℝ) ^ k = Fintype.card σ ^ (k - 1) * Fintype.card σ := by
      rw [← pow_succ]; congr 1; omega
    have hpos : (0 : ℝ) < (Fintype.card σ : ℝ) ^ k := pow_pos hn k
    rw [one_div, inv_pow] at hmean
    rw [← hFk] at hmean
    have := mul_le_mul_of_nonneg_left hmean hpos.le
    rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul, hk', mul_assoc,
      mul_inv_cancel_left₀ hn.ne'] at this
    simpa [mul_comm] using this
  have hS0 : 0 ≤ ∑ i, x i := Finset.sum_nonneg fun i _ => hx i
  have h2k0 : 0 ≤ ∑ i, x i ^ (2 * k - 1) := Finset.sum_nonneg fun i _ => pow_nonneg (hx i) _
  -- `F_{2k-1}^k ≤ M^{k(k-1)} F_k^k ≤ F_k^{k-1} F_k^k`.
  have hF2k : (∑ i, x i ^ (2 * k - 1)) ^ k ≤ Fk ^ (2 * k - 1) := by
    calc (∑ i, x i ^ (2 * k - 1)) ^ k ≤ (M ^ (k - 1) * Fk) ^ k := pow_le_pow_left₀ h2k0 h2k k
      _ = (M ^ k) ^ (k - 1) * Fk ^ k := by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm (k - 1)]
      _ ≤ Fk ^ (k - 1) * Fk ^ k :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (pow_nonneg hM0 k) hMk _)
            (pow_nonneg hFk0 k)
      _ = Fk ^ (2 * k - 1) := by rw [← pow_add]; congr 1; omega
  calc ((∑ i, x i) * ∑ i, x i ^ (2 * k - 1)) ^ k
      = (∑ i, x i) ^ k * (∑ i, x i ^ (2 * k - 1)) ^ k := mul_pow _ _ _
    _ ≤ ((Fintype.card σ : ℝ) ^ (k - 1) * Fk) * Fk ^ (2 * k - 1) :=
        mul_le_mul hpm hF2k (pow_nonneg h2k0 k) (by positivity)
    _ = (Fintype.card σ : ℝ) ^ (k - 1) * Fk ^ (2 * k) := by
        rw [mul_assoc, ← pow_succ']; congr 2; omega

/-- **The moment inequality `F₁ F_{2k-1} ≤ n^{1-1/k} F_k²`.** For nonnegative reals
`x₁, …, x_n` and `k ≥ 1`, `(∑ xᵢ) (∑ xᵢ^{2k-1}) ≤ n^{1-1/k} (∑ xᵢ^k)²` (the "Fact" in the proof
of Theorem 2.1 of N. Alon, Y. Matias and M. Szegedy, J. Comput. System Sci. 58 (1999), stated
there for positive reals, with the remark that `x₁ = n^{1/k}`, `x₂ = ⋯ = x_n = 1` shows it is
tight up to a constant factor). -/
theorem sum_mul_sum_le_rpow {σ : Type*} [Fintype σ] (x : σ → ℝ) (hx : ∀ i, 0 ≤ x i) (k : ℕ)
    (hk : 1 ≤ k) :
    (∑ i, x i) * ∑ i, x i ^ (2 * k - 1) ≤
      (Fintype.card σ : ℝ) ^ (1 - 1 / (k : ℝ)) * (∑ i, x i ^ k) ^ 2 := by
  have hA : 0 ≤ (∑ i, x i) * ∑ i, x i ^ (2 * k - 1) :=
    mul_nonneg (Finset.sum_nonneg fun i _ => hx i)
      (Finset.sum_nonneg fun i _ => pow_nonneg (hx i) _)
  have hn : (0 : ℝ) ≤ Fintype.card σ := Nat.cast_nonneg _
  have hB : 0 ≤ (Fintype.card σ : ℝ) ^ (1 - 1 / (k : ℝ)) * (∑ i, x i ^ k) ^ 2 :=
    mul_nonneg (Real.rpow_nonneg hn _) (sq_nonneg _)
  have hk0 : k ≠ 0 := by omega
  refine (pow_le_pow_iff_left₀ hA hB hk0).1 ?_
  have hpow : ((Fintype.card σ : ℝ) ^ (1 - 1 / (k : ℝ))) ^ k = (Fintype.card σ : ℝ) ^ (k - 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn, ← Real.rpow_natCast]
    congr 1
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk0
    rw [Nat.cast_sub hk]
    field_simp
    push_cast
    ring
  rw [mul_pow (_ ^ (1 - 1 / (k : ℝ))), hpow, ← pow_mul]
  simpa only [mul_comm k 2] using sum_mul_sum_pow_le x hx k hk

/-- **Second moment of the AMS estimator against `F_k²`.** For `k ≥ 1` and every stream `l` over
a set `ι` of `n` symbols, the average of `X²` over the positions is at most
`k n^{1-1/k} F_k²`. Consequently (informally; this is not part of the statement) the mean `Y`
of `s₁` independent copies has `Var(Y) ≤ k n^{1-1/k} F_k² / s₁` (N. Alon, Y. Matias and
M. Szegedy, J. Comput. System Sci. 58 (1999), proof of Theorem 2.1). -/
theorem average_basicEstimator_sq_le_rpow [Fintype ι] (k : ℕ) (hk : 1 ≤ k) (l : List ι) :
    (1 / l.length : ℝ) * ∑ p, basicEstimator k l p ^ 2 ≤
      k * (Fintype.card ι : ℝ) ^ (1 - 1 / (k : ℝ)) * (∑ i, (l.count i : ℝ) ^ k) ^ 2 := by
  have hlen : (l.length : ℝ) = ∑ i, (l.count i : ℝ) := by
    have := sum_suffixCount (fun _ => (1 : ℝ)) l
    simpa using this
  refine (average_basicEstimator_sq_le k hk l).trans ?_
  rw [mul_assoc, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  rw [hlen]
  exact sum_mul_sum_le_rpow (fun i => (l.count i : ℝ)) (fun _ => Nat.cast_nonneg _) k hk

end MathlibExt.Probability.Streaming.AMS
