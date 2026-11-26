/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.CyclotomicTraceMetric
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Diameter of the cyclotomic box

The trace distance between any two lattice points in the box `B(p, N)` is at most
`2 N p √(p - 1)`, and this bound is attained at the alternating point and its negation.

Statements from Katerina Saettone, Alexandru Zaharescu and Zhuo Zhang, *On a Special
Metric in Cyclotomic Fields*, INTEGERS 25 (2025), Article A10 (arXiv:2410.22687).
-/

namespace MetaMathlibExt

@[expose] public section

open IsCyclotomicExtension

variable {p : ℕ} [NeZero p] {K : Type*} [Field K] [CharZero K] [IsCyclotomicExtension {p} ℚ K]

private theorem dist_le_of_mem_box {p : ℕ} [NeZero p] {K : Type*} [Field K] [CharZero K]
    [IsCyclotomicExtension {p} ℚ K] (hp : p.Prime) (N : ℕ) (a b : Fin (p - 1) → ℤ)
    (ha : a ∈ cyclotomicBox p N) (hb : b ∈ cyclotomicBox p N) :
    cyclotomicTraceDist p (cyclotomicLatticePoint K a) (cyclotomicLatticePoint K b) ≤
      2 * N * p * √(p - 1 : ℝ) := by
  let c : Fin (p - 1) → ℚ := fun i => ((a i - b i : ℤ) : ℚ)
  have hsub : cyclotomicLatticePoint K a - cyclotomicLatticePoint K b =
      ∑ i, (c i : K) * zeta p ℚ K ^ (i.val + 1) := by
    simp only [cyclotomicLatticePoint, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← sub_mul]
    congr 1
    simp only [c]
    push_cast
    ring
  have heq := (cyclotomicTraceNormSq_eq_and_ge (K := K) hp c).1
  rw [← hsub] at heq
  have hnonneg : 0 ≤ ((p : ℚ) + 1)
      * Algebra.trace ℚ K (cyclotomicLatticePoint K a - cyclotomicLatticePoint K b) ^ 2 := by
    apply mul_nonneg
    · have hpos : (0 : ℚ) ≤ (p : ℚ) := by positivity
      linarith
    · exact sq_nonneg _
  have hle : cyclotomicTraceNormSq p (cyclotomicLatticePoint K a - cyclotomicLatticePoint K b) ≤
      (p : ℚ) ^ 2 * ∑ i, c i ^ 2 := by
    linarith [heq, hnonneg]
  have hp1 : 1 ≤ p := by
    have h2 := hp.two_le
    omega
  have hsum : ∑ i, c i ^ 2 ≤ (p - 1) * (2 * (N : ℚ)) ^ 2 := by
    have hper : ∀ i ∈ Finset.univ, c i ^ 2 ≤ (2 * (N : ℚ)) ^ 2 := by
      intro i _
      have ha_i := Finset.mem_Icc.mp ((Fintype.mem_piFinset.mp ha) i)
      have hb_i := Finset.mem_Icc.mp ((Fintype.mem_piFinset.mp hb) i)
      have hd : |a i - b i| ≤ 2 * (N : ℤ) := by
        rw [abs_le]
        constructor <;> linarith
      have hcast : |c i| ≤ 2 * (N : ℚ) := by
        have h1 : |c i| = (((|a i - b i| : ℤ) : ℚ)) := by
          simp only [c]
          rw [Int.cast_abs]
        rw [h1]
        have h2 : (((|a i - b i| : ℤ) : ℚ)) ≤ (((2 * (N : ℤ) : ℤ) : ℚ)) := by
          exact Int.cast_le.mpr hd
        have h3 : (((2 * (N : ℤ) : ℤ) : ℚ)) = 2 * (N : ℚ) := by push_cast; ring
        linarith
      have h4 : |2 * (N : ℚ)| = 2 * (N : ℚ) := by
        apply abs_of_nonneg
        positivity
      have h5 : |c i| ≤ |2 * (N : ℚ)| := by rw [h4]; exact hcast
      exact sq_le_sq.mpr h5
    have hle2 : ∑ i, c i ^ 2 ≤ ∑ _i : Fin (p - 1), (2 * (N : ℚ)) ^ 2 :=
      Finset.sum_le_sum hper
    have hcard : ∑ _i : Fin (p - 1), (2 * (N : ℚ)) ^ 2 = (p - 1) * (2 * (N : ℚ)) ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_sub hp1, Nat.cast_one]
    linarith
  have hmul : (0 : ℚ) ≤ (p : ℚ) ^ 2 := by positivity
  have hS : cyclotomicTraceNormSq p (cyclotomicLatticePoint K a - cyclotomicLatticePoint K b) ≤
      (p : ℚ) ^ 2 * ((p - 1) * (2 * (N : ℚ)) ^ 2) := by
    calc cyclotomicTraceNormSq p (cyclotomicLatticePoint K a - cyclotomicLatticePoint K b)
        ≤ (p : ℚ) ^ 2 * ∑ i, c i ^ 2 := hle
      _ ≤ (p : ℚ) ^ 2 * ((p - 1) * (2 * (N : ℚ)) ^ 2) := by
          apply mul_le_mul_of_nonneg_left hsum hmul
  have hdist : cyclotomicTraceDist p (cyclotomicLatticePoint K a) (cyclotomicLatticePoint K b) =
      √(cyclotomicTraceNormSq p (cyclotomicLatticePoint K a - cyclotomicLatticePoint K b) : ℝ) := by
    simp [cyclotomicTraceDist, cyclotomicTraceNorm]
  rw [hdist]
  have hpm1 : (0 : ℝ) ≤ (p - 1 : ℝ) := by
    have h1r : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp1
    linarith
  have hy : (0 : ℝ) ≤ 2 * N * p * √(p - 1 : ℝ) := by
    apply mul_nonneg
    · apply mul_nonneg
      · apply mul_nonneg <;> positivity
      · positivity
    · exact Real.sqrt_nonneg _
  have hcast : (cyclotomicTraceNormSq p
      (cyclotomicLatticePoint K a - cyclotomicLatticePoint K b) : ℝ)
      ≤ (p : ℝ) ^ 2 * ((p - 1 : ℝ) * (2 * (N : ℝ)) ^ 2) := by
    have h1 : (cyclotomicTraceNormSq p
        (cyclotomicLatticePoint K a - cyclotomicLatticePoint K b) : ℝ)
        ≤ ((((p : ℚ) ^ 2 * ((p - 1) * (2 * (N : ℚ)) ^ 2) : ℚ)) : ℝ) := by
      exact Rat.cast_le.mpr hS
    have h2 : ((((p : ℚ) ^ 2 * ((p - 1) * (2 * (N : ℚ)) ^ 2) : ℚ)) : ℝ) =
        (p : ℝ) ^ 2 * ((p - 1 : ℝ) * (2 * (N : ℝ)) ^ 2) := by
      push_cast
      ring
    linarith
  have hsq : (cyclotomicTraceNormSq p (cyclotomicLatticePoint K a - cyclotomicLatticePoint K b) : ℝ)
      ≤ (2 * N * p * √(p - 1 : ℝ)) ^ 2 := by
    have hsq0 : (2 * (N : ℝ) * p * √(p - 1 : ℝ)) ^ 2 =
        (p : ℝ) ^ 2 * ((p - 1 : ℝ) * (2 * (N : ℝ)) ^ 2) := by
      have hsqrt : √(p - 1 : ℝ) ^ 2 = (p - 1 : ℝ) := Real.sq_sqrt hpm1
      calc (2 * (N : ℝ) * p * √(p - 1 : ℝ)) ^ 2
          = (2 * (N : ℝ)) ^ 2 * (p : ℝ) ^ 2 * (√(p - 1 : ℝ) ^ 2) := by ring
        _ = (p : ℝ) ^ 2 * ((p - 1 : ℝ) * (2 * (N : ℝ)) ^ 2) := by rw [hsqrt]; ring
    linarith [hcast, hsq0]
  have hle : √(cyclotomicTraceNormSq p
        (cyclotomicLatticePoint K a - cyclotomicLatticePoint K b) : ℝ)
      ≤ √((2 * N * p * √(p - 1 : ℝ)) ^ 2) := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq hy] at hle

private theorem dist_eq_alternating {p : ℕ} [NeZero p] {K : Type*} [Field K] [CharZero K]
    [IsCyclotomicExtension {p} ℚ K] (hp : p.Prime) (hp2 : p ≠ 2) (N : ℕ) :
    cyclotomicTraceDist p (cyclotomicLatticePoint K fun i : Fin (p - 1) => (N : ℤ) * (-1) ^ i.val)
        (cyclotomicLatticePoint K fun i : Fin (p - 1) => -((N : ℤ) * (-1) ^ i.val)) =
      2 * N * p * √(p - 1 : ℝ) := by
  let a₀ : Fin (p - 1) → ℤ := fun i => (N : ℤ) * (-1) ^ i.val
  let b₀ : Fin (p - 1) → ℤ := fun i => -((N : ℤ) * (-1) ^ i.val)
  let c₀ : Fin (p - 1) → ℚ := fun i => ((a₀ i - b₀ i : ℤ) : ℚ)
  have hsub : cyclotomicLatticePoint K a₀ - cyclotomicLatticePoint K b₀ =
      ∑ i, (c₀ i : K) * zeta p ℚ K ^ (i.val + 1) := by
    simp only [cyclotomicLatticePoint, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← sub_mul]
    congr 1
    simp only [c₀, a₀, b₀]
    push_cast
    ring
  have hc : ∀ i : Fin (p - 1), c₀ i = 2 * (N : ℚ) * (-1 : ℚ) ^ i.val := by
    intro i
    simp only [c₀, a₀, b₀]
    push_cast
    ring
  have halt : ∑ i : Fin (p - 1), (-1 : ℚ) ^ i.val = 0 := by
    simpa [hp.even_sub_one hp2] using (Fin.sum_neg_one_pow ℚ (p - 1))
  have hsum0 : ∑ i, c₀ i = 0 := by
    have h1 : ∑ i, c₀ i = (2 * (N : ℚ)) * ∑ i : Fin (p - 1), (-1 : ℚ) ^ i.val := by
      simp only [hc]
      rw [Finset.mul_sum]
    rw [h1, halt, mul_zero]
  have htr0 : Algebra.trace ℚ K
      (cyclotomicLatticePoint K a₀ - cyclotomicLatticePoint K b₀) = 0 := by
    rw [hsub, trace_sum_mul_zeta_pow_succ hp c₀, hsum0, neg_zero]
  have hsq1 : ∀ i : Fin (p - 1), ((-1 : ℚ) ^ i.val) ^ 2 = 1 := by
    intro i
    rw [sq, ← pow_add]
    exact Even.neg_one_pow ⟨i.val, rfl⟩
  have hsq : ∀ i : Fin (p - 1), c₀ i ^ 2 = (2 * (N : ℚ)) ^ 2 := by
    intro i
    rw [hc i]
    have h1 : (2 * (N : ℚ) * (-1 : ℚ) ^ i.val) ^ 2
        = (2 * (N : ℚ)) ^ 2 * (((-1 : ℚ) ^ i.val) ^ 2) := by ring
    rw [h1, hsq1 i, mul_one]
  have hp1 : 1 ≤ p := by
    have h2 := hp.two_le
    omega
  have hsum2 : ∑ i, c₀ i ^ 2 = (p - 1) * (2 * (N : ℚ)) ^ 2 := by
    have h1 : ∑ i, c₀ i ^ 2 = ∑ _i : Fin (p - 1), (2 * (N : ℚ)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      exact hsq i
    rw [h1]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_sub hp1, Nat.cast_one]
  have heq := (cyclotomicTraceNormSq_eq_and_ge (K := K) hp c₀).1
  rw [← hsub] at heq
  have hNorm : cyclotomicTraceNormSq p (cyclotomicLatticePoint K a₀ - cyclotomicLatticePoint K b₀) =
      (p : ℚ) ^ 2 * ((p - 1) * (2 * (N : ℚ)) ^ 2) := by
    rw [heq, htr0]
    simp [hsum2]
  have hdist : cyclotomicTraceDist p (cyclotomicLatticePoint K a₀)
      (cyclotomicLatticePoint K b₀) =
      √(cyclotomicTraceNormSq p
        (cyclotomicLatticePoint K a₀ - cyclotomicLatticePoint K b₀) : ℝ) := by
    simp [cyclotomicTraceDist, cyclotomicTraceNorm]
  rw [hdist, hNorm]
  have hpm1 : (0 : ℝ) ≤ (p - 1 : ℝ) := by
    have h1r : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp1
    linarith
  have hy : (0 : ℝ) ≤ 2 * N * p * √(p - 1 : ℝ) := by
    apply mul_nonneg
    · apply mul_nonneg
      · apply mul_nonneg <;> positivity
      · positivity
    · exact Real.sqrt_nonneg _
  have hysq : (2 * (N : ℝ) * p * √(p - 1 : ℝ)) ^ 2 =
      (((p : ℚ) ^ 2 * ((p - 1) * (2 * (N : ℚ)) ^ 2) : ℚ) : ℝ) := by
    have hsqrt : √(p - 1 : ℝ) ^ 2 = (p - 1 : ℝ) := Real.sq_sqrt hpm1
    have hcast : ((((p : ℚ) ^ 2 * ((p - 1) * (2 * (N : ℚ)) ^ 2) : ℚ)) : ℝ) =
        (p : ℝ) ^ 2 * ((p - 1 : ℝ) * (2 * (N : ℝ)) ^ 2) := by
      push_cast
      ring
    rw [hcast]
    calc (2 * (N : ℝ) * p * √(p - 1 : ℝ)) ^ 2
        = (2 * (N : ℝ)) ^ 2 * (p : ℝ) ^ 2 * (√(p - 1 : ℝ) ^ 2) := by ring
      _ = (p : ℝ) ^ 2 * ((p - 1 : ℝ) * (2 * (N : ℝ)) ^ 2) := by rw [hsqrt]; ring
  rw [← hysq, Real.sqrt_sq hy]

/-- **Diameter of the cyclotomic box.** Let $p$ be an odd prime, let $N$ be a natural number, and
let $K$ be a field generated over $\mathbb{Q}$ by a primitive $p$-th root of unity, with fixed
primitive $p$-th root of unity $\omega \in K$. Let $d(\alpha, \beta) = \lVert \alpha - \beta \rVert$
be the trace metric on $K$, where $\lVert \gamma \rVert \ge 0$ and
$\lVert \gamma \rVert^2 = \sum_{j=1}^{p-1} \operatorname{Tr}_{K/\mathbb{Q}}(\gamma \omega^j)^2$.
Let $B(p, N)$ be the set of integer vectors $a = (a_1, \dots, a_{p-1})$ with $-N \le a_i \le N$
for all $i$, and write $\alpha_a = a_1 \omega + \dots + a_{p-1} \omega^{p-1}$. Then
$d(\alpha_a, \alpha_b) \le 2 N p \sqrt{p - 1}$ for all $a, b \in B(p, N)$, and this bound is
attained: $d(\alpha, -\alpha) = 2 N p \sqrt{p - 1}$ for
$\alpha = N \omega - N \omega^2 + \dots + N \omega^{p-2} - N \omega^{p-1}$, the point whose
coefficient of $\omega^i$ is $(-1)^{i-1} N$.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Lemma 2 (`integers-2025-A10-lem-2`). -/
public theorem cyclotomicBox_diam (hp : p.Prime) (hp2 : p ≠ 2) (N : ℕ) :
    (∀ a ∈ cyclotomicBox p N, ∀ b ∈ cyclotomicBox p N,
      cyclotomicTraceDist p (cyclotomicLatticePoint K a) (cyclotomicLatticePoint K b) ≤
        2 * N * p * √(p - 1 : ℝ)) ∧
    cyclotomicTraceDist p (cyclotomicLatticePoint K fun i : Fin (p - 1) => (N : ℤ) * (-1) ^ i.val)
        (cyclotomicLatticePoint K fun i : Fin (p - 1) => -((N : ℤ) * (-1) ^ i.val)) =
      2 * N * p * √(p - 1 : ℝ) := by
  exact ⟨fun a ha b hb => dist_le_of_mem_box hp N a b ha hb, dist_eq_alternating hp hp2 N⟩

end

end MetaMathlibExt
