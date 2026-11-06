/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.BernoulliPolynomials
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import MathlibExt.Analysis.Ramanujan.Part1Ch7Phi
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import MathlibExt.Analysis.Ramanujan.Part1Ch7Entry8

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 7, Entry 8

Berndt's `φ_r(x)` (`chapter7Phi`) for a positive integer `r` is the polynomial
`(B_{r+1}(x + 1) - B_{r+1}(1)) / (r + 1)`, which expands in Bernoulli numbers and in
zeta values at negative odd integers, and gives Faulhaber's power sums at natural `x`.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7

namespace Entry8Bernoullibound

open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

def chapter7BernoulliPolynomial (m : ℕ) (x : ℂ) : ℂ :=
  ((Polynomial.bernoulli m).map (algebraMap ℚ ℂ)).eval x

def chapter7Entry8BernoulliForm (r : ℕ) (x : ℂ) : ℂ :=
  (∑ k ∈ range (r + 1),
      ((r + 1).choose k : ℂ) * (bernoulli k : ℂ) * x ^ (r + 1 - k)) /
      (r + 1 : ℂ) +
    x ^ r

def chapter7Entry8ZetaForm (r : ℕ) (x : ℂ) : ℂ :=
  x ^ (r + 1) / (r + 1 : ℂ) + x ^ r / 2 -
    2 / (r + 1 : ℂ) *
      ∑ k ∈ Icc 1 (r / 2),
        ((r + 1).choose (2 * k) : ℂ) * (k : ℂ) *
          riemannZeta (1 - (2 * k : ℂ)) * x ^ (r + 1 - 2 * k)

/-- **Bernoulli-polynomial form of Berndt's $\varphi_r$.** For a natural number $r$ and
$x \in \mathbb{C}$, $P_r(x) = \frac{B_{r+1}(x + 1) - B_{r+1}(1)}{r + 1}$, where $B_{r+1}$ is the
Bernoulli polynomial of degree $r + 1$.

For positive $r$ this polynomial agrees on $-1 < x < 0$ with Berndt's
$\varphi_r(x) = \zeta(-r) - \zeta(-r, x + 1)$, where $\zeta$ is the Riemann zeta function and
$\zeta(s, a)$ the Hurwitz zeta function, and so extends it to all of $\mathbb{C}$.
-/
def chapter7IntegerPhi (r : ℕ) (x : ℂ) : ℂ :=
  (chapter7BernoulliPolynomial (r + 1) (x + 1) -
      chapter7BernoulliPolynomial (r + 1) 1) /
    (r + 1 : ℂ)

private theorem chapter7IntegerPhi_eq_eval₂ (r : ℕ) (x : ℂ) :
    chapter7IntegerPhi r x =
      ((Polynomial.bernoulli (r + 1)).eval₂ (algebraMap ℚ ℂ) (x + 1) -
        (Polynomial.bernoulli (r + 1)).eval₂ (algebraMap ℚ ℂ) 1) / (r + 1 : ℂ) := by
  simp only [chapter7IntegerPhi, chapter7BernoulliPolynomial, Polynomial.eval_map]

/-- Shift identity for the mapped Bernoulli polynomial:
`B_{r+1}(y+1) = B_{r+1}(y) + (r+1) * y^r`. -/
private theorem eval₂_bernoulli_one_add (r : ℕ) (y : ℂ) :
    (Polynomial.bernoulli (r + 1)).eval₂ (algebraMap ℚ ℂ) (y + 1) =
      (Polynomial.bernoulli (r + 1)).eval₂ (algebraMap ℚ ℂ) y + ((r : ℂ) + 1) * y ^ r := by
  simp only [← Polynomial.eval_map]
  have h := Polynomial.bernoulli_comp_one_add_X (r + 1)
  rw [nsmul_eq_mul] at h
  have hC := congrArg (Polynomial.map (algebraMap ℚ ℂ)) h
  rw [Polynomial.map_comp] at hC
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_one,
    Polynomial.map_X, Polynomial.map_natCast, Polynomial.map_pow] at hC
  have e := congrArg (Polynomial.eval y) hC
  rw [Polynomial.eval_comp] at e
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_natCast] at e
  rw [Nat.add_sub_cancel] at e
  have hcast : ((r + 1 : ℕ) : ℂ) = (r : ℂ) + 1 := by
    rw [Nat.cast_add, Nat.cast_one]
  rw [hcast, add_comm (1 : ℂ) y] at e
  exact e

/-- **Bernoulli and zeta expansions of $P_r$, and sums of powers.** Let $r$ be a positive integer
and $P_r(x) = \frac{B_{r+1}(x + 1) - B_{r+1}(1)}{r + 1}$, where $B_{r+1}$ is the Bernoulli
polynomial of degree $r + 1$. Then for every $x \in \mathbb{C}$,
$P_r(x) = \frac{1}{r + 1} \sum_{k=0}^{r} \binom{r+1}{k} B_k\, x^{r+1-k} + x^r$, where $B_k$
are the Bernoulli numbers with $B_1 = -\tfrac12$, and
$P_r(x) = \frac{x^{r+1}}{r + 1} + \frac{x^r}{2} - \frac{2}{r + 1} Z_r(x)$, where
$Z_r(x) = \sum_{k=1}^{\lfloor r/2 \rfloor} \binom{r+1}{2k}\, k\, \zeta(1 - 2k)\, x^{r+1-2k}$
and $\zeta$ is the Riemann zeta function. Moreover $P_r(n) = \sum_{k=1}^{n} k^r$ for every
natural number $n$.

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 7, Entry 8.
Proves `Wanted` entry `ramanujan_part1_ch7_entry8_bernoullibound`.
-/
theorem ramanujan_part1_ch7_entry8_bernoullibound
    (r : ℕ) (hr : 0 < r) (x : ℂ) :
    chapter7IntegerPhi r x = chapter7Entry8BernoulliForm r x ∧
      chapter7IntegerPhi r x = chapter7Entry8ZetaForm r x ∧
      ∀ n : ℕ,
        chapter7IntegerPhi r n = ∑ k ∈ Icc 1 n, (k : ℂ) ^ r := by
  have hr1 : ((r : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero r
  -- Part 1: `chapter7IntegerPhi` equals the Bernoulli form.
  have hPart1 : chapter7IntegerPhi r x = chapter7Entry8BernoulliForm r x := by
    rw [chapter7IntegerPhi_eq_eval₂]
    exact Entry8.ramanujan_part1_ch7_entry8 r hr x
  -- Part 2: the Bernoulli form equals the zeta form.
  have hsplit : (∑ k ∈ Finset.filter (fun k => Even k) (range (r + 1)),
        ((r + 1).choose k : ℂ) * (bernoulli k : ℂ) * x ^ (r + 1 - k)) +
      (∑ k ∈ Finset.filter (fun k => ¬Even k) (range (r + 1)),
        ((r + 1).choose k : ℂ) * (bernoulli k : ℂ) * x ^ (r + 1 - k)) =
      (∑ k ∈ range (r + 1),
        ((r + 1).choose k : ℂ) * (bernoulli k : ℂ) * x ^ (r + 1 - k)) :=
    Finset.sum_filter_add_sum_filter_not (range (r + 1)) (fun k => Even k) _
  have hodd : (∑ k ∈ Finset.filter (fun k => ¬Even k) (range (r + 1)),
      ((r + 1).choose k : ℂ) * (bernoulli k : ℂ) * x ^ (r + 1 - k)) =
      ((r + 1).choose 1 : ℂ) * (bernoulli 1 : ℂ) * x ^ (r + 1 - 1) := by
    refine Finset.sum_eq_single 1 ?_ ?_
    · intro b hb hne
      have hbO : ¬Even b := (Finset.mem_filter.mp hb).2
      have hbOdd : Odd b := Nat.not_even_iff_odd.mp hbO
      rcases hbOdd with ⟨m, rfl⟩
      have hm : 1 < 2 * m + 1 := by omega
      have hb0 : ((bernoulli (2 * m + 1) : ℚ) : ℂ) = 0 := by
        have h0 := bernoulli_eq_zero_of_odd (show Odd (2 * m + 1) from ⟨m, rfl⟩) hm
        exact_mod_cast h0
      simp [hb0]
    · intro hcon
      have h1mem : (1 : ℕ) ∈ Finset.filter (fun k => ¬Even k) (range (r + 1)) := by
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_range.mpr (by omega), ?_⟩
        exact Nat.not_even_iff_odd.mpr odd_one
      exact absurd h1mem hcon
  have hset : Finset.filter (fun k => Even k) (range (r + 1)) =
      insert 0 (Finset.image (fun j => 2 * j) (Icc 1 (r / 2))) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
      Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨hkr, kEv⟩
      rcases kEv with ⟨m, rfl⟩
      by_cases hm0 : m = 0
      · left
        omega
      · right
        refine ⟨m, ⟨?_, ?_⟩, ?_⟩
        · omega
        · omega
        · show 2 * m = m + m
          ring
    · rintro (rfl | ⟨j, ⟨hj1, hj2⟩, hjk⟩)
      · exact ⟨by omega, ⟨0, rfl⟩⟩
      · have h2 : 2 * j = k := hjk
        exact ⟨by omega, ⟨j, by omega⟩⟩
  have h0not : (0 : ℕ) ∉ Finset.image (fun j => 2 * j) (Icc 1 (r / 2)) := by
    rw [Finset.mem_image]
    rintro ⟨j, hjIcc, hj0⟩
    rw [Finset.mem_Icc] at hjIcc
    obtain ⟨hj1, -⟩ := hjIcc
    have h2 : 2 * j = 0 := hj0
    omega
  have hinj : Set.InjOn (fun j => 2 * j) ↑(Icc 1 (r / 2)) := by
    intro a _ b _ hab
    have h2 : 2 * a = 2 * b := hab
    omega
  have heven : (∑ k ∈ Finset.filter (fun k => Even k) (range (r + 1)),
      ((r + 1).choose k : ℂ) * (bernoulli k : ℂ) * x ^ (r + 1 - k)) =
      (((r + 1).choose 0 : ℂ) * (bernoulli 0 : ℂ) * x ^ (r + 1 - 0)) +
        ∑ j ∈ Icc 1 (r / 2),
          ((r + 1).choose (2 * j) : ℂ) * (bernoulli (2 * j) : ℂ) *
            x ^ (r + 1 - (2 * j)) := by
    rw [hset, Finset.sum_insert h0not, Finset.sum_image hinj]
  have hS : (∑ k ∈ range (r + 1),
      ((r + 1).choose k : ℂ) * (bernoulli k : ℂ) * x ^ (r + 1 - k)) =
      (((r + 1).choose 0 : ℂ) * (bernoulli 0 : ℂ) * x ^ (r + 1 - 0)) +
        (((r + 1).choose 1 : ℂ) * (bernoulli 1 : ℂ) * x ^ (r + 1 - 1)) +
        ∑ j ∈ Icc 1 (r / 2),
          ((r + 1).choose (2 * j) : ℂ) * (bernoulli (2 * j) : ℂ) *
            x ^ (r + 1 - (2 * j)) := by
    rw [← hsplit, heven, hodd]
    ring
  have hF0 : ((r + 1).choose 0 : ℂ) * (bernoulli 0 : ℂ) * x ^ (r + 1 - 0) =
      x ^ (r + 1) := by
    simp [Nat.choose_zero_right, bernoulli_zero]
  have hF1 : ((r + 1).choose 1 : ℂ) * (bernoulli 1 : ℂ) * x ^ (r + 1 - 1) =
      ((r : ℂ) + 1) * (-1 / 2) * x ^ r := by
    rw [Nat.choose_one_right, bernoulli_one, Nat.add_sub_cancel]
    push_cast
    ring
  have hBterm : ∀ j ∈ Icc 1 (r / 2),
      ((r + 1).choose (2 * j) : ℂ) * (bernoulli (2 * j) : ℂ) *
        x ^ (r + 1 - (2 * j)) =
        -2 * (((r + 1).choose (2 * j) : ℂ) * (j : ℂ) *
          riemannZeta (1 - (2 * (j : ℂ))) * x ^ (r + 1 - 2 * j)) := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hB : (bernoulli (2 * j) : ℂ) =
        -(2 * (j : ℂ)) * riemannZeta (1 - 2 * (j : ℂ)) := by
      have hzeta := riemannZeta_neg_nat_eq_bernoulli (2 * j - 1)
      rw [show 2 * j - 1 + 1 = 2 * j from by omega,
        Odd.neg_one_pow (show Odd (2 * j - 1) from ⟨j - 1, by omega⟩)] at hzeta
      have hcast1 : ((2 * j - 1 : ℕ) : ℂ) = 2 * (j : ℂ) - 1 := by
        rw [Nat.cast_sub (show 1 ≤ 2 * j from by omega), Nat.cast_mul, Nat.cast_one,
          Nat.cast_ofNat]
      have edenom : (2 * (j : ℂ) - 1) + 1 = 2 * (j : ℂ) := by ring
      have elhs : -(2 * (j : ℂ) - 1) = 1 - 2 * (j : ℂ) := by ring
      rw [hcast1, edenom, elhs] at hzeta
      have hj0' : ((j : ℂ)) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
      have hj0 : (2 : ℂ) * (j : ℂ) ≠ 0 :=
        mul_ne_zero (by norm_num) hj0'
      rw [hzeta]
      field_simp
    rw [hB]
    ring
  have hFe : (∑ j ∈ Icc 1 (r / 2),
      ((r + 1).choose (2 * j) : ℂ) * (bernoulli (2 * j) : ℂ) *
        x ^ (r + 1 - (2 * j))) =
      -2 * ∑ j ∈ Icc 1 (r / 2),
        ((r + 1).choose (2 * j) : ℂ) * (j : ℂ) *
          riemannZeta (1 - (2 * (j : ℂ))) * x ^ (r + 1 - 2 * j) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j hj => hBterm j hj)
  have hPart2 : chapter7IntegerPhi r x = chapter7Entry8ZetaForm r x := by
    rw [hPart1]
    unfold chapter7Entry8BernoulliForm chapter7Entry8ZetaForm
    rw [hS, hF0, hF1, hFe]
    field_simp
    ring
  -- Part 3: Faulhaber sum via telescoping.
  have hPart3 : ∀ n : ℕ,
      chapter7IntegerPhi r ↑n = ∑ k ∈ Icc 1 n, (k : ℂ) ^ r := by
    intro n
    set B : ℂ → ℂ := fun y => (Polynomial.bernoulli (r + 1)).eval₂ (algebraMap ℚ ℂ) y
    have hterm : ∀ j ∈ range n,
        B ((((j + 1 : ℕ)) : ℂ) + 1) - B ((((j : ℕ)) : ℂ) + 1) =
          ((r : ℂ) + 1) * ((((j : ℕ)) : ℂ) + 1) ^ r := by
      intro j _
      have e := eval₂_bernoulli_one_add r ((((j : ℕ)) : ℂ) + 1)
      have hc : ((((j + 1 : ℕ)) : ℂ) + 1) = ((((j : ℕ)) : ℂ) + 1) + 1 := by
        rw [Nat.cast_add, Nat.cast_one]
      rw [hc]
      linear_combination e
    have hsum : (∑ j ∈ range n, ((((j : ℕ)) : ℂ) + 1) ^ r) =
        ∑ k ∈ Icc 1 n, (k : ℂ) ^ r := by
      apply Finset.sum_bij (fun j _ => j + 1)
      · intro j hj
        have hjn := Finset.mem_range.mp hj
        change j + 1 ∈ Icc 1 n
        simp only [Finset.mem_Icc]
        omega
      · intro a _ b _ hab
        have h2 : a + 1 = b + 1 := hab
        omega
      · intro k hk
        have hkk := Finset.mem_Icc.mp hk
        refine ⟨k - 1, Finset.mem_range.mpr (by omega), ?_⟩
        show k - 1 + 1 = k
        omega
      · intro j hj
        rw [Nat.cast_add, Nat.cast_one]
    have htele : ((r : ℂ) + 1) * ∑ j ∈ range n, ((((j : ℕ)) : ℂ) + 1) ^ r =
        B ((((n : ℕ)) : ℂ) + 1) - B ((((0 : ℕ)) : ℂ) + 1) := by
      have h := Finset.sum_range_sub (fun j => B ((((j : ℕ)) : ℂ) + 1)) n
      have h2 : (∑ j ∈ range n, ((r : ℂ) + 1) * ((((j : ℕ)) : ℂ) + 1) ^ r) =
          ∑ j ∈ range n, (B ((((j + 1 : ℕ)) : ℂ) + 1) - B ((((j : ℕ)) : ℂ) + 1)) :=
        Finset.sum_congr rfl (fun j hj => (hterm j hj).symm)
      rw [Finset.mul_sum, h2]
      exact h
    have h01 : ((((0 : ℕ)) : ℂ) + 1) = 1 := by simp
    rw [h01] at htele
    rw [chapter7IntegerPhi_eq_eval₂, ← hsum, div_eq_iff hr1]
    linear_combination -htele
  exact ⟨hPart1, hPart2, hPart3⟩

/-- **Berndt's $\varphi_r$ as a Bernoulli-polynomial difference for positive integer $r$.** Let
$r$ be a positive integer and $-1 < x < 0$. Then $\varphi_r(x) = \zeta(-r) - \zeta(-r, x + 1)$,
where $\zeta$ is the Riemann zeta function and $\zeta(s, a)$ the Hurwitz zeta function, equals
$P_r(x) = \frac{B_{r+1}(x + 1) - B_{r+1}(1)}{r + 1}$, where $B_{r+1}$ is the Bernoulli
polynomial of degree $r + 1$. -/
theorem chapter7Phi_eq_chapter7IntegerPhi (r : ℕ) (hr : r ≠ 0) (x : Chapter7PhiArgument) :
    chapter7Phi r x = chapter7IntegerPhi r (x : ℝ) := by
  obtain ⟨x, hx1, hx0⟩ := x
  have hB (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
      HurwitzZeta.hurwitzZeta y (-r) =
        -1 / (r + 1) * (Polynomial.bernoulli (r + 1)).eval₂ (algebraMap ℚ ℂ) (y : ℂ) := by
    rw [HurwitzZeta.hurwitzZeta_neg_nat hr hy, Polynomial.eval_map]
  have h1 := hB 1 ⟨zero_le_one, le_rfl⟩
  rw [AddCircle.coe_period, HurwitzZeta.hurwitzZeta_zero, Complex.ofReal_one] at h1
  have hr1 : (r : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero r
  unfold chapter7Phi
  rw [chapter7IntegerPhi_eq_eval₂, h1, hB (x + 1) ⟨by linarith, by linarith⟩]
  push_cast
  field_simp
  ring

/-- **Bernoulli and zeta expansions of Berndt's $\varphi_r$ on $(-1, 0)$.** Let $r$ be a positive
integer and, for $-1 < x < 0$, let $\varphi_r(x) = \zeta(-r) - \zeta(-r, x + 1)$, where $\zeta$
is the Riemann zeta function and $\zeta(s, a)$ the Hurwitz zeta function. Then for every
$-1 < x < 0$,
$\varphi_r(x) = \frac{1}{r + 1} \sum_{k=0}^{r} \binom{r+1}{k} B_k\, x^{r+1-k} + x^r$, where $B_k$
are the Bernoulli numbers with $B_1 = -\tfrac12$, and
$\varphi_r(x) = \frac{x^{r+1}}{r + 1} + \frac{x^r}{2} - \frac{2}{r + 1} Z_r(x)$, where
$Z_r(x) = \sum_{k=1}^{\lfloor r/2 \rfloor} \binom{r+1}{2k}\, k\, \zeta(1 - 2k)\, x^{r+1-2k}$.

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 7, Entry 8, for Berndt's
`φ_r` (`chapter7Phi`) on its domain `-1 < x < 0`. -/
theorem ramanujan_part1_ch7_entry8_phi (r : ℕ) (hr : 0 < r) (x : Chapter7PhiArgument) :
    chapter7Phi r x = chapter7Entry8BernoulliForm r (x : ℝ) ∧
      chapter7Phi r x = chapter7Entry8ZetaForm r (x : ℝ) := by
  rw [chapter7Phi_eq_chapter7IntegerPhi r hr.ne' x]
  obtain ⟨h1, h2, -⟩ := ramanujan_part1_ch7_entry8_bernoullibound r hr (x : ℝ)
  exact ⟨h1, h2⟩

end

end Entry8Bernoullibound

end MathlibExt.Analysis.Ramanujan.Part1Ch7
