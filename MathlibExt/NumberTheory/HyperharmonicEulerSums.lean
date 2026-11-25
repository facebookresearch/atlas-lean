/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.PSeries
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Tactic.LinearCombination

/-!
# Duality for hyperharmonic Euler sums

Exchanging the depths and complex parameters leaves the generalized hyperharmonic Euler sum
unchanged. If $P_n(z,x) = (z+x)\cdots(z+x+n-1)$, the common sum is the double series
with terms $[x^k]P_n(r,x)\,[x^p]P_m(t,x)/(n+m+1)!$. Summing a row telescopes after
multiplying by $n+1-t$ and reducing the coefficient degree. A factorial bound gives
absolute convergence, so the same calculation applies to the columns.
-/

namespace MetaMathlibExt

@[expose] public section

open Real

/-- **Generalized hyperharmonic numbers.** For natural numbers $n$ and $k$ and a complex number
$r$, the generalized hyperharmonic number $H_n^{[r]}(k)$ is $0$ when $k > n$; when $k \le n$ it is
the elementary symmetric polynomial of degree $n - k$ in $r, r + 1, \ldots, r + n - 1$ divided by
$n!$, that is,

$$H_n^{[r]}(k) = \frac{1}{n!} \sum_{0 \le j_1 < \cdots < j_{n-k} < n} \prod_{i=1}^{n-k} (r + j_i).$$

The source defines $H_n^{[r]}(k)$ in (2.4) by $(-1)^k k! \, H_n^{[r]}(k) = D_x^k \binom{n+r-x-1}{n}$
at $x = 0$, where $D_x^k$ is the $k$-th derivative in $x$; the explicit form above follows from it.
For $r = 1$ it is the depth-$k$ multiple harmonic number, and for
$r \notin \{0, -1, \ldots, 1 - n\}$ it equals
$\binom{n+r-1}{n} \sum_{1 \le i_1 < \cdots < i_k \le n} \prod_{j=1}^{k} 1/(i_j + r - 1)$,
see (2.10).

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Section 2, (2.4) and (2.10) (`integers-2026-A81-cor-1`). -/
noncomputable def generalizedHyperharmonic (n k : ℕ) (r : ℂ) : ℂ :=
  if k ≤ n then
    (∑ s ∈ (Finset.range n).powersetCard (n - k), ∏ j ∈ s, (r + j)) / n.factorial
  else 0

/-- **Generalized hyperharmonic numbers vanish for $k > n$.** For all natural numbers $n$ and $k$
with $n < k$ and every complex number $r$, the generalized hyperharmonic number $H_n^{[r]}(k)$
equals $0$.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Section 2, (2.4) (`integers-2026-A81-cor-1`). -/
theorem generalizedHyperharmonic_of_lt {n k : ℕ} (h : n < k) (r : ℂ) :
    generalizedHyperharmonic n k r = 0 := by
  simp [generalizedHyperharmonic, Nat.not_le.mpr h]

/-- **Generalized hyperharmonic numbers with both indices zero.** For every complex number $r$,
the generalized hyperharmonic number $H_0^{[r]}(0)$ equals $1$.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Section 2, (2.4) (`integers-2026-A81-cor-1`). -/
@[simp]
theorem generalizedHyperharmonic_zero_zero (r : ℂ) : generalizedHyperharmonic 0 0 r = 1 := by
  simp [generalizedHyperharmonic]

/-- **The value $H_1^{[r]}(0) = r$.** For every complex number $r$, the generalized
hyperharmonic number $H_1^{[r]}(0)$ equals $r$.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Section 2, (2.4) (`integers-2026-A81-cor-1`). -/
theorem generalizedHyperharmonic_one_zero (r : ℂ) : generalizedHyperharmonic 1 0 r = r := by
  simp [generalizedHyperharmonic, Finset.range_one, Finset.powersetCard_one]

/-- **The value $H_1^{[r]}(1) = 1$.** For every complex number $r$, the generalized
hyperharmonic number $H_1^{[r]}(1)$ equals $1$.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Section 2, (2.4) (`integers-2026-A81-cor-1`). -/
theorem generalizedHyperharmonic_one_one (r : ℂ) : generalizedHyperharmonic 1 1 r = 1 := by
  simp [generalizedHyperharmonic]

/-- **Generalized hyperharmonic Euler sum.** For an integer $k \ge 0$, complex numbers $r$ and
$a$ and an integer $p$, the generalized hyperharmonic Euler sum is
$S(k, r; p; a) = \sum_{n \ge k} H_n^{[r]}(k) / (n + a)^p$, where $H_n^{[r]}(k)$ is the
generalized hyperharmonic number. A term whose denominator $(n + a)^p$ vanishes counts as $0$,
and $S(k, r; p; a) = 0$ when the series is not summable.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Corollary 1 display (`integers-2026-A81-cor-1`). -/
noncomputable def hyperharmonicEulerSum (k : ℕ) (r : ℂ) (p : ℤ) (a : ℂ) : ℂ :=
  ∑' n : ℕ, generalizedHyperharmonic (n + k) k r / (((n + k : ℕ) : ℂ) + a) ^ p

/-- **Hyperharmonic Euler sums as sums over all indices.** For every integer $k \ge 0$, complex
numbers $r$ and $a$, and integer $p$, write $H_n^{[r]}(k)$ for the generalized hyperharmonic
number. Then the hyperharmonic Euler sum $S(k, r; p; a) = \sum_{n \ge k} H_n^{[r]}(k) / (n + a)^p$
equals $\sum_{n \ge 0} H_n^{[r]}(k) / (n + a)^p$, because $H_n^{[r]}(k) = 0$ for $n < k$.

Both sides are the sums of the series in the sense of unconditional summation, with the value $0$
assigned to a series that does not converge, and a term with $n + a = 0$ and $p \ne 0$ is read as
$0$, so the identity holds without any hypothesis.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Corollary 1 display (`integers-2026-A81-cor-1`). -/
theorem hyperharmonicEulerSum_eq_tsum (k : ℕ) (r : ℂ) (p : ℤ) (a : ℂ) :
    hyperharmonicEulerSum k r p a =
      ∑' n : ℕ, generalizedHyperharmonic n k r / ((n : ℂ) + a) ^ p := by
  unfold hyperharmonicEulerSum
  refine (add_left_injective k).tsum_eq
    (f := fun n : ℕ => generalizedHyperharmonic n k r / ((n : ℂ) + a) ^ p) ?_
  intro n hn
  by_cases h : k ≤ n
  · exact ⟨n - k, by simp only; omega⟩
  · exact absurd (by simp [generalizedHyperharmonic_of_lt (Nat.lt_of_not_le h)]) hn

/-- **Odd multiple harmonic numbers.** For natural numbers $k$ and $n$, the depth-$k$ odd
harmonic number is the real number
$$O_n(k) = \sum_{1 \le i_1 < \cdots < i_k \le n} \prod_{j=1}^{k} \frac{1}{i_j - 1/2}.$$
In particular $O_n(0) = 1$ (the empty product) and $O_n(k) = 0$ for $k > n$ (the empty sum).

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, (1.8) and (2.11) (`integers-2026-A81-cor-1`). -/
noncomputable def oddMultipleHarmonic (k n : ℕ) : ℝ :=
  ∑ s ∈ (Finset.Icc 1 n).powersetCard k, ∏ i ∈ s, ((i : ℝ) - 1 / 2)⁻¹

/-- **Odd multiple harmonic numbers of depth zero.** For every natural number $n$, the
depth-zero odd harmonic number $O_n(0)$ equals $1$.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, (2.11) (`integers-2026-A81-cor-1`). -/
@[simp]
theorem oddMultipleHarmonic_zero (n : ℕ) : oddMultipleHarmonic 0 n = 1 := by
  simp [oddMultipleHarmonic]

/-- **Vanishing of odd multiple harmonic numbers of large depth.** For natural numbers $k$ and
$n$ with $k > n$, the depth-$k$ odd harmonic number $O_n(k)$ equals $0$.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, (2.11) (`integers-2026-A81-cor-1`). -/
theorem oddMultipleHarmonic_of_lt {k n : ℕ} (h : n < k) : oddMultipleHarmonic k n = 0 := by
  have hcard : (Finset.Icc 1 n).card < k := by simpa using h
  simp [oddMultipleHarmonic, Finset.powersetCard_eq_empty.mpr hcard]

/-- **The first odd harmonic number.** The depth-one odd harmonic number $O_1(1)$ equals $2$.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, (2.11) (`integers-2026-A81-cor-1`). -/
theorem oddMultipleHarmonic_one_one : oddMultipleHarmonic 1 1 = 2 := by
  simp [oddMultipleHarmonic, Finset.powersetCard_one]
  norm_num

/-- **The algebra generated by $\log 2$, $\pi^2$ and odd zeta values.** This is the
$\mathbb{Q}$-subalgebra of $\mathbb{C}$ generated by $\log 2$, $\pi^2$ and the zeta values
$\zeta(3), \zeta(5), \zeta(7), \dots$ (that is, $\zeta(2j+1)$ for all integers $j \ge 1$). It is
written $\mathbb{Q}[\log 2, \pi^2, \zeta(3), \zeta(5), \dots]$.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Corollary 2 (`integers-2026-A81-cor-2`). -/
noncomputable def eulerSumPeriodAlgebra : Subalgebra ℚ ℂ :=
  Algebra.adjoin ℚ
    ({(Real.log 2 : ℂ), (π : ℂ) ^ 2} ∪ Set.range fun j : ℕ => riemannZeta (2 * j + 3))

/-- **Generators of the Euler sum period algebra.** The numbers $\log 2$ and $\pi^2$ and the odd
zeta values $\zeta(2j + 3)$ for all integers $j \ge 0$ lie in the $\mathbb{Q}$-subalgebra
$\mathbb{Q}[\log 2, \pi^2, \zeta(2j+1)_{j \ge 1}]$ of $\mathbb{C}$ that they generate.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Corollary 2 (`integers-2026-A81-cor-2`). -/
theorem generators_mem_eulerSumPeriodAlgebra :
    (Real.log 2 : ℂ) ∈ eulerSumPeriodAlgebra ∧ (π : ℂ) ^ 2 ∈ eulerSumPeriodAlgebra ∧
      ∀ j : ℕ, riemannZeta (2 * j + 3) ∈ eulerSumPeriodAlgebra :=
  ⟨Algebra.subset_adjoin (by simp), Algebra.subset_adjoin (by simp),
    fun j => Algebra.subset_adjoin (Or.inr ⟨j, rfl⟩)⟩

/-- **The algebra generated by $\log 2$, $\pi$, odd zeta values and even beta values.** For
integers $s \ge 2$ let $\beta(s) = \sum_{n \ge 0} (-1)^n / (2n+1)^s$ be the value of the Dirichlet
beta function. This is the $\mathbb{Q}$-subalgebra of $\mathbb{C}$ generated by $\log 2$, $\pi$,
the zeta values $\zeta(2j+1)$ for all integers $j \ge 1$ and the beta values $\beta(2j)$ for all
integers $j \ge 1$. It is written
$\mathbb{Q}[\log 2, \pi, \zeta(2j+1)_{j \ge 1}, \beta(2j)_{j \ge 1}]$.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Corollary 6 (`integers-2026-A81-cor-6`). -/
noncomputable def eulerSumBetaPeriodAlgebra : Subalgebra ℚ ℂ :=
  Algebra.adjoin ℚ
    ({(Real.log 2 : ℂ), (π : ℂ)} ∪ Set.range (fun j : ℕ => riemannZeta (2 * j + 3)) ∪
      Set.range fun j : ℕ =>
        ((∑' n : ℕ, (-1 : ℝ) ^ n / (2 * n + 1 : ℝ) ^ (2 * j + 2) : ℝ) : ℂ))

/-- **Generators of the Euler sum beta period algebra.** The numbers $\log 2$ and $\pi$, the zeta
values $\zeta(2j + 3)$ for all integers $j \ge 0$, and the Dirichlet beta values
$\beta(2j + 2) = \sum_{n \ge 0} (-1)^n / (2n + 1)^{2j+2}$ for all integers $j \ge 0$ lie in the
$\mathbb{Q}$-subalgebra $\mathbb{Q}[\log 2, \pi, \zeta(2j+1)_{j \ge 1}, \beta(2j)_{j \ge 1}]$ of
$\mathbb{C}$ that they generate.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Corollary 6 (`integers-2026-A81-cor-6`). -/
theorem generators_mem_eulerSumBetaPeriodAlgebra :
    (Real.log 2 : ℂ) ∈ eulerSumBetaPeriodAlgebra ∧ (π : ℂ) ∈ eulerSumBetaPeriodAlgebra ∧
      (∀ j : ℕ, riemannZeta (2 * j + 3) ∈ eulerSumBetaPeriodAlgebra) ∧
      ∀ j : ℕ, ((∑' n : ℕ, (-1 : ℝ) ^ n / (2 * n + 1 : ℝ) ^ (2 * j + 2) : ℝ) : ℂ) ∈
        eulerSumBetaPeriodAlgebra :=
  ⟨Algebra.subset_adjoin (by simp), Algebra.subset_adjoin (by simp),
    fun j => Algebra.subset_adjoin (Or.inl (Or.inr ⟨j, rfl⟩)),
    fun j => Algebra.subset_adjoin (Or.inr ⟨j, rfl⟩)⟩

namespace hyperharmonicEulerSum_duality

open Finset Filter Polynomial
open scoped Topology

private noncomputable def rising (z : ℂ) (n : ℕ) : ℂ[X] :=
  ∏ j ∈ range n, (X + C (z + j))

private lemma harmonic_eq_coeff (z : ℂ) (n k : ℕ) :
    generalizedHyperharmonic n k z = (rising z n).coeff k / n.factorial := by
  unfold generalizedHyperharmonic rising
  split_ifs with h
  · rw [Finset.prod_X_add_C_coeff _ _ (by simpa using h), card_range]
  · rw [coeff_eq_zero_of_natDegree_lt, zero_div]
    apply lt_of_le_of_lt _ (Nat.lt_of_not_le h)
    calc
      _ ≤ ∑ j ∈ range n, (X + C (z + j)).natDegree := natDegree_prod_le _ _
      _ = n := by simp only [Polynomial.natDegree_X_add_C, sum_const, card_range,
          smul_eq_mul, mul_one]

-- Normalizing the rising factorial gives a difference whose sum telescopes.
private noncomputable def boundary (z : ℂ) (b n d : ℕ) : ℂ :=
  (rising z n).coeff d * b.factorial / (n + b).factorial

private lemma boundary_step (z : ℂ) (b n d : ℕ) :
    boundary z b (n + 1) d =
      ((z + n) * boundary z b n d + (if d = 0 then 0 else boundary z b n (d - 1))) /
        (n + b + 1) := by
  have h : rising z (n + 1) = rising z n * (X + C (z + n)) := prod_range_succ _ _
  unfold boundary
  rw [h, mul_add, coeff_add, coeff_mul_C, Nat.succ_add, Nat.factorial_succ]
  cases d <;> simp [Nat.cast_add, coeff_mul_X, div_eq_mul_inv, mul_inv_rev] <;> ring

private noncomputable def majorant (z : ℂ) (b : ℕ) (ε : ℝ) (n : ℕ) : ℝ :=
  ∏ j ∈ range n, ((‖z + j‖ + ε) / (j + b + 1))

private lemma majorant_nonneg (z : ℂ) (b : ℕ) {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    0 ≤ majorant z b ε n :=
  prod_nonneg fun _ _ => by positivity

private lemma boundary_bound (z : ℂ) (b : ℕ) {ε : ℝ} (hε : 0 < ε) (n d : ℕ) :
    ‖boundary z b n d‖ * ε ^ d ≤ majorant z b ε n := by
  induction n generalizing d with
  | zero =>
    cases d <;> simp [boundary, rising, majorant, Polynomial.coeff_one, Nat.factorial_ne_zero]
  | succ n ih =>
    rw [boundary_step, majorant, prod_range_succ]
    change _ ≤ majorant z b ε n * _
    have hd : 0 < (n : ℝ) + b + 1 := by positivity
    have hn : ‖(n : ℂ) + b + 1‖ = (n : ℝ) + b + 1 := by
      norm_cast
    rw [norm_div, hn, div_mul_eq_mul_div, mul_div_assoc', div_le_div_iff_of_pos_right hd]
    calc
      _ ≤ (‖z + n‖ * ‖boundary z b n d‖ +
          ‖if d = 0 then 0 else boundary z b n (d - 1)‖) * ε ^ d := by
        gcongr
        simpa only [norm_mul] using norm_add_le ((z + n) * boundary z b n d) _
      _ ≤ majorant z b ε n * (‖z + n‖ + ε) := by
        rw [add_mul, mul_add, mul_assoc]
        apply add_le_add
        · rw [mul_comm (majorant _ _ _ _) ‖_‖]
          exact mul_le_mul_of_nonneg_left (ih d) (norm_nonneg _)
        · cases d with
          | zero => simp [mul_nonneg (majorant_nonneg z b hε n) hε.le]
          | succ d =>
            simpa [pow_succ, ← mul_assoc] using mul_le_mul_of_nonneg_right (ih d) hε.le

-- The gap between Re z and b + 1 controls both the boundary and its weighted series.
private lemma majorant_convergence (z : ℂ) (b : ℕ) (hz : z.re < b + 1) :
    ∃ ε > 0, Tendsto (majorant z b ε) atTop (𝓝 0) ∧
      Summable fun n : ℕ => majorant z b ε n / (n + b + 1) := by
  let ε := ((b : ℝ) + 1 - z.re) / 3
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨N, hN⟩ := exists_nat_ge (z.im ^ 2 / ε - z.re)
  have hnorm (n : ℕ) (hn : N ≤ n) : ‖z + n‖ + 2 * ε ≤ n + b + 1 := by
    -- Squaring absorbs the fixed imaginary part into the slack in the real-part bound.
    have h₁ : z.im ^ 2 / ε ≤ n + z.re := by
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have h₂ := (div_le_iff₀ hε).mp h₁
    have h₃ : 0 ≤ (n : ℝ) + z.re := (by positivity : 0 ≤ z.im ^ 2 / ε).trans h₁
    have hs := Complex.sq_norm_sub_sq_re (z + n)
    simp only [Complex.add_re, Complex.natCast_re, Complex.add_im, Complex.natCast_im,
      add_zero] at hs
    have : ‖z + n‖ ≤ n + z.re + ε := by nlinarith [sq_nonneg ε]
    dsimp [ε] at *
    linarith
  let u (i : ℕ) := majorant z b ε (i + N)
  let v (i : ℕ) := u i / ((i + N : ℕ) + (b : ℝ) + 1)
  have hu (i) : 0 ≤ u i := majorant_nonneg z b hε _
  have hv (i) : 0 ≤ v i := div_nonneg (hu i) (by positivity)
  have hdiff (i : ℕ) : ε * v i ≤ u i - u (i + 1) := by
    have hstep : u (i + 1) = u i * ((‖z + (i + N : ℕ)‖ + ε) / ((i + N : ℕ) + (b : ℝ) + 1)) := by
      dsimp [u, majorant]
      rw [Nat.succ_add, prod_range_succ]
    rw [hstep]
    dsimp only [v]
    have hd : 0 < ((i + N : ℕ) : ℝ) + b + 1 := by positivity
    field_simp
    nlinarith [mul_nonneg (hu i) (sub_nonneg.mpr (hnorm (i + N) (by omega)))]
  have hs : Summable v := by
    apply summable_of_sum_range_le hv (c := u 0 / ε)
    intro M
    rw [le_div_iff₀ hε, mul_comm, mul_sum]
    calc
      _ ≤ ∑ i ∈ range M, (u i - u (i + 1)) := sum_le_sum fun i _ => hdiff i
      _ ≤ u 0 := by rw [sum_range_sub']; linarith [hu M]
  have hmono : Antitone u := antitone_nat_of_succ_le fun i => by
    linarith [hdiff i, mul_nonneg hε.le (hv i)]
  have hlow : BddBelow (Set.range u) := ⟨0, fun _ ⟨i, hi⟩ => hi ▸ hu i⟩
  -- A positive limit would give a summable upper bound for the harmonic series.
  have hinf : (⨅ i, u i) = 0 := by
    refine le_antisymm ?_ (le_ciInf hu)
    by_contra! hpos
    have hh : Summable (fun i : ℕ => (⨅ j, u j) / ((i + N : ℕ) + (b : ℝ) + 1)) :=
      hs.of_nonneg_of_le
        (fun i => by positivity) (fun i => div_le_div_of_nonneg_right (ciInf_le hlow i)
        (by positivity))
    have hh' := hh.mul_left (⨅ j, u j)⁻¹
    apply Real.not_summable_natCast_inv
    apply (summable_nat_add_iff (N + b + 1)).mp
    simpa [Nat.cast_add, ← add_assoc, div_eq_mul_inv, ← mul_assoc, hpos.ne'] using hh'
  refine ⟨ε, hε, (tendsto_add_atTop_iff_nat N).mp ?_, (summable_nat_add_iff N).mp hs⟩
  simpa [hinf] using tendsto_atTop_ciInf hmono hlow

private lemma boundary_convergence (z : ℂ) (b d : ℕ) (hz : z.re < b + 1) :
    Tendsto (fun n => boundary z b n d) atTop (𝓝 0) ∧
      Summable fun n : ℕ => boundary z b n d / (n + b + 1) := by
  obtain ⟨ε, hε, hlim, hsum⟩ := majorant_convergence z b hz
  have hbound (n : ℕ) : ‖boundary z b n d‖ ≤ majorant z b ε n / ε ^ d :=
    (le_div_iff₀ (pow_pos hε d)).mpr (boundary_bound z b hε n d)
  refine ⟨squeeze_zero_norm hbound (by simpa using hlim.div_const (ε ^ d)), ?_⟩
  apply (hsum.div_const (ε ^ d)).of_norm_bounded
  intro n
  have hn : ‖(n : ℂ) + b + 1‖ = (n : ℝ) + b + 1 := by norm_cast
  rw [norm_div, hn, div_right_comm]
  exact div_le_div_of_nonneg_right (hbound n) (by positivity)

-- After summing the difference, the value at depth d + 1 is the previous
-- value divided by b + 1 - z.
private lemma boundary_hasSum (z : ℂ) (b d : ℕ) (hz : z.re < b + 1) :
    HasSum (fun n : ℕ => boundary z b n d / (n + b + 1)) (1 / (b + 1 - z) ^ (d + 1)) := by
  let D : ℂ := b + 1 - z
  have hD : D ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp [D] at this
    linarith
  let f (j n : ℕ) := boundary z b n j / (n + b + 1)
  have hsum (j : ℕ) := (boundary_convergence z b j hz).2.hasSum
  have step (j n : ℕ) :
      D * f j n - (if j = 0 then 0 else f (j - 1) n) =
        boundary z b n j - boundary z b (n + 1) j := by
    rw [boundary_step]
    have hn : (n : ℂ) + b + 1 ≠ 0 := by norm_cast
    dsimp only [D, f]
    split_ifs <;> field_simp <;> ring
  have eval (j : ℕ) (v : ℂ)
      (hv : HasSum (fun n : ℕ => if j = 0 then 0 else f (j - 1) n) v) :
      D * (∑' n, f j n) - v = boundary z b 0 j := by
    have hs := ((hsum j).mul_left D).sub hv
    have ht := hs.tendsto_sum_nat
    change Tendsto (fun m => ∑ n ∈ range m, (D * f j n - _)) _ _ at ht
    simp_rw [step, sum_range_sub'] at ht
    have hl := tendsto_const_nhds (x := boundary z b 0 j) |>.sub (boundary_convergence z b j hz).1
    exact tendsto_nhds_unique ht (by simpa using hl)
  change HasSum (f d) (1 / D ^ (d + 1))
  refine (hsum d).summable.hasSum_iff.mpr ?_
  change ∑' n, f d n = 1 / D ^ (d + 1)
  induction d with
  | zero =>
    have h := eval 0 0 (by simp [hasSum_zero])
    simpa only [zero_add, pow_one] using (eq_div_iff hD).mpr (by
      simpa [mul_comm, boundary, rising, Nat.factorial_ne_zero] using h :
        (∑' n, f 0 n) * D = 1)
  | succ d ih =>
    have h := eval (d + 1) (∑' n, f d n) (by simpa using hsum d)
    rw [ih] at h
    simp [boundary, rising, Polynomial.coeff_one] at h
    rw [pow_succ _ (d + 1), ← div_div, eq_div_iff hD]
    linear_combination h

private noncomputable def moment (z : ℂ) (b d n : ℕ) : ℂ :=
  (rising z (n + d)).coeff d / (n + d + b + 1).factorial

private lemma moment_hasSum (z : ℂ) (b d : ℕ) (hz : z.re < b + 1) :
    HasSum (moment z b d) (1 / (b.factorial * (b + 1 - z) ^ (d + 1))) := by
  let g (n : ℕ) := (rising z n).coeff d / (n + b + 1).factorial
  have heq (n : ℕ) : boundary z b n d / (n + b + 1) / b.factorial = g n := by
    simp [boundary, g, Nat.factorial_succ, div_eq_mul_inv, mul_inv_rev,
      Nat.factorial_ne_zero, mul_assoc, mul_left_comm, mul_comm]
  have hs := (boundary_hasSum z b d hz).div_const (b.factorial : ℂ)
  simp_rw [heq] at hs
  have hinit : ∑ n ∈ range d, g n = 0 := by
    apply sum_eq_zero
    intro n hn
    have h := harmonic_eq_coeff z n d
    rw [generalizedHyperharmonic_of_lt (mem_range.mp hn)] at h
    have hc := (div_eq_zero_iff.mp h.symm).resolve_right (by exact_mod_cast n.factorial_ne_zero)
    simp [g, hc]
  have htail := (hasSum_nat_add_iff' d).mpr hs
  unfold moment
  simpa only [hinit, sub_zero, g, div_div, mul_comm ((b + 1 - z) ^ (d + 1))] using htail

private lemma factorial_bound (c n m : ℕ) :
    (c + n).factorial * (c + m).factorial ≤ c.factorial * (c + m + n).factorial := by
  rw [← Nat.factorial_mul_ascFactorial c n, ← Nat.factorial_mul_ascFactorial (c + m) n,
    mul_right_comm, ← mul_assoc]
  exact Nat.mul_le_mul_left _ (Nat.ascFactorial_le n (by omega))

private noncomputable def kernel (k p : ℕ) (r t : ℂ) (n m : ℕ) : ℂ :=
  (rising r (n + k)).coeff k * (rising t (m + p)).coeff p /
    (n + k + (m + p) + 1).factorial

private lemma kernel_summable (k p : ℕ) (r t : ℂ) (hr : r.re < p + 1) (ht : t.re < k + 1) :
    Summable (Function.uncurry (kernel k p r t)) := by
  let c := k + p + 1
  have hs := (moment_hasSum r p k hr).summable.norm.mul_norm
    (moment_hasSum t k p ht).summable.norm
  apply (hs.mul_right (c.factorial : ℝ)).of_norm_bounded
  rintro ⟨n, m⟩
  simp only [Function.uncurry_apply_pair, kernel, moment, norm_div, norm_mul, Complex.norm_natCast]
  -- Separate the two indices by bounding the reciprocal factorial by a product.
  have hfac : ((n + k + p + 1).factorial : ℝ) * (m + p + k + 1).factorial ≤
      c.factorial * (n + k + (m + p) + 1).factorial := by
    have h := factorial_bound c n m
    dsimp only [c] at h ⊢
    exact_mod_cast (by simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h :
      (n + k + p + 1).factorial * (m + p + k + 1).factorial ≤
        (k + p + 1).factorial * (n + k + (m + p) + 1).factorial)
  have h : 1 / ((n + k + (m + p) + 1).factorial : ℝ) ≤
      c.factorial / ((n + k + p + 1).factorial * (m + p + k + 1).factorial : ℝ) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    simpa using hfac
  calc
    _ = (‖(rising r (n + k)).coeff k‖ * ‖(rising t (m + p)).coeff p‖) *
        (1 / ((n + k + (m + p) + 1).factorial : ℝ)) := by ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left h (by positivity)).trans_eq (by ring)

private lemma kernel_row (k p : ℕ) (r t : ℂ) (ht : t.re < k + 1) (n : ℕ) :
    HasSum (kernel k p r t n)
      (generalizedHyperharmonic (n + k) k r / (((n + k : ℕ) : ℂ) + (1 - t)) ^ ((p : ℤ) + 1)) := by
  have ht' : t.re < (n + k : ℕ) + (1 : ℝ) := by push_cast; linarith
  have hs := (moment_hasSum t (n + k) p ht').mul_left ((rising r (n + k)).coeff k)
  simp only [moment, ← mul_div_assoc] at hs
  rw [harmonic_eq_coeff, ← Int.natCast_succ, zpow_natCast, div_div]
  convert hs using 2 with m
  · simp only [kernel, Nat.add_comm (m + p) (n + k)]
  · simp
  · rw [add_sub_assoc]

end hyperharmonicEulerSum_duality

open hyperharmonicEulerSum_duality in
/-- **Duality for hyperharmonic Euler sums.** Let $k, p \ge 0$ be integers and let $r, t$ be
complex numbers with $\operatorname{Re}(r) < p + 1$ and $\operatorname{Re}(t) < k + 1$. Write
$H_n^{[r]}(k)$ for the generalized hyperharmonic number. Then the series
$S(k, r; p + 1; 1 - t) = \sum_{n \ge k} H_n^{[r]}(k) / (n + 1 - t)^{p+1}$ and
$S(p, t; k + 1; 1 - r) = \sum_{n \ge p} H_n^{[t]}(p) / (n + 1 - r)^{k+1}$ both converge absolutely,
and $S(k, r; p + 1; 1 - t) = S(p, t; k + 1; 1 - r)$.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Corollary 1 (`integers-2026-A81-cor-1`). -/
theorem hyperharmonicEulerSum_duality (k p : ℕ) (r t : ℂ) (hr : r.re < p + 1)
    (ht : t.re < k + 1) :
    Summable (fun n : ℕ =>
        generalizedHyperharmonic (n + k) k r / (((n + k : ℕ) : ℂ) + (1 - t)) ^ ((p : ℤ) + 1)) ∧
      Summable (fun n : ℕ =>
        generalizedHyperharmonic (n + p) p t / (((n + p : ℕ) : ℂ) + (1 - r)) ^ ((k : ℤ) + 1)) ∧
      hyperharmonicEulerSum k r (p + 1) (1 - t) = hyperharmonicEulerSum p t (k + 1) (1 - r) := by
  have hs := (kernel_summable k p r t hr ht).hasSum
  have hrow := hs.prod_fiberwise (kernel_row k p r t ht)
  have hcol := ((Equiv.prodComm ℕ ℕ).hasSum_iff.mpr hs).prod_fiberwise (g := fun m =>
    generalizedHyperharmonic (m + p) p t / (((m + p : ℕ) : ℂ) + (1 - r)) ^ ((k : ℤ) + 1)) (by
      intro m
      have h := kernel_row p k t r hr m
      unfold kernel at h
      simpa only [Function.comp_def, Equiv.prodComm_apply, Function.uncurry_apply_pair,
        Prod.swap_prod_mk, kernel, mul_comm, Nat.add_comm (m + p)] using h)
  exact ⟨hrow.summable, hcol.summable, hrow.tsum_eq.trans hcol.tsum_eq.symm⟩

end

end MetaMathlibExt
