/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.NumberTheory.Bernoulli

namespace MetaMathlibExt

@[expose] public section

open scoped BigOperators

/--
**Generalized Watson trigonometric sum.** For natural numbers $n$ and $\nu$, $C_n(\nu)$ is the real
number
$$
C_n(\nu) = \sum_{l=1}^{n-1} \frac{\cos(2\pi\nu l/n)}{\sin(\pi l/n)}.
$$
For $n \le 1$ the sum is empty and $C_n(\nu) = 0$.

Source: Iaroslav V. Blagouchine, *On a Generalization of Watson’s Trigonometric Sum (On Dowker’s Sum
of Order One Half)*, INTEGERS 25 (2025), Article A30, definition of `C_n(ν)`.
-/
public noncomputable def watsonCosSum (n ν : ℕ) : ℝ :=
  ∑ l ∈ Finset.Icc 1 (n - 1),
    Real.cos (2 * Real.pi * (ν : ℝ) * (l : ℝ) / (n : ℝ)) *
      (1 / Real.sin (Real.pi * (l : ℝ) / (n : ℝ)))

/--
**Watson's alternating cosecant sum.** For a natural number $n$, the alternating cosecant sum is
the real number
$$
C_n = \sum_{l=1}^{n-1} \frac{(-1)^{l+1}}{\sin(\pi l / n)}.
$$
For $n \le 1$ the sum is empty and $C_n = 0$.

Source: Iaroslav V. Blagouchine, *On a Generalization of Watson’s Trigonometric Sum (On Dowker’s Sum
of Order One Half)*, INTEGERS 25 (2025), Article A30, definition of `C_n`.
-/
public noncomputable def watsonAlternatingCosecantSum (n : ℕ) : ℝ :=
  ∑ l ∈ Finset.Icc 1 (n - 1),
    (-1 : ℝ) ^ (l + 1) * (1 / Real.sin (Real.pi * (l : ℝ) / (n : ℝ)))

/--
**Watson's cosine sum at $n = 2$, $\nu = 1$.** The cosine sum
$C_n(\nu) = \sum_{l=1}^{n-1} \cos(2 \pi \nu l / n) / \sin(\pi l / n)$ satisfies $C_2(1) = -1$.

Source: Iaroslav V. Blagouchine, *On a Generalization of Watson’s Trigonometric Sum (On Dowker’s Sum
of Order One Half)*, INTEGERS 25 (2025), Article A30, definition of `C_n(ν)`.
-/
public theorem watsonCosSum_two_one : watsonCosSum 2 1 = -1 := by
  norm_num [watsonCosSum, Real.sin_pi_div_two]

/--
**Watson's alternating cosecant sum at $n = 2$.** The alternating cosecant sum
$C_2 = \sum_{l=1}^{1} (-1)^{l+1} / \sin(\pi l / 2)$ equals $1$.

Source: Iaroslav V. Blagouchine, *On a Generalization of Watson’s Trigonometric Sum (On Dowker’s Sum
of Order One Half)*, INTEGERS 25 (2025), Article A30, definition of `C_n`.
-/
public theorem watsonAlternatingCosecantSum_two : watsonAlternatingCosecantSum 2 = 1 := by
  norm_num [watsonAlternatingCosecantSum, Real.sin_pi_div_two]

/--
**Watson's alternating cosecant sum vanishes for odd $n$.** For every odd natural number $n$,
$$
\sum_{l=1}^{n-1} \frac{(-1)^{l+1}}{\sin(\pi l / n)} = 0.
$$

Source: Iaroslav V. Blagouchine, *On a Generalization of Watson’s Trigonometric Sum (On Dowker’s Sum
of Order One Half)*, INTEGERS 25 (2025), Article A30, Corollary 2 and Theorem 6.
-/
public theorem watson_alternating_odd_zero (n : ℕ) (hn : Odd n) :
    watsonAlternatingCosecantSum n = 0 := by
  have hnodd := Nat.odd_iff.mp hn
  unfold watsonAlternatingCosecantSum
  apply Finset.sum_involution (fun l _ => n - l)
  · intro l hl
    obtain ⟨hl₁, hl₂⟩ := Finset.mem_Icc.mp hl
    have hle : l ≤ n := by omega
    have hn₀ : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have hangle : Real.pi * ((n - l : ℕ) : ℝ) / n = Real.pi - Real.pi * l / n := by
      rw [Nat.cast_sub hle]
      field_simp
    have hsign : (-1 : ℝ) ^ (n - l + 1) = (-1) ^ l := by
      apply neg_one_pow_congr
      simp only [Nat.even_iff]
      omega
    rw [hangle, Real.sin_pi_sub, hsign, pow_succ]
    ring
  · intro l hl _
    have := Finset.mem_Icc.mp hl
    omega
  · intro l hl
    have := Finset.mem_Icc.mp hl
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro l hl
    have := Finset.mem_Icc.mp hl
    omega

/--
**Odd cotangent derivatives.** For natural numbers $r$, $n$ and $\nu$, $\mathcal{H}_{2r-1}(\nu/n)$
is the real number $\cot^{(2r-1)}(\pi\nu/n)$, the $(2r-1)$st derivative of the cotangent function
evaluated at $\pi\nu/n$. Here $2r - 1$ is computed in the natural numbers, so for $r = 0$ this is
$\cot(\pi\nu/n)$ itself.

The derivative is taken of the cotangent as a function on all of $\mathbb{R}$; the value is the
classical one whenever $\pi\nu/n$ is not a multiple of $\pi$.

Source: Iaroslav V. Blagouchine, *On a Generalization of Watson’s Trigonometric Sum (On Dowker’s Sum
of Order One Half)*, INTEGERS 25 (2025), Article A30, definition of `ℋ_{2r-1}`.
-/
public noncomputable def watsonOddCotangentDeriv (r n ν : ℕ) : ℝ :=
  iteratedDeriv (2 * r - 1) Real.cot (Real.pi * (ν : ℝ) / (n : ℝ))

/--
**Watson expansion terms.** For natural numbers $r$, $n$ and $\nu$, let $B_{2r}$ be the $2r$th
Bernoulli number and let $\mathcal{H}_{2r-1}(\nu/n) = \cot^{(2r-1)}(\pi\nu/n)$ be the
$(2r-1)$st derivative of the cotangent evaluated at $\pi\nu/n$. The $r$th Watson expansion term is
the real number
$$
\Bigl(1 - \frac{1}{2^{2r-1}}\Bigr)
\frac{\pi^{2r-1} B_{2r} \, \mathcal{H}_{2r-1}(\nu/n)}{(2r)! \, n^{2r-1}}.
$$
Here $2r - 1$ is computed in the natural numbers, so for $r = 0$ the factor $1 - 1/2^{2r-1}$ is $0$
and the term vanishes.

Source: Iaroslav V. Blagouchine, *On a Generalization of Watson’s Trigonometric Sum (On Dowker’s Sum
of Order One Half)*, INTEGERS 25 (2025), Article A30, Theorem 3 (printed as Theorem 4).
-/
public noncomputable def watsonExpansionTerm (r n ν : ℕ) : ℝ :=
  (1 - 1 / (2 : ℝ) ^ (2 * r - 1)) * Real.pi ^ (2 * r - 1) *
      (((bernoulli (2 * r) : ℚ) : ℝ)) * watsonOddCotangentDeriv r n ν /
    ((Nat.factorial (2 * r) : ℝ) * (n : ℝ) ^ (2 * r - 1))

/--
**Main part of the asymptotic expansion of Watson's alternating cosecant sum.** For natural numbers
$N$ and $n$, the main part is the real number
$$
M_N(n) = \frac{2 n \log 2}{\pi} + 2 \sum_{r=1}^{N-1}
\frac{(-1)^{r+1} (2^{2r-1} - 1)(2^{2r} - 1) \pi^{2r-1} B_{2r}^2}{r \, (2r)! \, n^{2r-1}},
$$
where $B_{2r}$ is the $2r$-th Bernoulli number. For $N \le 1$ the sum is empty.

Source: Iaroslav V. Blagouchine, *On a Generalization of Watson’s Trigonometric Sum (On Dowker’s Sum
of Order One Half)*, INTEGERS 25 (2025), Article A30, Corollary 2.
-/
public noncomputable def watsonAlternatingMain (N n : ℕ) : ℝ :=
  2 * (n : ℝ) * Real.log 2 / Real.pi +
    2 * (∑ r ∈ Finset.Icc 1 (N - 1),
      (-1 : ℝ) ^ (r + 1) * ((2 : ℝ) ^ (2 * r - 1) - 1) *
          ((2 : ℝ) ^ (2 * r) - 1) * Real.pi ^ (2 * r - 1) *
          (((bernoulli (2 * r) : ℚ) : ℝ) ^ 2) /
        ((r : ℝ) * (Nat.factorial (2 * r) : ℝ) * (n : ℝ) ^ (2 * r - 1)))

end

end MetaMathlibExt
