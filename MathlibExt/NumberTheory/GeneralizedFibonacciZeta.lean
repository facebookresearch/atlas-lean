/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.RingTheory.Binomial
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The ℓ-generalized Fibonacci zeta series

The terms of an ℓ-generalized Fibonacci sequence grow at least geometrically every two steps
when ℓ ≥ 2. Consequently its zeta series converges absolutely on the open right half-plane.

The complex roots of the characteristic polynomial, counted with multiplicity, multiply to
$(-1)^{\ell+1}$. Consequently, when $\ell - 1$ divides $k$ and $q = k/(\ell - 1)$, the points
$-(k + q) + i\pi(2n + q)/\log \alpha$ for even $\ell$ and $-(k + q) + 2\pi i n/\log \alpha$ for odd
$\ell$ belong to the set of possible poles of the ℓ-generalized Fibonacci zeta function.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **ℓ-generalized Fibonacci sequence.** Let $\ell$ be a natural number. A function
$F : \mathbb{Z} \to \mathbb{Z}$ is an $\ell$-generalized Fibonacci sequence when $F(n) = 0$ for
every integer $n$ with $2 - \ell \le n \le 0$, $F(1) = 1$, and
$F(n) = \sum_{i=0}^{\ell-1} F(n-1-i)$ for every integer $n > 1$.

The values of $F$ below $2 - \ell$ are unconstrained, since the sequence is defined only from
that index onward.

Source: Nabin Kumar Meher and Dilip Kumar Sahoo, *Analytic Continuation of the
ℓ-Generalized Fibonacci Zeta Function*, INTEGERS 24 (2024), Article A85, Definition
preceding Proposition 1. -/
public def IsLGeneralizedFibonacci (ℓ : ℕ) (F : ℤ → ℤ) : Prop :=
  (∀ n : ℤ, 2 - (ℓ : ℤ) ≤ n → n < 1 → F n = 0) ∧
    F 1 = 1 ∧
    ∀ n : ℤ, 1 < n →
      F n = ∑ i ∈ Finset.range ℓ, F (n - 1 - (i : ℤ))

/-- **Characteristic polynomial of the ℓ-generalized Fibonacci recurrence.** For a natural number
$\ell$, the characteristic polynomial of the $\ell$-generalized Fibonacci recurrence is the
polynomial $\varphi_\ell(X) = X^\ell - \sum_{i=0}^{\ell-1} X^i$ in $\mathbb{C}[X]$; for
$\ell \ge 2$ this is $X^\ell - X^{\ell-1} - \cdots - X - 1$.

Source: Nabin Kumar Meher and Dilip Kumar Sahoo, *Analytic Continuation of the
ℓ-Generalized Fibonacci Zeta Function*, INTEGERS 24 (2024), Article A85,
Characteristic polynomial definition. -/
public noncomputable def lGeneralizedFibonacciCharacteristic (ℓ : ℕ) : Polynomial ℂ :=
  Polynomial.X ^ ℓ - ∑ i ∈ Finset.range ℓ, Polynomial.X ^ i

/-- **Dresden–Du coefficient.** For a natural number $\ell$ and a complex number $\beta$, the
Dresden–Du coefficient is the complex number
$c(\beta) = \frac{\beta - 1}{2 + (\ell + 1)(\beta - 2)}$, taken to be $0$ when the denominator
vanishes.

Source: Nabin Kumar Meher and Dilip Kumar Sahoo, *Analytic Continuation of the
ℓ-Generalized Fibonacci Zeta Function*, INTEGERS 24 (2024), Article A85,
Coefficient definition preceding Lemma 1. -/
public noncomputable def lGeneralizedFibonacciCoefficient (ℓ : ℕ) (β : ℂ) : ℂ :=
  (β - 1) / (2 + ((ℓ : ℂ) + 1) * (β - 2))

/-- **Other roots of the ℓ-generalized Fibonacci characteristic polynomial.** For a natural number
$\ell$ and a real number $\alpha$, this is the finite set of distinct complex roots of the
characteristic polynomial $\varphi_\ell(X) = X^\ell - \sum_{i=0}^{\ell-1} X^i$ other than $\alpha$.
In applications $\alpha$ is the dominant real root of $\varphi_\ell$.

Each root is listed once, without multiplicity; the roots of $\varphi_\ell$ are in fact simple.

Source: Nabin Kumar Meher and Dilip Kumar Sahoo, *Analytic Continuation of the
ℓ-Generalized Fibonacci Zeta Function*, INTEGERS 24 (2024), Article A85,
Root notation preceding Proposition 1. -/
public noncomputable def lGeneralizedFibonacciOtherRoots (ℓ : ℕ) (α : ℝ) : Finset ℂ :=
  ((lGeneralizedFibonacciCharacteristic ℓ).roots.toFinset).erase (α : ℂ)

/-- **Possible pole of the ℓ-generalized Fibonacci zeta function at a given index.** Let $\ell$
be a natural number, let $\alpha$ be a real number, and let $R$ be the set of complex roots of
$X^\ell - \sum_{i<\ell} X^i$ other than $\alpha$. For a function $\kappa$ from $\mathbb{C}$ to the
natural numbers and an integer $n$, the possible pole indexed by $(\kappa, n)$ is
$$
s_{\kappa,n} = -\sum_{\beta \in R} \kappa(\beta) +
\frac{2 n \pi i + \sum_{\beta \in R} \kappa(\beta) \log \beta}{\log \alpha},
$$
where $\log$ is the principal branch of the complex logarithm.

Only the values of $\kappa$ on $R$ enter; their sum is the number called $k$ in the paper.

Source: Nabin Kumar Meher and Dilip Kumar Sahoo, *Analytic Continuation of the
ℓ-Generalized Fibonacci Zeta Function*, INTEGERS 24 (2024), Article A85, Theorem 1. -/
public noncomputable def lGeneralizedFibonacciZetaPole
    (ℓ : ℕ) (α : ℝ) (κ : ℂ → ℕ) (n : ℤ) : ℂ :=
  -((∑ β ∈ lGeneralizedFibonacciOtherRoots ℓ α, κ β : ℕ) : ℂ) +
    (2 * (n : ℂ) * (Real.pi : ℂ) * Complex.I +
        ∑ β ∈ lGeneralizedFibonacciOtherRoots ℓ α, (κ β : ℂ) * Complex.log β) /
      Complex.log (α : ℂ)

/-- **The ℓ-generalized Fibonacci characteristic polynomial for ℓ = 2.** For $\ell = 2$ the
characteristic polynomial $\varphi_2$ of the $\ell$-generalized Fibonacci recurrence is the
Fibonacci polynomial $X^2 - X - 1$ in $\mathbb{C}[X]$.

Source: Nabin Kumar Meher and Dilip Kumar Sahoo, *Analytic Continuation of the
ℓ-Generalized Fibonacci Zeta Function*, INTEGERS 24 (2024), Article A85, Equation (3). -/
public theorem lGeneralizedFibonacciCharacteristic_two :
    lGeneralizedFibonacciCharacteristic 2 = Polynomial.X ^ 2 - Polynomial.X - 1 := by
  simp [lGeneralizedFibonacciCharacteristic, Finset.sum_range_succ]
  ring

/-- **The possible pole at the zero index is zero.** For every natural number $\ell$ and every
real number $\alpha$, the possible pole $s_{\kappa,n}$ of the $\ell$-generalized Fibonacci zeta
function indexed by the identically zero function $\kappa$ and $n = 0$ equals $0$.

Source: Nabin Kumar Meher and Dilip Kumar Sahoo, *Analytic Continuation of the
ℓ-Generalized Fibonacci Zeta Function*, INTEGERS 24 (2024), Article A85, Theorem 1. -/
public theorem lGeneralizedFibonacciZetaPole_zero (ℓ : ℕ) (α : ℝ) :
    lGeneralizedFibonacciZetaPole ℓ α (fun _ => 0) 0 = 0 := by
  simp [lGeneralizedFibonacciZetaPole]

/-- **Set of possible poles of the ℓ-generalized Fibonacci zeta function.** For a natural number
$\ell$ and a real number $\alpha$, let $R$ be the set of distinct complex roots of the
characteristic polynomial $X^\ell - \sum_{i=0}^{\ell-1} X^i$ other than $\alpha$. The set $S$ of
possible poles is the set of all complex numbers $-K + (2n\pi i + L)/\log\alpha$, where $n$ is
an integer, $(\kappa_\beta)_{\beta \in R}$ is a family of natural numbers,
$K = \sum_{\beta \in R} \kappa_\beta$ and $L = \sum_{\beta \in R} \kappa_\beta \log \beta$. Here
$\log$ is the principal complex logarithm.

Source: Nabin Kumar Meher and Dilip Kumar Sahoo, *Analytic Continuation of the
ℓ-Generalized Fibonacci Zeta Function*, INTEGERS 24 (2024), Article A85, Theorem 1. -/
public noncomputable def lGeneralizedFibonacciZetaPoleSet (ℓ : ℕ) (α : ℝ) : Set ℂ :=
  {s | ∃ (κ : ℂ → ℕ) (n : ℤ), s = lGeneralizedFibonacciZetaPole ℓ α κ n}

/-- **Residue expression of the ℓ-generalized Fibonacci zeta function.** Let $\ell$ be a natural
number, let $\alpha$ be a real number, let $R$ be the set of complex roots of
$X^\ell - \sum_{i<\ell} X^i$ other than $\alpha$, let
$c(\beta) = (\beta - 1)/(2 + (\ell + 1)(\beta - 2))$ be the Dresden–Du coefficient, and put
$d = c(\alpha)/\alpha$. For a function $\kappa$ from $\mathbb{C}$ to the natural numbers and an
integer $n$, let $k = \sum_{\beta \in R} \kappa(\beta)$ and let $s_0$ be the possible pole
indexed by $(\kappa, n)$. The residue expression indexed by $(\kappa, n)$ is
$$
\rho_{\kappa,n} = d^{-s_0} \binom{-s_0}{k} d^{-k} \cdot
\frac{k!}{\prod_{\beta \in R} \kappa(\beta)!} \cdot
\prod_{\beta \in R} \left(\frac{c(\beta)}{\beta}\right)^{\kappa(\beta)} \cdot
\frac{1}{\log \alpha},
$$
where $\binom{-s_0}{k} = (-s_0)(-s_0 - 1)\cdots(-s_0 - k + 1)/k!$ is the generalized binomial
coefficient, $d^{-s_0}$ and $d^{-k}$ are principal complex powers, and $\log$ is the principal
branch of the complex logarithm.

Source: Nabin Kumar Meher and Dilip Kumar Sahoo, *Analytic Continuation of the
ℓ-Generalized Fibonacci Zeta Function*, INTEGERS 24 (2024), Article A85, Theorem 1. -/
public noncomputable def lGeneralizedFibonacciZetaResidue
    (ℓ : ℕ) (α : ℝ) (κ : ℂ → ℕ) (n : ℤ) : ℂ :=
  let roots := lGeneralizedFibonacciOtherRoots ℓ α
  let k := (∑ β ∈ roots, κ β)
  let s₀ := lGeneralizedFibonacciZetaPole ℓ α κ n
  let dominant :=
    lGeneralizedFibonacciCoefficient ℓ (α : ℂ) * (α : ℂ)⁻¹
  dominant ^ (-s₀) *
    Ring.choose (-s₀) k *
    dominant ^ (-(k : ℂ)) *
    ((Nat.factorial k : ℂ) /
      ∏ β ∈ roots, (Nat.factorial (κ β) : ℂ)) *
    (∏ β ∈ roots,
      (lGeneralizedFibonacciCoefficient ℓ β * β⁻¹) ^ κ β) *
    (1 / Complex.log (α : ℂ))

/-- **Corollary pole of the ℓ-generalized Fibonacci zeta function.** For natural numbers $\ell$
and $k$, a real number $\alpha$ and an integer $n$, let $q$ be the quotient of $k$ by $\ell - 1$
in natural-number division, with $q = 0$ when $\ell \le 1$ (so $q = k/(\ell - 1)$ when
$\ell \ge 2$ and $\ell - 1$ divides $k$). The corollary pole is the complex number
$-(k + q) + i\pi(2n + q)/\log \alpha$ if $\ell$ is even and $-(k + q) + 2\pi i n/\log \alpha$ if
$\ell$ is odd, where $\log$ is the principal complex logarithm.

Source: Nabin Kumar Meher and Dilip Kumar Sahoo, *Analytic Continuation of the
ℓ-Generalized Fibonacci Zeta Function*, INTEGERS 24 (2024), Article A85, Corollary 1. -/
public noncomputable def lGeneralizedFibonacciZetaCorollaryPole
    (ℓ k : ℕ) (α : ℝ) (n : ℤ) : ℂ :=
  -((k + k / (ℓ - 1) : ℕ) : ℂ) +
    if Even ℓ then
      Complex.I * (Real.pi : ℂ) *
          ((2 * n + (k / (ℓ - 1) : ℕ) : ℤ) : ℂ) /
        Complex.log (α : ℂ)
    else
      Complex.I * (2 * (n : ℂ) * (Real.pi : ℂ)) /
        Complex.log (α : ℂ)

namespace lGeneralizedFibonacciZeta_summable

variable {ℓ : ℕ} {F : ℤ → ℤ}

private theorem nonneg (hF : IsLGeneralizedFibonacci ℓ F) (n : ℤ)
    (hn : 2 - (ℓ : ℤ) ≤ n) : 0 ≤ F n := by
  obtain hn' | rfl | hn' := lt_trichotomy n 1
  · rw [hF.1 n hn hn']
  · simp [hF.2.1]
  · rw [hF.2.2 n hn']
    refine Finset.sum_nonneg fun i hi => nonneg hF _ ?_
    have := Finset.mem_range.mp hi
    omega
termination_by n.toNat
decreasing_by omega

/-- Keeping the two most recent terms gives a lower bound for the full recurrence. -/
private theorem add_le (hℓ : 2 ≤ ℓ) (hF : IsLGeneralizedFibonacci ℓ F)
    (n : ℤ) (hn : 0 ≤ n) : F (n + 1) + F n ≤ F (n + 2) := by
  rw [hF.2.2 (n + 2) (by omega)]
  calc
    _ = ∑ i ∈ Finset.range 2, F (n + 2 - 1 - (i : ℤ)) := by
      simp [Finset.sum_range_succ, show n + 2 - 1 = n + 1 by omega]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hℓ) fun i hi _ =>
      nonneg hF _ (by
        have := Finset.mem_range.mp hi
        omega)

private theorem pow_le_pair (hℓ : 2 ≤ ℓ) (hF : IsLGeneralizedFibonacci ℓ F) (k : ℕ) :
    (2 : ℤ) ^ k ≤ F (2 * (k : ℤ) + 1) ∧ 2 ^ k ≤ F (2 * (k : ℤ) + 2) := by
  induction k with
  | zero =>
    have h := add_le hℓ hF 0 (le_refl 0)
    simpa [hF.2.1, hF.1 0 (by omega) (by decide)] using h
  | succ k ih =>
    have h₁ := add_le hℓ hF (2 * (k : ℤ) + 1) (by positivity)
    have h₂ := add_le hℓ hF (2 * (k : ℤ) + 2) (by positivity)
    push_cast
    rw [pow_succ]
    ring_nf at h₁ h₂ ih ⊢
    have := pow_nonneg (by decide : (0 : ℤ) ≤ 2) k
    omega

end lGeneralizedFibonacciZeta_summable

/-- **Absolute convergence of the ℓ-generalized Fibonacci zeta series.** Let $\ell \ge 2$ and let
$F$ be an $\ell$-generalized Fibonacci sequence. For every complex number $s$ with
$\operatorname{Re} s > 0$, the series $\sum_{n \ge 1} |F_n^{-s}|$ converges, where $F_n^{-s}$ is
the principal complex power of $F_n$ viewed as a complex number.

Source: Nabin Kumar Meher and Dilip Kumar Sahoo, *Analytic Continuation of the
ℓ-Generalized Fibonacci Zeta Function*, INTEGERS 24 (2024), Article A85, Proposition 1. -/
public theorem lGeneralizedFibonacciZeta_summable
    (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (F : ℤ → ℤ)
    (hF : IsLGeneralizedFibonacci ℓ F) (s : ℂ) (hs : 0 < s.re) :
    Summable (fun j : ℕ => ‖((F ((j : ℤ) + 1) : ℂ) ^ (-s))‖) := by
  have hgeom : Summable (fun k : ℕ => ((2 : ℝ) ^ (-s.re)) ^ k) :=
    summable_geometric_of_lt_one (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_lt_zero.mpr hs))
  have hbound (n : ℤ) (k : ℕ) (hk : (2 : ℤ) ^ k ≤ F n) :
      ‖(F n : ℂ) ^ (-s)‖ ≤ ((2 : ℝ) ^ (-s.re)) ^ k := by
    have hk' : (2 : ℝ) ^ k ≤ (F n : ℝ) := by exact_mod_cast hk
    rw [← Complex.ofReal_intCast, Complex.norm_cpow_eq_rpow_re_of_pos
      (lt_of_lt_of_le (by positivity) hk'), Complex.neg_re, Real.rpow_pow_comm (by norm_num)]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hk' (neg_nonpos.mpr hs.le)
  apply Summable.even_add_odd
  · apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hgeom
    intro k
    simpa using hbound _ k (lGeneralizedFibonacciZeta_summable.pow_le_pair hℓ hF k).1
  · apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hgeom
    intro k
    simpa [add_assoc] using hbound _ k (lGeneralizedFibonacciZeta_summable.pow_le_pair hℓ hF k).2

namespace lGeneralizedFibonacciZeta_corollaryPole_mem

open Polynomial

variable {ℓ : ℕ}

private theorem degree_sum_lt (ℓ : ℕ) : (∑ i ∈ Finset.range ℓ, (X : ℂ[X]) ^ i).degree < ℓ := by
  refine (degree_sum_le _ _).trans_lt ((Finset.sup_lt_iff (WithBot.bot_lt_natCast ℓ)).mpr ?_)
  intro i hi
  rw [degree_X_pow]
  exact_mod_cast Finset.mem_range.mp hi

private theorem monic (ℓ : ℕ) : (lGeneralizedFibonacciCharacteristic ℓ).Monic :=
  monic_X_pow_sub (degree_sum_lt ℓ)

private theorem natDegree_eq (ℓ : ℕ) : (lGeneralizedFibonacciCharacteristic ℓ).natDegree = ℓ := by
  apply natDegree_eq_of_degree_eq_some
  rw [lGeneralizedFibonacciCharacteristic, degree_sub_eq_left_of_degree_lt] <;>
    simp [degree_sum_lt ℓ]

private theorem coeff_zero (hℓ : 0 < ℓ) : (lGeneralizedFibonacciCharacteristic ℓ).coeff 0 = -1 := by
  simp [lGeneralizedFibonacciCharacteristic, coeff_X_pow, hℓ, hℓ.ne]

private theorem card_roots (ℓ : ℕ) : (lGeneralizedFibonacciCharacteristic ℓ).roots.card = ℓ :=
  (splits_iff_card_roots.mp (IsAlgClosed.splits _)).trans (natDegree_eq ℓ)

/-- Vieta's formula: the roots, counted with multiplicity, multiply to `(-1) ^ (ℓ + 1)`. -/
private theorem prod_roots (hℓ : 0 < ℓ) :
    (lGeneralizedFibonacciCharacteristic ℓ).roots.prod = (-1) ^ (ℓ + 1) := by
  have h := (IsAlgClosed.splits _).coeff_zero_eq_prod_roots_of_monic (monic ℓ)
  rw [coeff_zero hℓ, natDegree_eq ℓ] at h
  calc (lGeneralizedFibonacciCharacteristic ℓ).roots.prod
      = ((-1) ^ ℓ * (-1) ^ ℓ) * (lGeneralizedFibonacciCharacteristic ℓ).roots.prod := by
        rw [← pow_add, ← two_mul, pow_mul]
        simp
    _ = (-1) ^ (ℓ + 1) := by rw [mul_assoc, ← h, pow_succ]

private theorem ne_zero_of_mem_roots (hℓ : 0 < ℓ) {β : ℂ}
    (hβ : β ∈ (lGeneralizedFibonacciCharacteristic ℓ).roots) : β ≠ 0 := by
  rintro rfl
  rw [mem_roots (monic ℓ).ne_zero, IsRoot.def, ← coeff_zero_eq_eval_zero, coeff_zero hℓ] at hβ
  norm_num at hβ

private theorem ofReal_mem_roots {α : ℝ} (hαroot : α ^ ℓ = ∑ i ∈ Finset.range ℓ, α ^ i) :
    (α : ℂ) ∈ (lGeneralizedFibonacciCharacteristic ℓ).roots := by
  rw [mem_roots (monic ℓ).ne_zero, IsRoot.def]
  simp only [lGeneralizedFibonacciCharacteristic, eval_sub, eval_pow, eval_X, eval_finsetSum]
  exact_mod_cast sub_eq_zero.mpr hαroot

end lGeneralizedFibonacciZeta_corollaryPole_mem

/-- **Explicit possible poles of the ℓ-generalized Fibonacci zeta function.** Let $\ell \ge 2$, let
$\alpha > 1$ be a real number with $\alpha^\ell = \sum_{i=0}^{\ell-1} \alpha^i$, and let $k$ be a
natural number divisible by $\ell - 1$; write $q = k/(\ell - 1)$. Then for every integer $n$, the
point $-(k + q) + i\pi(2n + q)/\log \alpha$ if $\ell$ is even, and $-(k + q) + 2\pi i n/\log \alpha$
if $\ell$ is odd, belongs to the set $S$ of possible poles of the $\ell$-generalized Fibonacci
zeta function determined by $\ell$ and $\alpha$.

A witnessing exponent tuple takes the constant value $q$ at every root of the characteristic
polynomial other than $\alpha$.

Source: Nabin Kumar Meher and Dilip Kumar Sahoo, *Analytic Continuation of the
ℓ-Generalized Fibonacci Zeta Function*, INTEGERS 24 (2024), Article A85, Corollary 1. -/
public theorem lGeneralizedFibonacciZeta_corollaryPole_mem
    (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (α : ℝ) (hα : 1 < α)
    (hαroot : α ^ ℓ = ∑ i ∈ Finset.range ℓ, α ^ i)
    (k : ℕ) (hk : ℓ - 1 ∣ k) (n : ℤ) :
    lGeneralizedFibonacciZetaCorollaryPole ℓ k α n ∈
      lGeneralizedFibonacciZetaPoleSet ℓ α := by
  have hℓ0 : 0 < ℓ := by omega
  have hkq : k + k / (ℓ - 1) = ℓ * (k / (ℓ - 1)) := by
    obtain ⟨m, rfl⟩ := hk
    rw [Nat.mul_div_cancel_left m (by omega)]
    obtain ⟨j, rfl⟩ : ∃ j, ℓ = j + 1 := ⟨ℓ - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  have hαmem := Multiset.mem_toFinset.mpr
    (lGeneralizedFibonacciZeta_corollaryPole_mem.ofReal_mem_roots hαroot)
  have hcard := lGeneralizedFibonacciZeta_corollaryPole_mem.card_roots ℓ
  have hroots := lGeneralizedFibonacciZeta_corollaryPole_mem.prod_roots hℓ0
  have hne := @lGeneralizedFibonacciZeta_corollaryPole_mem.ne_zero_of_mem_roots ℓ hℓ0
  -- The witness is `q` times the root multiplicity. Since the roots are simple, this is the
  -- constant `q` on the other roots, but the argument below does not need simplicity: with
  -- multiplicities, Vieta's formula applies to the product over the roots directly.
  set P := lGeneralizedFibonacciCharacteristic ℓ
  set q := k / (ℓ - 1) with hq
  set c := P.roots.count (α : ℂ)
  set κ : ℂ → ℕ := fun β => q * P.roots.count β with hκ
  have hR : lGeneralizedFibonacciOtherRoots ℓ α = P.roots.toFinset.erase (α : ℂ) := rfl
  have hK : ∑ β ∈ lGeneralizedFibonacciOtherRoots ℓ α, κ β + q * c = ℓ * q := by
    have h := Finset.add_sum_erase P.roots.toFinset (fun β => P.roots.count β) hαmem
    rw [Multiset.toFinset_sum_count_eq, hcard] at h
    rw [hR, hκ, ← Finset.mul_sum, ← mul_add, add_comm, h, mul_comm]
  have hprod : (∏ β ∈ lGeneralizedFibonacciOtherRoots ℓ α, β ^ P.roots.count β) *
      (α : ℂ) ^ c = (-1) ^ (ℓ + 1) := by
    have h := Finset.mul_prod_erase P.roots.toFinset (fun β => β ^ P.roots.count β) hαmem
    rw [← Finset.prod_multiset_count, hroots] at h
    rw [hR, mul_comm, h]
  have hlog : ∀ β ∈ lGeneralizedFibonacciOtherRoots ℓ α,
      Complex.exp ((κ β : ℂ) * Complex.log β) = (β ^ P.roots.count β) ^ q := by
    intro β hβ
    rw [Complex.exp_nat_mul, Complex.exp_log (hne
      (Multiset.mem_toFinset.mp (Finset.mem_of_mem_erase hβ))), ← pow_mul, mul_comm]
  have hα0 : (α : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have hlogα : Complex.log (α : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_log (by linarith)]
    exact Complex.ofReal_ne_zero.mpr (Real.log_pos hα).ne'
  have hexp : Complex.exp ((∑ β ∈ lGeneralizedFibonacciOtherRoots ℓ α,
        (κ β : ℂ) * Complex.log β) + ((q * c : ℕ) : ℂ) * Complex.log (α : ℂ)) =
      ((-1) ^ (ℓ + 1)) ^ q := by
    rw [Complex.exp_add, Complex.exp_sum, Finset.prod_congr rfl hlog, Complex.exp_nat_mul,
      Complex.exp_log hα0, Finset.prod_pow, pow_mul', ← mul_pow, hprod]
  have hS : ((∑ β ∈ lGeneralizedFibonacciOtherRoots ℓ α, κ β : ℕ) : ℂ) =
      (ℓ : ℂ) * q - q * c := by
    rw [eq_sub_iff_add_eq]
    exact_mod_cast hK
  rcases Nat.even_or_odd ℓ with hev | hodd
  · have h1 : ((-1 : ℂ) ^ (ℓ + 1)) ^ q = Complex.exp (q * (Real.pi * Complex.I)) := by
      rw [Complex.exp_nat_mul, Complex.exp_pi_mul_I, pow_succ, hev.neg_one_pow, one_mul]
    obtain ⟨M, hM⟩ := Complex.exp_eq_exp_iff_exists_int.mp (hexp.trans h1)
    refine ⟨κ, n - M, ?_⟩
    simp only [lGeneralizedFibonacciZetaCorollaryPole, lGeneralizedFibonacciZetaPole, hev,
      ite_true]
    rw [← hq, hkq, hS, eq_sub_of_add_eq hM]
    push_cast
    field_simp
    ring
  · have h1 : ((-1 : ℂ) ^ (ℓ + 1)) ^ q = Complex.exp 0 := by
      rw [Complex.exp_zero, (Nat.even_add_one.mpr (Nat.not_even_iff_odd.mpr hodd)).neg_one_pow,
        one_pow]
    obtain ⟨M, hM⟩ := Complex.exp_eq_exp_iff_exists_int.mp (hexp.trans h1)
    refine ⟨κ, n - M, ?_⟩
    simp only [lGeneralizedFibonacciZetaCorollaryPole, lGeneralizedFibonacciZetaPole,
      Nat.not_even_iff_odd.mpr hodd, ite_false]
    rw [← hq, hkq, hS, eq_sub_of_add_eq hM]
    push_cast
    field_simp
    ring

end

end MetaMathlibExt
