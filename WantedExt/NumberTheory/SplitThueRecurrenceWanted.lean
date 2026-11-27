/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Split families of Thue equations with linear recurrence factors

Statements from Tobias Hilgart, *On Split Families of Thue Equations with Linear Recurrence
Sequences as Factors*, INTEGERS 25 (2025), Article A35.

The integer sequences `G 1, …, G d` are simple linear recurrences, written through their
closed formulas `G i n = ∑_{r ∈ R i} c i r * r ^ n` (distinct complex roots, nonzero
coefficients). `γ i` is the dominant root of `G i` (real and nonnegative, as the paper
assumes), and `δ (d - 1)`, `δ d` are the second dominant roots of `G (d - 1)`, `G d`.

The roots `α⁽ⁱ⁾ = α n i` of `fₙ(x, 1) = ∏ (x - G k n) - 1` are labelled as in the paper,
`α⁽ⁱ⁾` being the root close to `G i n`: an admissible labelling is any `α : ℕ → ℕ → ℝ`
such that, for all large `n`, every `α n i` is a root with `|α n i - G i n| < 1` (for large
`n` this determines the labelling, since the `G i n` are far apart).
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Split Thue recurrence family.** Let $d \in \mathbb{N}$, let $G_i(n)$ be integers for
$i, n \in \mathbb{N}$, and let $\gamma_i \in \mathbb{R}$ and $\delta_i \in \mathbb{C}$ for
$i \in \mathbb{N}$. Then $(d, G, \gamma, \delta)$ is a split Thue recurrence family when $d \ge 3$
and there are finite sets $R_i \subseteq \mathbb{C}$ and complex numbers $c_i(r)$
($i \in \mathbb{N}$, $r \in \mathbb{C}$) such that: for every $1 \le i \le d$, $c_i(r) \ne 0$
for all $r \in R_i$, $G_i(n) = \sum_{r \in R_i} c_i(r) r^n$ for all $n$, $\gamma_i \in R_i$,
and $|r| < \gamma_i$ for all $r \in R_i$ with $r \ne \gamma_i$; $\gamma_1 \ge 0$, $\gamma$ is
strictly increasing on $\{1, \dots, d - 1\}$, and $\gamma_{d-1} = \gamma_d$;
$c_{d-1}(\gamma_{d-1}) = c_d(\gamma_d)$; for $i \in \{d - 1, d\}$, $\delta_i \in R_i$,
$\delta_i \ne \gamma_i$, and $|r| < |\delta_i|$ for all $r \in R_i$ other than $\gamma_i$ and
$\delta_i$; and $|\delta_{d-1}| < |\delta_d| < \gamma_{d-2}$ and
$\gamma_{d-2}^2 < \gamma_d |\delta_d|$.

In words: each $G_i$ is a simple linear recurrence with dominant root $\gamma_i$, the sequences
$G_{d-1}$ and $G_d$ share their dominant root and its coefficient, and $\delta_{d-1}$, $\delta_d$
are their second dominant roots.

Source: Tobias Hilgart, *On Split Families of Thue Equations with Linear Recurrence Sequences as
Factors*, INTEGERS 25 (2025), Article A35, Theorem 1 (conditions 1-3); dominant roots taken real and
nonnegative as in
the paper's standing assumption after Corollary 1. -/
public def IsSplitThueRecurrenceFamily (d : ℕ) (G : ℕ → ℕ → ℤ) (γ : ℕ → ℝ) (δ : ℕ → ℂ) :
    Prop :=
  3 ≤ d ∧ ∃ (R : ℕ → Finset ℂ) (c : ℕ → ℂ → ℂ),
    (∀ i ∈ Finset.Icc 1 d, (∀ r ∈ R i, c i r ≠ 0) ∧
      ∀ n, (G i n : ℂ) = ∑ r ∈ R i, c i r * r ^ n) ∧
    (∀ i ∈ Finset.Icc 1 d, ((γ i : ℝ) : ℂ) ∈ R i ∧ ∀ r ∈ R i, r ≠ γ i → ‖r‖ < γ i) ∧
    0 ≤ γ 1 ∧ StrictMonoOn γ (Set.Icc 1 (d - 1)) ∧ γ (d - 1) = γ d ∧
    c (d - 1) (γ (d - 1)) = c d (γ d) ∧
    (∀ i ∈ ({d - 1, d} : Finset ℕ), δ i ∈ R i ∧ δ i ≠ γ i ∧
      ∀ r ∈ R i, r ≠ γ i → r ≠ δ i → ‖r‖ < ‖δ i‖) ∧
    ‖δ (d - 1)‖ < ‖δ d‖ ∧ ‖δ d‖ < γ (d - 2) ∧ γ (d - 2) ^ 2 < γ d * ‖δ d‖

/-- **A split Thue recurrence family has at least three sequences.** If $(d, G, \gamma, \delta)$
is a split Thue recurrence family, then $d \ge 3$.

Source: Tobias Hilgart, *On Split Families of Thue Equations with Linear Recurrence Sequences as
Factors*, INTEGERS 25 (2025), Article A35, Theorem 1 (the conditions mention `γ (d - 2)`). -/
public theorem IsSplitThueRecurrenceFamily.three_le {d : ℕ} {G : ℕ → ℕ → ℤ} {γ : ℕ → ℝ}
    {δ : ℕ → ℂ} (h : IsSplitThueRecurrenceFamily d G γ δ) : 3 ≤ d :=
  h.1

/-- **Example of a split Thue recurrence family.** Let $G_1(n) = 3^n$, $G_2(n) = 5^n + 1$ and
$G_i(n) = 5^n + 2^n$ for $i \notin \{1, 2\}$; let $\gamma_1 = 3$ and $\gamma_i = 5$ for
$i \ne 1$; and let $\delta_2 = 1$ and $\delta_i = 2$ for $i \ne 2$. Then $(3, G, \gamma, \delta)$
is a split Thue recurrence family: the dominant roots of $G_1, G_2, G_3$ are $3, 5, 5$ and the
second dominant roots of $G_2, G_3$ are $1, 2$.

Source: Tobias Hilgart, *On Split Families of Thue Equations with Linear Recurrence Sequences as
Factors*, INTEGERS 25 (2025), Article A35, Theorem 1 (conditions 1-3). -/
public theorem isSplitThueRecurrenceFamily_example :
    IsSplitThueRecurrenceFamily 3
      (fun i n => if i = 1 then 3 ^ n else if i = 2 then 5 ^ n + 1 else 5 ^ n + 2 ^ n)
      (fun i => if i = 1 then 3 else 5) (fun i => if i = 2 then 1 else 2) := by
  refine ⟨le_rfl, fun i => if i = 1 then {3} else if i = 2 then {5, 1} else {5, 2},
    fun _ _ => 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have : i = 1 ∨ i = 2 ∨ i = 3 := by simp only [Finset.mem_Icc] at hi; omega
    rcases this with rfl | rfl | rfl <;> refine ⟨fun _ _ => one_ne_zero, fun n => ?_⟩ <;>
      norm_num [Finset.sum_pair]
  · intro i hi
    have : i = 1 ∨ i = 2 ∨ i = 3 := by simp only [Finset.mem_Icc] at hi; omega
    rcases this with rfl | rfl | rfl <;> norm_num
  · norm_num
  · intro a ha b hb hab
    simp only [Set.mem_Icc] at ha hb
    obtain ⟨rfl, rfl⟩ : a = 1 ∧ b = 2 := by omega
    norm_num
  · norm_num
  · norm_num
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> norm_num
  · norm_num
  · norm_num
  · norm_num

/-- **Hilgart's theorem on split families of Thue equations.** Let $(d, G, \gamma, \delta)$ be a
split Thue recurrence family. Then there is $\kappa \in \mathbb{R}$ such that for every
$n \in \mathbb{N}$ and all integers $x, y$ with $|y| \ge 2$ and
$$(x - G_1(n) y) \cdots (x - G_d(n) y) - y^d = \pm 1$$
we have $\log |x| \le \kappa$, $\log |y| \le \kappa$ and $n \le \kappa$ (where $\log 0 = 0$).

Source: Tobias Hilgart, *On Split Families of Thue Equations with Linear Recurrence Sequences as
Factors*, INTEGERS 25 (2025), Article A35, Theorem 1 (`integers-2025-A35-thm-1`). The computability
of `κ` is not
recorded. -/
public theorem_wanted splitThue_recurrence_solutions_bounded {d : ℕ} {G : ℕ → ℕ → ℤ}
    {γ : ℕ → ℝ} {δ : ℕ → ℂ} (hF : IsSplitThueRecurrenceFamily d G γ δ) :
    ∃ κ : ℝ, ∀ (n : ℕ) (x y : ℤ), 2 ≤ |y| →
      ((∏ i ∈ Finset.Icc 1 d, (x - G i n * y)) - y ^ d = 1 ∨
        (∏ i ∈ Finset.Icc 1 d, (x - G i n * y)) - y ^ d = -1) →
      Real.log |(x : ℝ)| ≤ κ ∧ Real.log |(y : ℝ)| ≤ κ ∧ (n : ℝ) ≤ κ

/-- **Split Thue families eventually have only trivial solutions.** Let $(d, G, \gamma, \delta)$
be a split Thue recurrence family. Then there is $n_0$ such that for every $n \ge n_0$ and all
integers $x, y$,
$$(x - G_1(n) y) \cdots (x - G_d(n) y) - y^d = \pm 1$$
holds if and only if $(x, y) = (\pm 1, 0)$ or, for some $1 \le i \le d$,
$(x, y) = (G_i(n), 1)$ or $(x, y) = (-G_i(n), -1)$.

Source: Tobias Hilgart, *On Split Families of Thue Equations with Linear Recurrence Sequences as
Factors*, INTEGERS 25 (2025), Article A35, Corollary 1 (`integers-2025-A35-cor-1`). The
computability of `n₀` is not
recorded. -/
public theorem_wanted splitThue_recurrence_solutions_eventually_trivial {d : ℕ}
    {G : ℕ → ℕ → ℤ} {γ : ℕ → ℝ} {δ : ℕ → ℂ} (hF : IsSplitThueRecurrenceFamily d G γ δ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ x y : ℤ,
      ((∏ i ∈ Finset.Icc 1 d, (x - G i n * y)) - y ^ d = 1 ∨
        (∏ i ∈ Finset.Icc 1 d, (x - G i n * y)) - y ^ d = -1) ↔
      ((x = 1 ∨ x = -1) ∧ y = 0) ∨
        ∃ i ∈ Finset.Icc 1 d, (x = G i n ∧ y = 1) ∨ (x = -G i n ∧ y = -1)

/-- **Asymptotics of the roots of a split Thue family.** Let $(d, G, \gamma, \delta)$ be a split
Thue recurrence family. Call reals $\alpha_i(n)$ ($i, n \in \mathbb{N}$) an admissible labelling
if there is $N$ such that for all $n \ge N$ and $1 \le i \le d$,
$\prod_{k=1}^{d} (\alpha_i(n) - G_k(n)) = 1$ and $|\alpha_i(n) - G_i(n)| < 1$. Then, first,
there is $N$ such that for all $n \ge N$ every $z \in \mathbb{C}$ with
$\prod_{k=1}^{d} (z - G_k(n)) = 1$ is real; second, an admissible labelling exists; third, for
every admissible labelling $\alpha$ and every $1 \le i \le d$ there are $C \in \mathbb{R}$ and
$N$ such that for all $n \ge N$
$$|(\alpha_i(n) - G_i(n)) \prod_{k \ne i} (G_i(n) - G_k(n)) - 1| \le C \Gamma_i^{-n},$$
where the product is over $1 \le k \le d$ with $k \ne i$, and
$\Gamma_i = \gamma_i^{i-1} (\prod_{k=i+1}^{d-2} \gamma_k) \gamma_d^2$ if $i \le d - 2$ and
$\Gamma_i = \gamma_d^{d-2} |\delta_d|$ otherwise.

Source: Tobias Hilgart, *On Split Families of Thue Equations with Linear Recurrence Sequences as
Factors*, INTEGERS 25 (2025), Article A35, Lemma 1 (`integers-2025-A35-lem-1`). The `O`-term is
written as
`|(α⁽ⁱ⁾ - G i n) * ∏_{k ≠ i} (G i n - G k n) - 1| ≤ C * γ_ε⁻ⁿ`; `δ d` enters through its
modulus. -/
public theorem_wanted splitThue_recurrence_roots_asymptotic {d : ℕ} {G : ℕ → ℕ → ℤ}
    {γ : ℕ → ℝ} {δ : ℕ → ℂ} (hF : IsSplitThueRecurrenceFamily d G γ δ) :
    (∃ N : ℕ, ∀ n ≥ N, ∀ z : ℂ, ∏ k ∈ Finset.Icc 1 d, (z - G k n) = 1 → z.im = 0) ∧
    (∃ α : ℕ → ℕ → ℝ, ∃ N : ℕ, ∀ n ≥ N, ∀ i ∈ Finset.Icc 1 d,
      ∏ k ∈ Finset.Icc 1 d, (α n i - G k n) = 1 ∧ |α n i - G i n| < 1) ∧
    ∀ α : ℕ → ℕ → ℝ, (∃ N : ℕ, ∀ n ≥ N, ∀ i ∈ Finset.Icc 1 d,
      ∏ k ∈ Finset.Icc 1 d, (α n i - G k n) = 1 ∧ |α n i - G i n| < 1) →
      ∀ i ∈ Finset.Icc 1 d, ∃ (C : ℝ) (N : ℕ), ∀ n ≥ N,
        |(α n i - G i n) * ∏ k ∈ (Finset.Icc 1 d).erase i, ((G i n : ℝ) - G k n) - 1| ≤
          C * ((if i ≤ d - 2 then γ i ^ (i - 1) * (∏ k ∈ Finset.Icc (i + 1) (d - 2), γ k) *
            γ d ^ 2 else γ d ^ (d - 2) * ‖δ d‖)⁻¹) ^ n

/-- **Growth of the roots of a split Thue family.** Let $(d, G, \gamma, \delta)$ be a split Thue
recurrence family, and let $\alpha_i(n)$ ($i, n \in \mathbb{N}$) be reals for which there is $N$
such that for all $n \ge N$ and $1 \le i \le d$, $\prod_{k=1}^{d} (\alpha_i(n) - G_k(n)) = 1$
and $|\alpha_i(n) - G_i(n)| < 1$. Then there are $c > 0$ and $N'$ such that for all $n \ge N'$
and $1 \le i \le d$ we have $|\alpha_i(n)| \ge c \gamma_i^n$, and for every $1 \le j \le d$ with
$j \ne i$ both $|\alpha_i(n) - \alpha_j(n)|$ and $|\alpha_i(n) - G_j(n)|$ are at least
$c |\delta_d|^n$ if $\{i, j\} = \{d - 1, d\}$, and at least $c \max(\gamma_i, \gamma_j)^n$
otherwise.

Source: Tobias Hilgart, *On Split Families of Thue Equations with Linear Recurrence Sequences as
Factors*, INTEGERS 25 (2025), Article A35, Lemma 2 (`integers-2025-A35-lem-2`), including its last
sentence (the same
bounds with `α⁽ʲ⁾` replaced by `G j n`). `Ω` is the paper's lower bound
`|f n| ≥ c * g n` for large `n`. -/
public theorem_wanted splitThue_recurrence_roots_growth {d : ℕ} {G : ℕ → ℕ → ℤ}
    {γ : ℕ → ℝ} {δ : ℕ → ℂ} (hF : IsSplitThueRecurrenceFamily d G γ δ)
    (α : ℕ → ℕ → ℝ) (hα : ∃ N : ℕ, ∀ n ≥ N, ∀ i ∈ Finset.Icc 1 d,
      ∏ k ∈ Finset.Icc 1 d, (α n i - G k n) = 1 ∧ |α n i - G i n| < 1) :
    ∃ c > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ i ∈ Finset.Icc 1 d,
      c * γ i ^ n ≤ |α n i| ∧ ∀ j ∈ Finset.Icc 1 d, j ≠ i →
        (({i, j} : Finset ℕ) = {d - 1, d} →
          c * ‖δ d‖ ^ n ≤ |α n i - α n j| ∧ c * ‖δ d‖ ^ n ≤ |α n i - G j n|) ∧
        (({i, j} : Finset ℕ) ≠ {d - 1, d} →
          c * max (γ i) (γ j) ^ n ≤ |α n i - α n j| ∧
            c * max (γ i) (γ j) ^ n ≤ |α n i - G j n|)

/-- **Determinants of logarithms in a split Thue family.** Let $(d, G, \gamma, \delta)$ be a
split Thue recurrence family, let $\alpha_i(n)$ ($i, n \in \mathbb{N}$) be reals for which there
is $N$ such that for all $n \ge N$ and $1 \le i \le d$,
$\prod_{l=1}^{d} (\alpha_i(n) - G_l(n)) = 1$ and $|\alpha_i(n) - G_i(n)| < 1$, and let
$1 \le k \le d - 1$. Let $B_k(n)$ be the $k \times k$ matrix with entries
$\log |\alpha_i(n) - G_j(n)|$ for $1 \le i, j \le k$, where $\log 0 = 0$. Then there are
$c_1 > 0$, $c_2 > 0$ and $N'$ such that $c_1 n^k \le |\det B_k(n)| \le c_2 n^k$ for all
$n \ge N'$.

Source: Tobias Hilgart, *On Split Families of Thue Equations with Linear Recurrence Sequences as
Factors*, INTEGERS 25 (2025), Article A35, Lemma 3 (`integers-2025-A35-lem-3`). `Real.log` is the
logarithm of the
absolute value; `Θ` is the paper's two-sided bound `c₁ n ^ k ≤ |det B_k| ≤ c₂ n ^ k` for
large `n`. -/
public theorem_wanted splitThue_recurrence_logUnitDet_asymptotic {d : ℕ} {G : ℕ → ℕ → ℤ}
    {γ : ℕ → ℝ} {δ : ℕ → ℂ} (hF : IsSplitThueRecurrenceFamily d G γ δ)
    (α : ℕ → ℕ → ℝ) (hα : ∃ N : ℕ, ∀ n ≥ N, ∀ i ∈ Finset.Icc 1 d,
      ∏ k ∈ Finset.Icc 1 d, (α n i - G k n) = 1 ∧ |α n i - G i n| < 1) (k : ℕ) (hk : 1 ≤ k) (hkd : k
          ≤ d - 1) :
    ∃ c₁ > 0, ∃ c₂ > 0, ∃ N : ℕ, ∀ n ≥ N,
      c₁ * (n : ℝ) ^ k ≤
          |(Matrix.of fun a b : Fin k => Real.log (α n ((a : ℕ) + 1) - G ((b : ℕ) + 1) n)).det| ∧
        |(Matrix.of fun a b : Fin k => Real.log (α n ((a : ℕ) + 1) - G ((b : ℕ) + 1) n)).det| ≤
          c₂ * (n : ℝ) ^ k

end

end MetaMathlibExt
