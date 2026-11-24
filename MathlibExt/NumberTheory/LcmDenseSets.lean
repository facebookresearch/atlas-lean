/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Squarefree
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.List.Permutation
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Harmonic sums over products of distinct primes

Let `S` be the harmonic sum over the chosen primes up to `x`.
`MetaMathlibExt.recipSum_primeProductLayer_asymp` compares the harmonic sums over products of
exactly or at most `k` distinct primes with `S ^ k / k!` whenever `k ≤ S / 8`.

Following Tao's proof, draw each prime with probability proportional to its reciprocal.
The sum of squared probabilities controls repeated draws, and the expected logarithm of the
product controls the cutoff. Each admissible squarefree product occurs in exactly `k!` orders.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Truncated logarithm.** For a real number $x$, the truncated logarithm is
$\operatorname{Log} x = \max(\log x, 1)$. Here $\log$ is extended to all reals by $\log 0 = 0$
and $\log x = \log |x|$ for $x < 0$, so the definition is total; the paper uses it only for
$x > 0$.

Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Notation.
-/
public noncomputable def truncLog (x : ℝ) : ℝ :=
  max (Real.log x) 1

/-- **Second iterated truncated logarithm.** For a real number $x$, the second iterated truncated
logarithm is $\operatorname{Log}_2 x = \operatorname{Log}(\operatorname{Log} x)$, where
$\operatorname{Log}$ is the truncated logarithm.

Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Notation.
-/
public noncomputable def truncLog2 (x : ℝ) : ℝ :=
  truncLog (truncLog x)

/-- **Third iterated truncated logarithm.** For real $x$, let
$\operatorname{Log} x = \max(\log x, 1)$ be the truncated logarithm, where $\log$ is the natural
logarithm extended by $\log x = \log |x|$ for $x < 0$ and $\log 0 = 0$, and let
$\operatorname{Log}_2 x = \operatorname{Log}(\operatorname{Log} x)$. The third iterated truncated
logarithm is the function on all of $\mathbb{R}$ given by
$\operatorname{Log}_3 x = \operatorname{Log}(\operatorname{Log}_2 x)$.

Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Notation.
-/
public noncomputable def truncLog3 (x : ℝ) : ℝ :=
  truncLog (truncLog2 x)

/-- **The truncated logarithm is at least one.** For every real number $x$, the truncated
logarithm $\operatorname{Log} x = \max(\log x, 1)$ satisfies $\operatorname{Log} x \ge 1$.

Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Notation.
-/
public theorem one_le_truncLog (x : ℝ) : 1 ≤ truncLog x := by
  exact le_max_right _ _

/-- **Elements of a set up to a bound.** For a set $A$ of natural numbers and a real number $x$,
this is the finite set of positive integers $n \in A$ with $n \le x$; it is empty when $x < 1$.

Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Notation.
-/
public noncomputable def naturalsInSetUpTo (A : Set ℕ) (x : ℝ) : Finset ℕ :=
  open Classical in (Finset.Icc 1 ⌊x⌋₊).filter (fun n => n ∈ A)

/-- **The empty set has no elements up to any bound.** For every real number $x$, the finite set
of elements $n$ of the empty set with $1 \le n \le x$ is empty.

Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Notation.
-/
@[simp] public theorem naturalsInSetUpTo_empty (x : ℝ) :
    naturalsInSetUpTo ∅ x = ∅ := by
  simp [naturalsInSetUpTo]

/-- **Harmonic sum of a set up to a bound.** For a set $A$ of natural numbers and a real number
$x$, this is the finite sum $\sum_{n \in A,\, 1 \le n \le x} 1/n$ of the reciprocals of the
positive integers in $A$ that are at most $x$; it is $0$ when $x < 1$.

The sum starts at $n = 1$, matching the paper's convention that natural numbers are positive.

Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Notation.
-/
public noncomputable def recipSumUpTo (A : Set ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ naturalsInSetUpTo A x, 1 / (n : ℝ)

/-- **The harmonic sum over the empty set vanishes.** For every real number $x$,
$\sum_{n \in \emptyset,\, n \le x} 1/n = 0$.

Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Notation.
-/
@[simp] public theorem recipSumUpTo_empty (x : ℝ) : recipSumUpTo ∅ x = 0 := by
  simp [recipSumUpTo]

/-- **Double sum of reciprocal least common multiples.** For a set $A$ of natural numbers and a
real number $x$, the double sum of reciprocal least common multiples of $A$ up to $x$ is the
real number $\sum 1/\operatorname{lcm}(n, m)$, summed over all ordered pairs $(n, m)$ with
$n, m \in A$, $1 \le n \le x$ and $1 \le m \le x$.

Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Equation (12).
-/
public noncomputable def lcmReciprocalSum (A : Set ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ naturalsInSetUpTo A x,
    ∑ m ∈ naturalsInSetUpTo A x, 1 / (Nat.lcm n m : ℝ)

/-- **Double reciprocal lcm sum of the empty set.** For every real number $x$, the double sum of
reciprocal least common multiples of the empty set up to $x$ is $0$.

Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Equation (12).
-/
@[simp] public theorem lcmReciprocalSum_empty (x : ℝ) : lcmReciprocalSum ∅ x = 0 := by
  simp [lcmReciprocalSum]

/-- **Logarithmic gcd moment.** For a set $A$ of natural numbers and a real number $x$, the
logarithmic gcd moment of $A$ up to $x$ is the sum of $\gcd(n, m)/(nm)$ over all ordered pairs
$(n, m)$ with $n, m \in A$, $1 \le n \le x$ and $1 \le m \le x$.

When $A \cap [1, x]$ is nonempty, dividing by $\big(\sum_{n \in A,\ 1 \le n \le x} 1/n\big)^2$
gives the expected value of $\gcd(n, m)$ for $n$ and $m$ drawn independently from $A \cap [1, x]$,
each with probability proportional to $1/n$.

Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Equation (9).
-/
public noncomputable def gcdLogarithmicMoment (A : Set ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ naturalsInSetUpTo A x,
    ∑ m ∈ naturalsInSetUpTo A x,
      (Nat.gcd n m : ℝ) / ((n : ℝ) * (m : ℝ))

/-- **Gcd defect.** For a set $A$ of natural numbers and a real number $x$, let
$S_A(x) = \sum_{n \in A,\ 1 \le n \le x} 1/n$ be the harmonic sum of $A$ up to $x$, and let
$G_A(x)$ be the sum of $\gcd(n, m)/(nm)$ over all ordered pairs $(n, m)$ with $n, m \in A$,
$1 \le n \le x$ and $1 \le m \le x$. The gcd defect of $A$ up to $x$ is
$\mathcal{E}_A(x) = G_A(x)/S_A(x)^2 - 1$, where division by $0$ gives $0$; in particular
$\mathcal{E}_A(x) = -1$ when $A$ has no element in $[1, x]$.

When $A$ has an element in $[1, x]$, $\mathcal{E}_A(x) + 1$ is the expected value of
$\gcd(n, m)$ for $n$ and $m$ drawn independently from $A \cap [1, x]$, each with probability
proportional to $1/n$, so $\mathcal{E}_A(x)$ is the quantity $\mathbb{E} \gcd(n, m) - 1$ of the
source.

Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Equation (9).
-/
public noncomputable def lcmDefect (A : Set ℕ) (x : ℝ) : ℝ :=
  gcdLogarithmicMoment A x / recipSumUpTo A x ^ 2 - 1

/-- **The gcd defect of the empty set.** For every real number $x$, the gcd defect of the empty
set up to $x$ equals $-1$.

The harmonic sum of the empty set is $0$, and division by $0$ gives $0$.

Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Equation (9).
-/
@[simp] public theorem lcmDefect_empty (x : ℝ) : lcmDefect ∅ x = -1 := by
  simp [lcmDefect, gcdLogarithmicMoment]

/-- **Products of a fixed number of distinct primes.** For a set $\mathcal{P}$ of natural numbers
and $k \in \mathbb{N}$, $\mathcal{P}^{[k]}$ is the set of squarefree natural numbers $n$ whose prime
divisors all lie in $\mathcal{P}$ and which have exactly $k$ distinct prime divisors; that is, the
products of exactly $k$ distinct primes from $\mathcal{P}$. In particular,
$\mathcal{P}^{[0]} = \{1\}$.

Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Lemma 1 notation.
-/
public noncomputable def primeProductLayer (P : Set ℕ) (k : ℕ) : Set ℕ :=
  {n | Squarefree n ∧
    (∀ p, p.Prime → p ∣ n → p ∈ P) ∧
    n.primeFactors.card = k}

/-- **Products of at most a fixed number of distinct primes.** For a set $\mathcal{P}$ of natural
numbers and $k \in \mathbb{N}$, $\mathcal{P}^{[\le k]}$ is the set of natural numbers that lie in
$\mathcal{P}^{[j]}$ for some $j \le k$, where $\mathcal{P}^{[j]}$ is the set of products of exactly
$j$ distinct primes from $\mathcal{P}$; that is,
$\mathcal{P}^{[\le k]} = \bigcup_{j \le k} \mathcal{P}^{[j]}$.

Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Lemma 1 notation.
-/
public noncomputable def primeProductsAtMost (P : Set ℕ) (k : ℕ) : Set ℕ :=
  {n | ∃ j ≤ k, n ∈ primeProductLayer P j}

/-- **At most zero primes means exactly zero primes.** For every set $\mathcal{P}$ of natural
numbers, $\mathcal{P}^{[\le 0]} = \mathcal{P}^{[0]}$, where $\mathcal{P}^{[\le k]}$ and
$\mathcal{P}^{[k]}$ are the products of at most, respectively exactly, $k$ distinct primes from
$\mathcal{P}$.

Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Lemma 1 notation.
-/
public theorem primeProductsAtMost_zero (P : Set ℕ) :
    primeProductsAtMost P 0 = primeProductLayer P 0 := by
  ext n
  simp [primeProductsAtMost]

/-- **Growth function of the dense-set construction.** Let $\operatorname{Log}_2$ be the second
iterated truncated logarithm. For real numbers $C_0$ and $x$, let $k$ be the natural number
$\max(\lceil C_0 \sqrt{\operatorname{Log}_2 x}\,\rceil - 1, 0)$, and set
$h = \operatorname{Log}_2 x - k^2/C_0^2 + 1$, $x' = \exp(\exp((k + 1)^2/C_0^2))$,
$h' = \operatorname{Log}_2 x' - k^2/C_0^2 + 1$ and $\psi = 1 + h^2/h'$. The growth function at
$(C_0, x)$ is $F_{C_0}(x) = \psi\, k^{2k} / (C_0^{2k}\, k!)$. Here division by $0$ gives $0$ and
$0^0 = 1$.

In the source, $h'$ is the value at $x_{k+1} = x'$ of the expression defining $h$, with $k$ kept
fixed, and $F_{C_0}(x)$ is written $\psi(x)\, k^{2k} C_0^{-2k}/k!$; the function is used only for
$C_0 > 0$ and sufficiently large $x$.

Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Equations (13)--(15).
-/
public noncomputable def lcmDenseGrowthF (C₀ x : ℝ) : ℝ :=
  let k : ℕ := Nat.ceil (C₀ * Real.sqrt (truncLog2 x)) - 1
  let h : ℝ := truncLog2 x - (k : ℝ) ^ 2 / C₀ ^ 2 + 1
  let xNext : ℝ := Real.exp (Real.exp (((k + 1 : ℕ) : ℝ) ^ 2 / C₀ ^ 2))
  let hNext : ℝ := truncLog2 xNext - (k : ℝ) ^ 2 / C₀ ^ 2 + 1
  let ψ : ℝ := 1 + h ^ 2 / hNext
  ψ * (k : ℝ) ^ (2 * k) / C₀ ^ (2 * k) / (k.factorial : ℝ)

end

namespace recipSum_primeProductLayer_asymp

open Finset

private lemma mem_upTo {A : Set ℕ} {x : ℝ} {n : ℕ} :
    n ∈ naturalsInSetUpTo A x ↔ 1 ≤ n ∧ n ≤ ⌊x⌋₊ ∧ n ∈ A := by
  classical simp [naturalsInSetUpTo, and_assoc]

-- Count multiples of each prime. For p ≤ N, floor(N/p) ≥ N/(2p).
private lemma log_moment (A : Finset ℕ) (N : ℕ) (hN : 0 < N)
    (hA : ∀ p ∈ A, Nat.Prime p ∧ p ≤ N) :
    ∑ p ∈ A, Real.log p / p ≤ 2 * Real.log N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  apply le_of_mul_le_mul_left (a := (N : ℝ)) _ hN'
  rw [mul_sum]
  calc
    _ ≤ ∑ p ∈ A, 2 * (ArithmeticFunction.vonMangoldt p * (N / p : ℕ)) := by
      refine sum_le_sum fun p hp => ?_
      obtain ⟨hpp, hle⟩ := hA p hp
      have hp' : (0 : ℝ) < p := by exact_mod_cast hpp.pos
      have hd : 1 ≤ N / p := Nat.div_pos hle hpp.pos
      have hb : N ≤ 2 * ((N / p) * p) := calc
        N ≤ (N / p) * p + p := by
          have := Nat.mod_add_div N p
          have := Nat.mod_lt N hpp.pos
          simpa [Nat.mul_comm p] using (show N ≤ p * (N / p) + p by omega)
        _ ≤ _ := by nlinarith [Nat.mul_le_mul_right p hd]
      rw [ArithmeticFunction.vonMangoldt_apply_prime hpp, ← mul_div_assoc, div_le_iff₀ hp']
      have hb' : (N : ℝ) ≤ 2 * (((N / p : ℕ) : ℝ) * p) := by exact_mod_cast hb
      have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_le)
      nlinarith only [mul_le_mul_of_nonneg_right hb' hlog]
    _ ≤ 2 * ∑ p ∈ Ioc 0 N, ArithmeticFunction.vonMangoldt p * (N / p : ℕ) := by
      rw [mul_sum]
      exact sum_le_sum_of_subset_of_nonneg
        (fun p hp => mem_Ioc.mpr ⟨(hA p hp).1.pos, (hA p hp).2⟩) (by intros; positivity)
    _ ≤ _ := by
      rw [← ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum, ArithmeticFunction.vonMangoldt_mul_zeta]
      simp only [ArithmeticFunction.log_apply]
      have h := sum_le_sum (s := Ioc 0 N) (f := fun n : ℕ => Real.log n) (g := fun _ => Real.log N)
        fun n hn => Real.log_le_log (by exact_mod_cast (mem_Ioc.mp hn).1)
          (by exact_mod_cast (mem_Ioc.mp hn).2)
      simp at h
      linarith

private lemma square_moment (A : Finset ℕ) (N : ℕ) (hA : ∀ p ∈ A, 2 ≤ p ∧ p ≤ N) :
    ∑ p ∈ A, (1 / (p : ℝ)) ^ 2 ≤ 1 := by
  let f (i : ℕ) : ℝ := ((i + 1 : ℝ))⁻¹
  have h : ∀ i : ℕ, f (i + 1) ≤ f i := by intro i; dsimp [f]; push_cast; gcongr; linarith
  calc
    _ ≤ ∑ p ∈ A, (f (p - 2) - f (p - 1)) := by
      refine sum_le_sum fun p hp => ?_
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' (hA p hp).1
      simp [f]
      field_simp
      nlinarith
    _ ≤ ∑ p ∈ Icc 2 N, (f (p - 2) - f (p - 1)) := by
      apply sum_le_sum_of_subset_of_nonneg (fun p hp => mem_Icc.mpr (hA p hp))
      intro p hp _
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' (mem_Icc.mp hp).1
      simpa using sub_nonneg.mpr (h j)
    _ ≤ 1 := by
      cases N with
      | zero => simp
      | succ N =>
        have he : ∑ p ∈ Icc 2 (N + 1), (f (p - 2) - f (p - 1)) =
              ∑ i ∈ range N, (f i - f (i + 1)) := by
          rw [← Ico_succ_right_eq_Icc, show Order.succ (N + 1) = N + 2 by rfl,
              ← sum_Ico_add' (fun p => f (p - 2) - f (p - 1)) 0 N 2]
          simp [Nat.Ico_zero_eq_range]
        rw [he, sum_range_sub']
        simpa [f] using (show 0 ≤ ((N : ℝ) + 1)⁻¹ by positivity)

-- Expectation of a function of k independent draws from a finite weighted set.
private noncomputable def mean (A : Finset ℕ) (w : ℕ → ℝ) : ℕ → (List ℕ → ℝ) → ℝ
  | 0, F => F []
  | k + 1, F => ∑ p ∈ A, w p * mean A w k (fun l => F (p :: l))

private lemma mean_const (A : Finset ℕ) (w : ℕ → ℝ) (hw : ∑ p ∈ A, w p = 1)
    (k : ℕ) (a : ℝ) : mean A w k (fun _ => a) = a := by
  induction k with
  | zero => rfl
  | succ k ih => simp [mean, ih, ← sum_mul, hw]

private lemma mean_sum {ι : Type*} (A : Finset ℕ) (w : ℕ → ℝ) (k : ℕ)
    (s : Finset ι) (F : ι → List ℕ → ℝ) :
    mean A w k (fun l => ∑ i ∈ s, F i l) = ∑ i ∈ s, mean A w k (F i) := by
  induction k generalizing F with
  | zero => rfl
  | succ k ih =>
    simp only [mean, ih (fun i l => F i (_ :: l)), mul_sum]
    rw [sum_comm]

private lemma mean_add (A : Finset ℕ) (w : ℕ → ℝ) (k : ℕ) (F G : List ℕ → ℝ) :
    mean A w k (fun l => F l + G l) = mean A w k F + mean A w k G := by
  induction k generalizing F G with
  | zero => rfl
  | succ k ih =>
    simp only [mean, ih (fun l => F (_ :: l)) (fun l => G (_ :: l)), mul_add, sum_add_distrib]

private lemma mean_scale (A : Finset ℕ) (w : ℕ → ℝ) (k : ℕ) (a : ℝ) (F : List ℕ → ℝ) :
    mean A w k (fun l => a * F l) = a * mean A w k F := by
  induction k generalizing F with
  | zero => rfl
  | succ k ih =>
    simp only [mean, ih (fun l => F (_ :: l)), mul_sum]
    exact sum_congr rfl fun _ _ => mul_left_comm ..

private lemma mean_mono (A : Finset ℕ) (w : ℕ → ℝ) (hw : ∀ p ∈ A, 0 ≤ w p)
    (k : ℕ) {F G : List ℕ → ℝ}
    (h : ∀ l : List ℕ, l.length = k → (∀ p ∈ l, p ∈ A) → F l ≤ G l) :
    mean A w k F ≤ mean A w k G := by
  induction k generalizing F G with
  | zero => exact h [] rfl (by simp)
  | succ k ih =>
    apply sum_le_sum fun p hp => mul_le_mul_of_nonneg_left (ih ?_) (hw p hp)
    intro l hl hmem
    exact h (p :: l) (by simp [hl]) (by simpa using ⟨hp, hmem⟩)

private lemma mean_score (A : Finset ℕ) (w v : ℕ → ℝ) (hw : ∑ p ∈ A, w p = 1) (k : ℕ) :
    mean A w k (fun l => (l.map v).sum) = k * ∑ p ∈ A, w p * v p := by
  induction k with
  | zero => simp [mean]
  | succ k ih =>
    simp only [mean, List.map_cons, List.sum_cons, mean_add A w k (fun _ => _) (fun l => _),
      mean_const A w hw, ih, mul_add, sum_add_distrib, ← sum_mul, hw, one_mul, Nat.cast_succ]
    ring

private lemma mean_atom (A : Finset ℕ) (w : ℕ → ℝ) (hw : ∑ p ∈ A, w p = 1)
    (a : List ℕ) (ha : ∀ p ∈ a, p ∈ A) :
    mean A w a.length (fun l => if l = a then 1 else 0) = (a.map w).prod := by
  induction a with
  | nil => simp [mean]
  | cons b a ih =>
    have hb := ha b (by simp)
    simp only [List.length_cons, mean, List.map_cons, List.prod_cons]
    rw [sum_eq_single b]
    · simpa using congrArg (w b * ·) (ih fun p hp => ha p (by simp [hp]))
    · intro p _ hpb
      simp [hpb, mean_const A w hw]
    · simp [hb]

private def duplicate (l : List ℕ) : ℝ := if l.Nodup then 0 else 1

-- Union bound for a repeated draw, summed over the previously drawn coordinates.
private lemma mean_duplicate (A : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∑ p ∈ A, w p = 1) (hw₀ : ∀ p ∈ A, 0 ≤ w p) (k : ℕ) :
    mean A w k duplicate ≤ (k : ℝ) ^ 2 * ∑ p ∈ A, w p ^ 2 := by
  have hQ : 0 ≤ ∑ p ∈ A, w p ^ 2 := by positivity
  induction k with
  | zero => simp [mean, duplicate]
  | succ k ih =>
    have hhit (p : ℕ) (hp : p ∈ A) :
        mean A w k (fun l => duplicate (p :: l)) ≤ mean A w k duplicate + k * w p := by
      let v (q : ℕ) : ℝ := if p = q then 1 else 0
      have h (l : List ℕ) : 0 ≤ (l.map v).sum := by
        apply List.sum_nonneg
        simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
        intros
        dsimp [v]
        split <;> norm_num
      have hmem (l : List ℕ) (hl : p ∈ l) : 1 ≤ (l.map v).sum := by
        induction l with
        | nil => simp at hl
        | cons q l ih =>
          by_cases hpq : p = q
          · simp [v, hpq] at *
            linarith [h l]
          · simpa [v, hpq] using ih (by simpa [hpq] using hl)
      calc
        _ ≤ mean A w k (fun l => duplicate l + (l.map v).sum) := by
          apply mean_mono A w hw₀
          intro l _ _
          by_cases hd : l.Nodup <;> by_cases hm : p ∈ l <;>
            simp only [duplicate, List.nodup_cons, hd, hm, not_true_eq_false, not_false_eq_true,
              and_true, and_false, ite_true, ite_false, zero_add, le_add_iff_nonneg_right] <;>
            first | exact h l | exact hmem l hm
        _ = _ := by
          rw [mean_add A w k duplicate, mean_score A w v hw]
          simp [v, mul_ite, hp]
    calc
      _ ≤ ∑ p ∈ A, w p * (mean A w k duplicate + k * w p) :=
        sum_le_sum fun p hp => mul_le_mul_of_nonneg_left (hhit p hp) (hw₀ p hp)
      _ = mean A w k duplicate + k * ∑ p ∈ A, w p ^ 2 := by
        simp_rw [mul_add, show ∀ a : ℝ, a * (k * a) = k * a ^ 2 by intro a; ring]
        rw [sum_add_distrib, ← sum_mul, ← mul_sum, hw, one_mul]
      _ ≤ _ := by
        push_cast
        nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) k) hQ]

private def good (N : ℕ) (l : List ℕ) : ℝ := if l.Nodup ∧ l.prod ≤ N then 1 else 0

-- Each admissible integer is represented by the permutations of its prime factor list.
private lemma good_mass (P : Set ℕ) (x S : ℝ) (hP : ∀ p ∈ P, Nat.Prime p)
    (hS : 0 < S) (hw : ∑ p ∈ naturalsInSetUpTo P x, (1 / (p : ℝ)) / S = 1) (k : ℕ) :
    mean (naturalsInSetUpTo P x) (fun p => (1 / (p : ℝ)) / S) k (good ⌊x⌋₊) =
      k.factorial * recipSumUpTo (primeProductLayer P k) x / S ^ k := by
  classical
  let A := naturalsInSetUpTo P x
  let B := naturalsInSetUpTo (primeProductLayer P k) x
  let w (p : ℕ) : ℝ := (1 / (p : ℝ)) / S
  let perms (n : ℕ) := n.primeFactorsList.permutations.toFinset
  let atom (a l : List ℕ) : ℝ := if l = a then 1 else 0
  have hcongr (l : List ℕ) (hl : l.length = k) (hA : ∀ p ∈ l, p ∈ A) :
      good ⌊x⌋₊ l = ∑ n ∈ B, ∑ a ∈ perms n, atom a l := by
    have hpr p (hp : p ∈ l) := hP p (mem_upTo.mp (hA p hp)).2.2
    have hpos := List.prod_pos fun p hp => (hpr p hp).pos
    have hperm := Nat.primeFactorsList_unique (l := l) rfl hpr
    have he (n : ℕ) (hn : n ∈ B) : l ∈ perms n ↔ l.prod = n := by
      simp only [perms, List.mem_toFinset, List.mem_permutations]
      exact ⟨fun h => h.prod_eq.trans (Nat.prod_primeFactorsList (by
        have := (mem_upTo.mp hn).1; omega)), fun e => e ▸ hperm⟩
    have hB : l.prod ∈ B ↔ l.Nodup ∧ l.prod ≤ ⌊x⌋₊ := by
      rw [mem_upTo]
      change _ ∧ _ ∧ (Squarefree _ ∧ _ ∧ _) ↔ _
      constructor
      · rintro ⟨_, hb, hs, _⟩
        exact ⟨hperm.nodup_iff.mpr hs.nodup_primeFactorsList, hb⟩
      · rintro ⟨hd, hb⟩
        have hd' := hperm.nodup_iff.mp hd
        refine ⟨hpos, hb, (Nat.squarefree_iff_nodup_primeFactorsList hpos.ne').mpr hd', ?_, ?_⟩
        · intro p hp hdvd
          exact (mem_upTo.mp (hA p (hperm.mem_iff.mpr
            ((Nat.mem_primeFactorsList_iff_dvd hpos.ne' hp).mpr hdvd)))).2.2
        · rw [← Nat.toFinset_factors, List.toFinset_card_of_nodup hd', ← hperm.length_eq, hl]
    simp only [atom, sum_ite_eq]
    simp_rw [sum_congr rfl fun n hn => if_congr (he n hn) rfl rfl]
    simp [good, hB]
  have hmass (n : ℕ) (hn : n ∈ B) : ∑ a ∈ perms n, mean A w k (atom a) =
      k.factorial * (1 / (n : ℝ)) / S ^ k := by
    obtain ⟨hn₁, hnN, hs, hpr, hcard⟩ := mem_upTo.mp hn
    have hlen : n.primeFactorsList.length = k := by
      rwa [← Nat.toFinset_factors, List.toFinset_card_of_nodup hs.nodup_primeFactorsList] at hcard
    have hev (a : List ℕ) (ha : a ∈ perms n) := List.mem_permutations.mp (List.mem_toFinset.mp ha)
    have hweight (a : List ℕ) :
        (a.map w).prod = (1 / (a.prod : ℝ)) / S ^ a.length := by
      induction a with
      | nil => simp
      | cons p l ih =>
        rw [List.map_cons, List.prod_cons, ih, List.prod_cons, Nat.cast_mul, List.length_cons,
          pow_succ]
        simp [w, div_eq_mul_inv]
        ring
    calc
      _ = ∑ _a ∈ perms n, (1 / (n : ℝ)) / S ^ k := by
        refine sum_congr rfl fun a ha => ?_
        have e := hev a ha
        have hlen' := e.length_eq.trans hlen
        have haA : ∀ p ∈ a, p ∈ A := by
          intro p hp
          have hm := e.mem_iff.mp hp
          have hpp := Nat.prime_of_mem_primeFactorsList hm
          exact mem_upTo.mpr ⟨hpp.one_le, (Nat.le_of_mem_primeFactorsList hm).trans hnN,
            hpr p hpp (Nat.dvd_of_mem_primeFactorsList hm)⟩
        rw [← hlen', show mean A w a.length (atom a) = _ from mean_atom A w hw a haA, hweight,
          e.prod_eq, Nat.prod_primeFactorsList (by omega : n ≠ 0)]
      _ = _ := by
        simp [perms, List.toFinset_card_of_nodup
          (List.nodup_permutations _ hs.nodup_primeFactorsList), List.length_permutations, hlen,
          mul_div_assoc]
  have hw₀ (p : ℕ) (_ : p ∈ A) : 0 ≤ w p := by dsimp [w]; positivity
  calc
    _ = mean A w k (fun l => ∑ n ∈ B, ∑ a ∈ perms n, atom a l) :=
      le_antisymm (mean_mono A w hw₀ k fun l hl hA => (hcongr l hl hA).le)
        (mean_mono A w hw₀ k fun l hl hA => (hcongr l hl hA).ge)
    _ = _ := by
      rw [mean_sum]
      simp_rw [mean_sum A w k (perms _) atom]
      rw [sum_congr rfl hmass, ← sum_div, ← mul_sum]
      rfl

-- A tuple outside the cutoff has logarithmic weight at least log N.
private lemma enough_good (A : Finset ℕ) (w : ℕ → ℝ) (N k : ℕ)
    (hN : 1 < N) (hw : ∑ p ∈ A, w p = 1) (hw₀ : ∀ p ∈ A, 0 ≤ w p)
    (hp₀ : ∀ p ∈ A, 0 < p)
    (hcol : (k : ℝ) ^ 2 * ∑ p ∈ A, w p ^ 2 ≤ 1 / 4)
    (hlog : k * ∑ p ∈ A, w p * Real.log p ≤ Real.log N / 4) :
    1 / 2 ≤ mean A w k (good N) := by
  let L := Real.log N
  let v (p : ℕ) := Real.log p
  have hL : 0 < L := Real.log_pos (by exact_mod_cast hN)
  have h (l : List ℕ) (_ : l.length = k) (hl : ∀ p ∈ l, p ∈ A) :
      L ≤ L * good N l + L * duplicate l + (l.map v).sum := by
    have hpos := List.prod_pos fun p hp => hp₀ p (hl p hp)
    have he : (l.map v).sum = Real.log l.prod := by
      rw [Nat.cast_list_prod, Real.log_list_prod]
      · simp [v, List.map_map, Function.comp_def]
      · intro t ht
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ht
        exact Nat.cast_ne_zero.mpr (hp₀ p (hl p hp)).ne'
    have hz : 0 ≤ Real.log l.prod := Real.log_nonneg (by exact_mod_cast hpos)
    have hlarge (hn : ¬l.prod ≤ N) : L ≤ Real.log l.prod :=
      Real.log_le_log (by exact_mod_cast (Nat.zero_lt_of_lt hN))
        (by exact_mod_cast Nat.le_of_lt (Nat.lt_of_not_ge hn))
    rw [he]
    by_cases hd : l.Nodup <;> by_cases hn : l.prod ≤ N <;>
      simp only [good, duplicate, hd, hn, and_true, and_false, ite_true, ite_false,
        mul_one, mul_zero, add_zero, zero_add, le_add_iff_nonneg_right] <;>
        first | exact hz | exact hlarge hn
  have hb := mean_mono A w hw₀ k h
  rw [mean_const A w hw, mean_add, mean_add, mean_scale, mean_scale, mean_score A w v hw] at hb
  have hc := (mean_duplicate A w hw hw₀ k).trans hcol
  change _ ≤ L / 4 at hlog
  change _ ≤ L * _ + L * _ + ↑k * ∑ p ∈ A, w p * v p at hb
  apply le_of_mul_le_mul_left (a := L) _ hL
  linarith [mul_le_mul_of_nonneg_left hc hL.le]

private lemma sum_layers (P : Set ℕ) (x : ℝ) (k : ℕ) :
    recipSumUpTo (primeProductsAtMost P k) x =
      ∑ j ∈ range (k + 1), recipSumUpTo (primeProductLayer P j) x := by
  classical
  let B := naturalsInSetUpTo (primeProductsAtMost P k) x
  have hm (n : ℕ) (hn : n ∈ B) : n.primeFactors.card ∈ range (k + 1) := by
    obtain ⟨_, _, j, hj, _, _, hcard⟩ := mem_upTo.mp hn
    simpa [hcard] using hj
  have hf (j : ℕ) (hj : j ∈ range (k + 1)) :
      B.filter (fun n => n.primeFactors.card = j) =
        naturalsInSetUpTo (primeProductLayer P j) x := by
    ext n
    simp only [B, mem_filter, mem_upTo]
    constructor
    · rintro ⟨⟨hn, hN, i, _, hs, hp, _⟩, hc⟩
      exact ⟨hn, hN, hs, hp, hc⟩
    · rintro ⟨hn, hN, hs, hp, hc⟩
      exact ⟨⟨hn, hN, j, by simpa using hj, hs, hp, hc⟩, hc⟩
  rw [recipSumUpTo, ← sum_fiberwise_of_maps_to hm]
  exact sum_congr rfl fun j hj => by rw [hf j hj, recipSumUpTo]

-- Successive terms grow by a factor of at least two throughout the range.
private lemma sum_terms (S : ℝ) (hS : 0 < S) (k : ℕ) (hk : 2 * (k : ℝ) ≤ S) :
    ∑ j ∈ range (k + 1), S ^ j / j.factorial ≤ 2 * (S ^ k / k.factorial) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [sum_range_succ]
    have hstep : 2 * (S ^ k / k.factorial) ≤ S ^ (k + 1) / (k + 1).factorial := by
      rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
      push_cast at hk ⊢
      field_simp
      exact hk
    have hprev := ih (by push_cast at hk; linarith)
    linarith only [hprev, hstep]

end recipSum_primeProductLayer_asymp

open Finset recipSum_primeProductLayer_asymp

/-- **Harmonic sums over products of distinct primes.** There are constants $c > 0$ and $C > 0$
such that the following holds. Let $\mathcal{P}$ be a set of primes, let $k$ be a natural number,
let $x \ge 1$ be real, and put $S = \sum_{p \in \mathcal{P},\, p \le x} 1/p$,
$T_k = \sum_{n \in \mathcal{P}^{[k]},\, n \le x} 1/n$ and
$T_{\le k} = \sum_{n \in \mathcal{P}^{[\le k]},\, n \le x} 1/n$, where $\mathcal{P}^{[k]}$ and
$\mathcal{P}^{[\le k]}$ are the sets of products of exactly $k$, respectively at most $k$,
distinct primes from $\mathcal{P}$. If $k \le cS$, then
$S^k/(C\,k!) \le T_k \le C\,S^k/k!$ and $S^k/(C\,k!) \le T_{\le k} \le C\,S^k/k!$.

Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Lemma 1.
-/
public theorem recipSum_primeProductLayer_asymp :
    ∃ c : ℝ, 0 < c ∧
    ∃ C : ℝ, 0 < C ∧
    ∀ (P : Set ℕ) (k : ℕ) (x : ℝ),
      (∀ p ∈ P, p.Prime) →
      1 ≤ x →
      let S := recipSumUpTo P x
      let Tk := recipSumUpTo (primeProductLayer P k) x
      let Tle := recipSumUpTo (primeProductsAtMost P k) x
      (k : ℝ) ≤ c * S →
        (S ^ k / (k.factorial : ℝ)) / C ≤ Tk ∧
        Tk ≤ C * (S ^ k / (k.factorial : ℝ)) ∧
        (S ^ k / (k.factorial : ℝ)) / C ≤ Tle ∧
        Tle ≤ C * (S ^ k / (k.factorial : ℝ)) := by
  classical
  refine ⟨1 / 8, by norm_num, 2, by norm_num, ?_⟩
  intro P k x hP hx S Tk Tle hk
  by_cases hk₀ : k = 0
  · subst k
    have hset : naturalsInSetUpTo (primeProductLayer P 0) x = {1} := by
      ext n
      simp only [mem_upTo, mem_singleton]
      constructor
      · rintro ⟨hn, _, _, _, hc⟩
        have := Nat.primeFactors_eq_empty.mp (card_eq_zero.mp hc)
        omega
      · rintro rfl
        exact ⟨by decide, Nat.le_floor (by simpa using hx), by
          exact ⟨squarefree_one, fun p hp hd => (hp.ne_one (Nat.dvd_one.mp hd)).elim, by simp⟩⟩
    have hTk : Tk = 1 := by simp [Tk, recipSumUpTo, hset]
    have hTle : Tle = Tk := by simp [Tle, Tk, primeProductsAtMost_zero]
    norm_num [hTle, hTk]
  let A := naturalsInSetUpTo P x
  let N := ⌊x⌋₊
  let w (p : ℕ) := (1 / (p : ℝ)) / S
  have hk' : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk₀
  have hS : 0 < S := by linarith
  have hA (p : ℕ) (hp : p ∈ A) : p.Prime ∧ p ≤ N :=
    ⟨hP p (mem_upTo.mp hp).2.2, (mem_upTo.mp hp).2.1⟩
  have hN : 1 < N := by
    obtain ⟨p, hp⟩ : A.Nonempty := by
      by_contra! he
      change 0 < ∑ p ∈ A, 1 / (p : ℝ) at hS
      simp [he] at hS
    exact (hA p hp).1.one_lt.trans_le (hA p hp).2
  have hw₀ (p : ℕ) (_ : p ∈ A) : 0 ≤ w p := by dsimp [w]; positivity
  have hw : ∑ p ∈ A, w p = 1 := by
    simp only [w, ← sum_div]
    exact div_self hS.ne'
  have hcol : (k : ℝ) ^ 2 * ∑ p ∈ A, w p ^ 2 ≤ 1 / 4 := by
    simp only [w, div_pow, ← sum_div]
    rw [← mul_div_assoc, div_le_iff₀ (sq_pos_of_pos hS)]
    have hsq := square_moment A N fun p hp => ⟨(hA p hp).1.two_le, (hA p hp).2⟩
    simp only [div_pow] at hsq
    have hks : (k : ℝ) ≤ S / 2 := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hsq (sq_nonneg (k : ℝ)),
      sq_le_sq' (by linarith : -(S / 2) ≤ k) hks]
  have hlog : k * ∑ p ∈ A, w p * Real.log p ≤ Real.log N / 4 := by
    have he (p : ℕ) : w p * Real.log p = (Real.log p / p) / S := by dsimp [w]; ring
    simp_rw [he]
    rw [← sum_div, ← mul_div_assoc, div_le_iff₀ hS]
    have hb := log_moment A N (by omega) hA
    have hL : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN.le)
    nlinarith [mul_le_mul_of_nonneg_left hb hk'.le, mul_le_mul_of_nonneg_right hk hL]
  have hlo := enough_good A w N k hN hw hw₀ (fun p hp => (hA p hp).1.pos) hcol hlog
  rw [good_mass P x S hP hS hw k] at hlo
  have low : (S ^ k / k.factorial) / 2 ≤ Tk := by
    have := (le_div_iff₀ (pow_pos hS k)).mp hlo
    dsimp only [Tk]
    rw [div_right_comm, div_le_iff₀ (by positivity : 0 < (k.factorial : ℝ))]
    linarith
  have upper (j : ℕ) :
      recipSumUpTo (primeProductLayer P j) x ≤ S ^ j / j.factorial := by
    have h := mean_mono A w hw₀ j (F := good N) (G := fun _ => 1)
      (by intro l _ _; simp [good]; split <;> norm_num)
    rw [mean_const A w hw, good_mass P x S hP hS hw j] at h
    rw [le_div_iff₀ (by positivity : 0 < (j.factorial : ℝ))]
    linarith [(div_le_iff₀ (pow_pos hS j)).mp h]
  have hle : Tk ≤ Tle :=
    sum_le_sum_of_subset_of_nonneg (fun n hn => by
      obtain ⟨ha, hb, hc⟩ := mem_upTo.mp hn
      exact mem_upTo.mpr ⟨ha, hb, k, le_rfl, hc⟩) (by intros; positivity)
  refine ⟨low, (upper k).trans (by linarith [show 0 ≤ S ^ k / k.factorial by positivity]),
    low.trans hle, ?_⟩
  rw [show Tle = _ from sum_layers P x k]
  exact (sum_le_sum fun j _ => upper j).trans (sum_terms S hS k (by linarith))

end MetaMathlibExt
