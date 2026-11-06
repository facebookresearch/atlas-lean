/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Optimization Problem 84b: real sum-product exponent
-/
module

public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Topology.Order.Monotone
public import Batteries.Util.ProofWanted

@[expose] public section

open scoped Pointwise

namespace MathlibExt.Combinatorics.RealSumProductExponentWanted

noncomputable section

/-!
# Optimization Problem 84b: real sum-product exponent

Source: `optimizationproblems/constants/84b.md` at commit
`2c1968cd520b60f1cf3cf50749f7285e800e4e15`, SHA-256
`896f56513ea43dfaba160dde68ad73e49f0894150fea48922b8cece636fdeac8`.

The historical equality `C₈₄ᵦ = 2` was refuted in May 2026. The source's
unverified `1.999281` forum row and its approximate-only lower rows are
recorded in metadata, not promoted to exact Lean bounds.
-/

/-- **Size of the larger of the sumset and the product set.** For a finite set $A$ of real
numbers, this is the natural number $\max(|A+A|, |AA|)$, where $A+A = \{a+b : a, b \in A\}$ is the
sumset and $AA = \{ab : a, b \in A\}$ is the product set of $A$. -/
def sumProductMaxCard (A : Finset ℝ) : ℕ :=
  max (A + A).card (A * A).card

/-- **Sum-product ratio.** For a finite set $A$ of real numbers, the sum-product ratio of $A$ is
$\log \max(|A+A|, |AA|) / \log |A|$, where $A+A$ and $AA$ are the sumset and the product set of
$A$. With the conventions $\log 0 = 0$ and $x / 0 = 0$, the ratio is $0$ when $|A| \le 1$. -/
def sumProductRatio (A : Finset ℝ) : ℝ :=
  Real.log (sumProductMaxCard A : ℝ) / Real.log (A.card : ℝ)

/-- **Sum-product ratios at a fixed cardinality.** For a finite set $A \subset \mathbb{R}$ write
$A + A$ and $AA$ for the sets of all sums $a + b$ and all products $ab$ with $a, b \in A$. For a
natural number $n \ge 2$, this is the set of the real numbers
$\log \max(|A + A|, |AA|) / \log |A|$ for all sets $A \subset \mathbb{R}$ with $|A| = n$; for
$n \le 1$ it consists of the single number $0$. -/
def fixedCardinalityRatios (n : ℕ) : Set ℝ :=
  {r : ℝ | ∃ A : Finset ℝ, A.card = n ∧ r = sumProductRatio A}

private theorem fixedCardinalityRatios_finite (n : ℕ) :
    (fixedCardinalityRatios n).Finite := by
  classical
  let pairs : Finset (ℕ × ℕ) :=
    (Finset.range (n * n + 1)).product (Finset.range (n * n + 1))
  let value : ℕ × ℕ → ℝ := fun p =>
    Real.log (((max p.1 p.2 : ℕ) : ℝ)) / Real.log (n : ℝ)
  refine (pairs.finite_toSet.image value).subset ?_
  intro r hr
  change ∃ A : Finset ℝ, A.card = n ∧ r = sumProductRatio A at hr
  rcases hr with ⟨A, hA, rfl⟩
  refine ⟨((A + A).card, (A * A).card), ?_, ?_⟩
  · apply Finset.mem_coe.mpr
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (by
      simpa [hA] using (Finset.card_add_le (s := A) (t := A)))),
      Finset.mem_range.mpr (Nat.lt_succ_of_le (by
        simpa [hA] using (Finset.card_mul_le (s := A) (t := A))))⟩
  · simp [value, sumProductRatio, sumProductMaxCard, hA]

private theorem fixedCardinalityRatios_nonempty (n : ℕ) :
    (fixedCardinalityRatios n).Nonempty := by
  classical
  let A : Finset ℝ :=
    (Finset.range n).map (Nat.castEmbedding : ℕ ↪ ℝ)
  exact ⟨sumProductRatio A, A, by simp [A], rfl⟩

private theorem fixedCardinalityRatios_bddBelow (n : ℕ) :
    BddBelow (fixedCardinalityRatios n) := by
  obtain ⟨r, _hr, hmin⟩ :=
    Set.exists_min_image (fixedCardinalityRatios n) id
      (fixedCardinalityRatios_finite n)
      (fixedCardinalityRatios_nonempty n)
  refine ⟨r, ?_⟩
  intro y hy
  simpa using hmin y hy

/-- **Least sum-product ratio at a fixed cardinality.** For a natural number $n$, the level
minimum $m(n)$ is the infimum of the sum-product ratios $\log \max(|A+A|, |AA|) / \log |A|$ over
all sets $A$ of $n$ real numbers, where $A+A$ and $AA$ are the sumset and the product set of $A$,
and the ratio is taken to be $0$ when $|A| \le 1$ (conventions $\log 0 = 0$ and $x / 0 = 0$).

The set of these ratios is finite and nonempty, so the infimum is attained. -/
def sumProductLevelMinimum (n : ℕ) : ℝ :=
  sInf (fixedCardinalityRatios n)

/-- **The level minimum is attained.** For every natural number $n$, let $m(n)$ be the infimum of
the sum-product ratios $\log \max(|A+A|, |AA|) / \log |A|$ over all sets $A$ of $n$ real numbers,
where $A+A$ and $AA$ are the sumset and the product set of $A$ and the ratio is taken to be $0$
when $|A| \le 1$ (conventions $\log 0 = 0$ and $x / 0 = 0$). Then $m(n)$ is the least element of
the set of these ratios: it is the ratio of some set of $n$ real numbers, and no set of $n$ real
numbers has a smaller ratio. -/
theorem sumProductLevelMinimum_isLeast (n : ℕ) :
    IsLeast (fixedCardinalityRatios n) (sumProductLevelMinimum n) := by
  simpa only [sumProductLevelMinimum] using
    (fixedCardinalityRatios_finite n).isClosed.isLeast_csInf
      (fixedCardinalityRatios_nonempty n)
      (fixedCardinalityRatios_bddBelow n)

/-- **The sum-product ratio is nonnegative.** For every nonempty finite set $A$ of real numbers,
the sum-product ratio $\log \max(|A+A|, |AA|) / \log |A|$ is at least $0$, where $A+A$ and $AA$
are the sumset and the product set of $A$, and the ratio is taken to be $0$ when $|A| = 1$
(conventions $\log 0 = 0$ and $x / 0 = 0$). -/
theorem sumProductRatio_nonneg (A : Finset ℝ) (hA : A.Nonempty) :
    0 ≤ sumProductRatio A := by
  have hone : 1 ≤ A.card := Finset.one_le_card.mpr hA
  have hsum : A.card ≤ (A + A).card :=
    Finset.card_le_card_add_left hA
  have hmax : 1 ≤ sumProductMaxCard A := by
    exact hone.trans (hsum.trans (Nat.le_max_left _ _))
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast hmax))
    (Real.log_nonneg (by exact_mod_cast hone))

/-- **The sum-product ratio is at most two.** For every finite set $A$ of real numbers with
$|A| \ge 2$, the sum-product ratio $\log \max(|A+A|, |AA|) / \log |A|$ is at most $2$, where $A+A$
and $AA$ are the sumset and the product set of $A$. -/
theorem sumProductRatio_le_two (A : Finset ℝ) (hA : 2 ≤ A.card) :
    sumProductRatio A ≤ 2 := by
  have hAone : (1 : ℝ) < A.card := by exact_mod_cast hA
  have hApos : (0 : ℝ) < A.card := zero_lt_one.trans hAone
  have hAnonempty : A.Nonempty :=
    Finset.card_pos.mp (Nat.zero_lt_two.trans_le hA)
  have hsumpos : 0 < (A + A).card :=
    (Finset.card_pos.mpr hAnonempty).trans_le
      (Finset.card_le_card_add_left hAnonempty)
  have hmaxpos : (0 : ℝ) < sumProductMaxCard A := by
    exact_mod_cast hsumpos.trans_le (Nat.le_max_left _ _)
  have hmaxleNat : sumProductMaxCard A ≤ A.card * A.card := by
    exact max_le Finset.card_add_le Finset.card_mul_le
  have hmaxle : (sumProductMaxCard A : ℝ) ≤ A.card * A.card := by
    exact_mod_cast hmaxleNat
  rw [sumProductRatio, div_le_iff₀ (Real.log_pos hAone)]
  calc
    Real.log (sumProductMaxCard A : ℝ) ≤ Real.log ((A.card : ℝ) * A.card) :=
      Real.log_le_log hmaxpos hmaxle
    _ = Real.log (A.card : ℝ) + Real.log (A.card : ℝ) := by
      rw [Real.log_mul hApos.ne' hApos.ne']
    _ = 2 * Real.log (A.card : ℝ) := by ring

/-- **The level minimum is nonnegative.** For every natural number $n \ge 1$, the level minimum
$m(n)$, the infimum of the sum-product ratios $\log \max(|A+A|, |AA|) / \log |A|$ over all sets $A$
of $n$ real numbers, satisfies $m(n) \ge 0$. Here $A+A$ and $AA$ are the sumset and the product set
of $A$, and the ratio is taken to be $0$ when $|A| = 1$ (conventions $\log 0 = 0$, $x / 0 = 0$). -/
theorem sumProductLevelMinimum_nonneg (n : ℕ) (hn : 0 < n) :
    0 ≤ sumProductLevelMinimum n := by
  rcases (sumProductLevelMinimum_isLeast n).1 with ⟨A, hcard, hvalue⟩
  rw [hvalue]
  apply sumProductRatio_nonneg
  exact Finset.card_pos.mp (hcard.symm ▸ hn)

/-- **The level minimum is at most two.** For every natural number $n \ge 2$, the level minimum
$m(n)$, the infimum of the sum-product ratios $\log \max(|A+A|, |AA|) / \log |A|$ over all sets $A$
of $n$ real numbers, where $A+A$ and $AA$ are the sumset and the product set of $A$, satisfies
$m(n) \le 2$. -/
theorem sumProductLevelMinimum_le_two (n : ℕ) (hn : 2 ≤ n) :
    sumProductLevelMinimum n ≤ 2 := by
  let A : Finset ℝ :=
    (Finset.range n).map (Nat.castEmbedding : ℕ ↪ ℝ)
  have hcard : A.card = n := by simp [A]
  have hmem : sumProductRatio A ∈ fixedCardinalityRatios n :=
    ⟨A, hcard, rfl⟩
  exact ((sumProductLevelMinimum_isLeast n).2 hmem).trans
    (sumProductRatio_le_two A (hcard.symm ▸ hn))

/-- **The sum-product level minima eventually lie in $[0, 2]$.** For a finite set
$A \subset \mathbb{R}$ write $A + A$ and $AA$ for the sets of all sums $a + b$ and all products
$ab$ with $a, b \in A$. For a natural number $n \ge 2$ let $m_n$ be the least value of
$\log \max(|A + A|, |AA|) / \log n$ over sets $A \subset \mathbb{R}$ with $|A| = n$. Then
$0 \le m_n \le 2$ for every sufficiently large $n$. -/
theorem eventually_sumProductLevelMinimum_mem_Icc :
    ∀ᶠ n : ℕ in Filter.atTop,
      sumProductLevelMinimum n ∈ Set.Icc (0 : ℝ) 2 := by
  filter_upwards [Filter.eventually_ge_atTop 2] with n hn
  exact ⟨sumProductLevelMinimum_nonneg n (Nat.zero_lt_two.trans_le hn),
    sumProductLevelMinimum_le_two n hn⟩

/-- **The level minima are eventually bounded above.** There is a real number $b$ such that
$m(n) \le b$ for all sufficiently large natural numbers $n$, where the level minimum $m(n)$ is the
infimum of the sum-product ratios $\log \max(|A+A|, |AA|) / \log |A|$ over all sets $A$ of $n$
real numbers, and $A+A$ and $AA$ are the sumset and the product set of $A$. -/
theorem sumProductLevelMinimum_isBoundedUnder_le :
    Filter.atTop.IsBoundedUnder (· ≤ ·) sumProductLevelMinimum :=
  Filter.isBoundedUnder_of_eventually_le
    (eventually_sumProductLevelMinimum_mem_Icc.mono fun _ hn => hn.2)

/-- **The sum-product level minima are eventually bounded below.** There is a real number $b$
such that the sum-product level minimum $m(n)$ satisfies $m(n) \ge b$ for all sufficiently large
$n$. -/
theorem sumProductLevelMinimum_isBoundedUnder_ge :
    Filter.atTop.IsBoundedUnder (· ≥ ·) sumProductLevelMinimum :=
  Filter.isBoundedUnder_of_eventually_ge
    (eventually_sumProductLevelMinimum_mem_Icc.mono fun _ hn => hn.1)

/-- **Sum-product exponent of the reals.** For $n \in \mathbb{N}$ let $m(n)$ be the sum-product
level minimum: the least value of $\log \max(|A + A|, |AA|) / \log |A|$ over sets
$A \subset \mathbb{R}$ with $n$ elements, where $A + A$ and $AA$ are the sets of sums $a + b$ and
products $ab$ of elements $a, b \in A$. The real sum-product exponent is
$\liminf_{n \to \infty} m(n)$.

For $n \le 1$ the conventions $\log 0 = 0$ and $x / 0 = 0$ give $m(n) = 0$; these levels do not
affect the limit inferior. -/
def sumProductExponent : ℝ :=
  Filter.liminf sumProductLevelMinimum Filter.atTop

/-- **The sum-product exponent ignores sets of size $0$ and $1$.** Let $m(n)$ be the sum-product
level minimum at $n$. The real sum-product exponent equals $\liminf_{n \to \infty} m(n + 2)$, so
the levels $n = 0$ and $n = 1$ do not affect it. -/
theorem sumProductExponent_eq_liminf_add_two :
    sumProductExponent =
      Filter.liminf (fun n : ℕ => sumProductLevelMinimum (n + 2)) Filter.atTop :=
  (Filter.liminf_nat_add sumProductLevelMinimum 2).symm

/-- **Uniform sum-product lower growth at rate $s$.** A real number $s$ has uniform sum-product
lower growth when for every $\varepsilon > 0$ there is a constant $K > 0$ such that every
nonempty finite set $A \subset \mathbb{R}$ satisfies
$K \cdot |A|^{s - \varepsilon} \le \max(|A + A|, |AA|)$, where $A + A$ and $AA$ are the sets of
sums $a + b$ and products $ab$ of elements $a, b \in A$.

The constant $K$ may depend on $\varepsilon$ but not on $A$. Requiring $A$ to be nonempty
avoids giving a meaning to $0^{s - \varepsilon}$; singleton sets are included. -/
def HasUniformSumProductLowerGrowth (s : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ K : ℝ, 0 < K ∧
      ∀ A : Finset ℝ,
        A.Nonempty →
          K * Real.rpow (A.card : ℝ) (s - ε) ≤ (sumProductMaxCard A : ℝ)

/-- **Statement of the uniform-growth characterization of the real sum-product exponent.** For a
finite set $A \subset \mathbb{R}$ write $A + A$ and $AA$ for the sets of all sums $a + b$ and all
products $ab$ with $a, b \in A$, and let the real sum-product exponent $C_{84b}$ be the limit
inferior, as $n \to \infty$, of the least value of $\log \max(|A + A|, |AA|) / \log n$ over sets
$A \subset \mathbb{R}$ with $|A| = n$. This is the proposition that $C_{84b}$ is the largest real
number $s$ with the following property: for every $\varepsilon > 0$ there is a constant $K > 0$
such that $K |A|^{s - \varepsilon} \le \max(|A + A|, |AA|)$ for every nonempty finite set
$A \subset \mathbb{R}$. -/
def epsilonUniformLowerGrowthCharacterization : Prop :=
  IsGreatest {s : ℝ | HasUniformSumProductLowerGrowth s} sumProductExponent

/-- **Statement of the Erdős–Szemerédi conjecture for real sets.** For a finite set
$A \subset \mathbb{R}$ write $A + A$ and $AA$ for the sets of all sums $a + b$ and all products
$ab$ with $a, b \in A$, and let the real sum-product exponent $C_{84b}$ be the limit inferior, as
$n \to \infty$, of the least value of $\log \max(|A + A|, |AA|) / \log n$ over sets
$A \subset \mathbb{R}$ with $|A| = n$. This is the proposition that $C_{84b} = 2$. -/
def erdosSzemerediHistoricalConjecture : Prop :=
  sumProductExponent = 2

/-- **Statement of the Bloom–Sawin–Schildkraut–Zhelezov refutation.** The statement that the real
sum-product exponent $C$ satisfies $C < 2$. -/
def bloomSawinSchildkrautZhelezovRefutation : Prop :=
  sumProductExponent < 2

/-- **Statement of the upper bound two for the real sum-product exponent.** For a finite set
$A \subset \mathbb{R}$ write $A + A$ and $AA$ for the sets of all sums $a + b$ and all products
$ab$ with $a, b \in A$, and let the real sum-product exponent $C_{84b}$ be the limit inferior, as
$n \to \infty$, of the least value of $\log \max(|A + A|, |AA|) / \log n$ over sets
$A \subset \mathbb{R}$ with $|A| = n$. This is the proposition that $C_{84b} \le 2$. -/
def erdosSzemerediHistoricalUpperBound : Prop :=
  sumProductExponent ≤ 2

/-- **Statement of the Bloom–Sawin–Schildkraut–Zhelezov upper bound.** The statement that there is a
real number $c > 0$ such that the real sum-product exponent $C$ satisfies $C \le 2 - c$. -/
def bloomSawinSchildkrautZhelezovUpperBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ sumProductExponent ≤ 2 - c

/-- **Statement of the Bloom–Sawin–Schildkraut–Zhelezov numerical upper bound.** The statement that
the real sum-product exponent $C$ satisfies $C \le 199999913/100000000$. -/
def bloomSawinSchildkrautZhelezovNumericalUpperBound : Prop :=
  sumProductExponent ≤ (199999913 : ℝ) / 100000000

/-- **Statement of the trivial lower bound for the real sum-product exponent.** For a finite set
$A \subset \mathbb{R}$ write $A + A$ and $AA$ for the sets of all sums $a + b$ and all products
$ab$ with $a, b \in A$. This is the proposition that the real sum-product exponent, the limit
inferior, as $n \to \infty$, of the least value of $\log \max(|A + A|, |AA|) / \log n$ over sets
$A \subset \mathbb{R}$ with $|A| = n$, is at least $1$. -/
def trivialLowerBound : Prop :=
  (1 : ℝ) ≤ sumProductExponent

/-- **Statement of Elekes's lower bound.** For a finite set $A \subset \mathbb{R}$ write $A + A$
and $AA$ for the sets of all sums $a + b$ and all products $ab$ with $a, b \in A$, and let the real
sum-product exponent $C_{84b}$ be the limit inferior, as $n \to \infty$, of the least value of
$\log \max(|A + A|, |AA|) / \log n$ over sets $A \subset \mathbb{R}$ with $|A| = n$. This is the
proposition that $C_{84b} \ge 5/4$. -/
def elekesLowerBound : Prop :=
  (5 : ℝ) / 4 ≤ sumProductExponent

/-- **Statement of Solymosi's $14/11$ lower bound.** The proposition that the real sum-product
exponent is at least $14/11$. -/
def solymosiFourteenEleventhsLowerBound : Prop :=
  (14 : ℝ) / 11 ≤ sumProductExponent

/-- **Statement of Solymosi's $4/3$ lower bound.** The proposition that the real sum-product
exponent is at least $4/3$. -/
def solymosiFourThirdsLowerBound : Prop :=
  (4 : ℝ) / 3 ≤ sumProductExponent

/-- **Statement of the Rudnev–Stevens lower bound.** The proposition that the real sum-product
exponent is at least $1558/1167 = 4/3 + 2/1167$. -/
def rudnevStevensLowerBound : Prop :=
  (1558 : ℝ) / 1167 ≤ sumProductExponent

/-- **Statement of Bloom's lower bound for the real sum-product exponent.** The statement that the
real sum-product exponent $C$ satisfies $1270/951 \le C$. -/
def bloomLowerBound : Prop :=
  (1270 : ℝ) / 951 ≤ sumProductExponent

/-- **Statement of Cushman's lower bound for the real sum-product exponent.** The statement that the
real sum-product exponent $C$ satisfies $4/3 + 10/4407 \le C$. -/
def cushmanCurrentLowerBound : Prop :=
  (4 : ℝ) / 3 + (10 : ℝ) / 4407 ≤ sumProductExponent

end

/--
**The real sum-product exponent is the largest uniform growth rate.** For a finite set
$A \subset \mathbb{R}$ write $A + A$ and $AA$ for the sets of all sums $a + b$ and all products
$ab$ with $a, b \in A$, and let the real sum-product exponent $C_{84b}$ be the limit inferior, as
$n \to \infty$, of the least value of $\log \max(|A + A|, |AA|) / \log n$ over sets
$A \subset \mathbb{R}$ with $|A| = n$. Then $C_{84b}$ is the largest real number $s$ with the
following property: for every $\varepsilon > 0$ there is a constant $K > 0$ such that
$K |A|^{s - \varepsilon} \le \max(|A + A|, |AA|)$ for every nonempty finite set
$A \subset \mathbb{R}$.

Optimization Problems 84b gives this as an equivalent definition of $C_{84b}$.

Source: Paul Erdős and Endre Szemerédi, On sums and products of
integers, Studies in Pure Mathematics (1983), 213-218,
https://doi.org/10.1007/978-3-0348-5438-2_19; György Elekes, On the number of sums and products,
Acta Arithmetica 81 (1997), no. 4, 365-367, https://doi.org/10.4064/aa-81-4-365-367; József
Solymosi, On the number of sums and products, Bulletin of the London Mathematical Society 37
(2005), no. 4, 491-494, https://doi.org/10.1112/S0024609305004261; József Solymosi, Bounding
multiplicative energy by the sumset, Advances in Mathematics 222 (2009), no. 2, 402-408,
https://doi.org/10.1016/j.aim.2009.04.006; Misha Rudnev and Sophie Stevens, An update on the
sum-product problem, Mathematical Proceedings of the Cambridge Philosophical Society 173 (2022),
no. 2, 411-430, https://arxiv.org/abs/2005.11145; Thomas F. Bloom, A history of the sum-product
problem, https://thomasbloom.org/notes/sumproduct.html; Adam Cushman, A note on the sum-product
problem and the convex sumset problem, arXiv:2512.13849 (2025),
https://arxiv.org/abs/2512.13849; Thomas F. Bloom, Will Sawin, Carl Schildkraut, and Dmitrii
Zhelezov, The sum-product conjecture is false for real numbers, arXiv:2605.28781 (2026),
https://arxiv.org/abs/2605.28781; Optimization Problems, record 84b, Sum-product exponent for
the reals, tables of known upper and lower bounds (source commit
2c1968cd520b60f1cf3cf50749f7285e800e4e15),
https://github.com/teorth/optimizationproblems/blob/2c1968cd520b60f1cf3cf50749f7285e800e4e15/constants/84b.md.
Moved from `OpenConjectures/Combinatorics/RealSumProductExponent`.
-/
public theorem_wanted epsilonUniformLowerGrowthCharacterization_holds : epsilonUniformLowerGrowthCharacterization

/--
**The Erdős–Szemerédi conjecture fails for real sets.** For a finite set $A \subset \mathbb{R}$
write $A + A$ and $AA$ for the sets of all sums $a + b$ and all products $ab$ with $a, b \in A$,
and let the real sum-product exponent $C_{84b}$ be the limit inferior, as $n \to \infty$, of the
least value of $\log \max(|A + A|, |AA|) / \log n$ over sets $A \subset \mathbb{R}$ with
$|A| = n$. Then $C_{84b} \ne 2$.

Bloom, Sawin, Schildkraut and Zhelezov construct arbitrarily large finite sets
$A \subset \mathbb{R}$ with $\max(|A + A|, |AA|) \le |A|^{2 - c}$ for an absolute constant $c > 0$,
so $C_{84b} \le 2 - c$.

Source: Paul Erdős and Endre Szemerédi, On sums and products of
integers, Studies in Pure Mathematics (1983), 213-218,
https://doi.org/10.1007/978-3-0348-5438-2_19; György Elekes, On the number of sums and products,
Acta Arithmetica 81 (1997), no. 4, 365-367, https://doi.org/10.4064/aa-81-4-365-367; József
Solymosi, On the number of sums and products, Bulletin of the London Mathematical Society 37
(2005), no. 4, 491-494, https://doi.org/10.1112/S0024609305004261; József Solymosi, Bounding
multiplicative energy by the sumset, Advances in Mathematics 222 (2009), no. 2, 402-408,
https://doi.org/10.1016/j.aim.2009.04.006; Misha Rudnev and Sophie Stevens, An update on the
sum-product problem, Mathematical Proceedings of the Cambridge Philosophical Society 173 (2022),
no. 2, 411-430, https://arxiv.org/abs/2005.11145; Thomas F. Bloom, A history of the sum-product
problem, https://thomasbloom.org/notes/sumproduct.html; Adam Cushman, A note on the sum-product
problem and the convex sumset problem, arXiv:2512.13849 (2025),
https://arxiv.org/abs/2512.13849; Thomas F. Bloom, Will Sawin, Carl Schildkraut, and Dmitrii
Zhelezov, The sum-product conjecture is false for real numbers, arXiv:2605.28781 (2026),
https://arxiv.org/abs/2605.28781; Optimization Problems, record 84b, Sum-product exponent for
the reals, tables of known upper and lower bounds (source commit
2c1968cd520b60f1cf3cf50749f7285e800e4e15),
https://github.com/teorth/optimizationproblems/blob/2c1968cd520b60f1cf3cf50749f7285e800e4e15/constants/84b.md.
Moved from `OpenConjectures/Combinatorics/RealSumProductExponent`.
-/
public theorem_wanted erdosSzemerediHistoricalConjecture_refuted : ¬ erdosSzemerediHistoricalConjecture

/--
**The real sum-product exponent is less than 2 (Bloom–Sawin–Schildkraut–Zhelezov).** The real
sum-product exponent $C$ satisfies $C < 2$. Here, for a finite set $A \subset \mathbb{R}$,
$A + A$ and $A \cdot A$ are the sets of sums $a + b$ and products $ab$ with $a, b \in A$, and
$M(A) = \max(|A + A|, |A \cdot A|)$; for $n \ge 2$, $m(n)$ is the minimum of
$\log M(A) / \log |A|$ over all $A \subset \mathbb{R}$ with $|A| = n$; and
$C = \liminf_{n \to \infty} m(n)$.

This refutes the historical Erdős–Szemerédi conjecture $C = 2$ for real sets: Bloom, Sawin,
Schildkraut and Zhelezov (arXiv:2605.28781) construct arbitrarily large finite sets
$A \subset \mathbb{R}$ with $M(A) \le |A|^{2 - c}$ for an absolute constant $c > 0$.

Source: Paul Erdős and Endre Szemerédi, On sums and products of integers, Studies in Pure
Mathematics (1983), 213-218, https://doi.org/10.1007/978-3-0348-5438-2_19; György Elekes, On the
number of sums and products, Acta Arithmetica 81 (1997), no. 4, 365-367,
https://doi.org/10.4064/aa-81-4-365-367; József Solymosi, On the number of sums and products,
Bulletin of the London Mathematical Society 37 (2005), no. 4, 491-494,
https://doi.org/10.1112/S0024609305004261; József Solymosi, Bounding multiplicative energy by
the sumset, Advances in Mathematics 222 (2009), no. 2, 402-408,
https://doi.org/10.1016/j.aim.2009.04.006; Misha Rudnev and Sophie Stevens, An update on the
sum-product problem, Mathematical Proceedings of the Cambridge Philosophical Society 173 (2022),
no. 2, 411-430, https://arxiv.org/abs/2005.11145; Thomas F. Bloom, A history of the sum-product
problem, https://thomasbloom.org/notes/sumproduct.html; Adam Cushman, A note on the sum-product
problem and the convex sumset problem, arXiv:2512.13849 (2025),
https://arxiv.org/abs/2512.13849; Thomas F. Bloom, Will Sawin, Carl Schildkraut, and Dmitrii
Zhelezov, The sum-product conjecture is false for real numbers, arXiv:2605.28781 (2026),
https://arxiv.org/abs/2605.28781; Optimization Problems, record 84b, Sum-product exponent for
the reals, tables of known upper and lower bounds (source commit
2c1968cd520b60f1cf3cf50749f7285e800e4e15),
https://github.com/teorth/optimizationproblems/blob/2c1968cd520b60f1cf3cf50749f7285e800e4e15/constants/84b.md.
Moved from `OpenConjectures/Combinatorics/RealSumProductExponent`.
-/
public theorem_wanted bloomSawinSchildkrautZhelezovRefutation_holds : bloomSawinSchildkrautZhelezovRefutation

/--
**The real sum-product exponent is at most two.** For a finite set $A \subset \mathbb{R}$ write
$A + A$ and $AA$ for the sets of all sums $a + b$ and all products $ab$ with $a, b \in A$, and
let the real sum-product exponent $C_{84b}$ be the limit inferior, as $n \to \infty$, of the least
value of $\log \max(|A + A|, |AA|) / \log n$ over sets $A \subset \mathbb{R}$ with $|A| = n$.
Then $C_{84b} \le 2$.

This follows from $|A + A| \le |A|^2$ and $|AA| \le |A|^2$; Optimization Problems 84b records it
as the upper bound of Erdős and Szemerédi (1983).

Source: Paul Erdős and Endre Szemerédi, On sums and
products of integers, Studies in Pure Mathematics (1983), 213-218,
https://doi.org/10.1007/978-3-0348-5438-2_19; György Elekes, On the number of sums and products,
Acta Arithmetica 81 (1997), no. 4, 365-367, https://doi.org/10.4064/aa-81-4-365-367; József
Solymosi, On the number of sums and products, Bulletin of the London Mathematical Society 37
(2005), no. 4, 491-494, https://doi.org/10.1112/S0024609305004261; József Solymosi, Bounding
multiplicative energy by the sumset, Advances in Mathematics 222 (2009), no. 2, 402-408,
https://doi.org/10.1016/j.aim.2009.04.006; Misha Rudnev and Sophie Stevens, An update on the
sum-product problem, Mathematical Proceedings of the Cambridge Philosophical Society 173 (2022),
no. 2, 411-430, https://arxiv.org/abs/2005.11145; Thomas F. Bloom, A history of the sum-product
problem, https://thomasbloom.org/notes/sumproduct.html; Adam Cushman, A note on the sum-product
problem and the convex sumset problem, arXiv:2512.13849 (2025),
https://arxiv.org/abs/2512.13849; Thomas F. Bloom, Will Sawin, Carl Schildkraut, and Dmitrii
Zhelezov, The sum-product conjecture is false for real numbers, arXiv:2605.28781 (2026),
https://arxiv.org/abs/2605.28781; Optimization Problems, record 84b, Sum-product exponent for
the reals, tables of known upper and lower bounds (source commit
2c1968cd520b60f1cf3cf50749f7285e800e4e15),
https://github.com/teorth/optimizationproblems/blob/2c1968cd520b60f1cf3cf50749f7285e800e4e15/constants/84b.md.
Moved from `OpenConjectures/Combinatorics/RealSumProductExponent`.
-/
public theorem_wanted erdosSzemerediHistoricalUpperBound_holds : erdosSzemerediHistoricalUpperBound

/--
**Bloom–Sawin–Schildkraut–Zhelezov upper bound for the real sum-product exponent.** There is a
real number $c > 0$ such that the real sum-product exponent $C$ satisfies $C \le 2 - c$. Here,
for a finite set $A \subset \mathbb{R}$, $A + A$ and $A \cdot A$ are the sets of sums $a + b$
and products $ab$ with $a, b \in A$, and $M(A) = \max(|A + A|, |A \cdot A|)$; for $n \ge 2$,
$m(n)$ is the minimum of $\log M(A) / \log |A|$ over all $A \subset \mathbb{R}$ with
$|A| = n$; and $C = \liminf_{n \to \infty} m(n)$.

Bloom, Sawin, Schildkraut and Zhelezov (arXiv:2605.28781) construct arbitrarily large finite
sets $A \subset \mathbb{R}$ with $M(A) \le |A|^{2 - c}$ for an absolute constant $c > 0$;
Optimization Problems 84b lists the resulting upper bound $2 - c$.

Source: Paul Erdős and Endre Szemerédi, On sums and products of integers, Studies in Pure
Mathematics (1983), 213-218, https://doi.org/10.1007/978-3-0348-5438-2_19; György Elekes, On the
number of sums and products, Acta Arithmetica 81 (1997), no. 4, 365-367,
https://doi.org/10.4064/aa-81-4-365-367; József Solymosi, On the number of sums and products,
Bulletin of the London Mathematical Society 37 (2005), no. 4, 491-494,
https://doi.org/10.1112/S0024609305004261; József Solymosi, Bounding multiplicative energy by
the sumset, Advances in Mathematics 222 (2009), no. 2, 402-408,
https://doi.org/10.1016/j.aim.2009.04.006; Misha Rudnev and Sophie Stevens, An update on the
sum-product problem, Mathematical Proceedings of the Cambridge Philosophical Society 173 (2022),
no. 2, 411-430, https://arxiv.org/abs/2005.11145; Thomas F. Bloom, A history of the sum-product
problem, https://thomasbloom.org/notes/sumproduct.html; Adam Cushman, A note on the sum-product
problem and the convex sumset problem, arXiv:2512.13849 (2025),
https://arxiv.org/abs/2512.13849; Thomas F. Bloom, Will Sawin, Carl Schildkraut, and Dmitrii
Zhelezov, The sum-product conjecture is false for real numbers, arXiv:2605.28781 (2026),
https://arxiv.org/abs/2605.28781; Optimization Problems, record 84b, Sum-product exponent for
the reals, tables of known upper and lower bounds (source commit
2c1968cd520b60f1cf3cf50749f7285e800e4e15),
https://github.com/teorth/optimizationproblems/blob/2c1968cd520b60f1cf3cf50749f7285e800e4e15/constants/84b.md.
Moved from `OpenConjectures/Combinatorics/RealSumProductExponent`.
-/
public theorem_wanted bloomSawinSchildkrautZhelezovUpperBound_holds : bloomSawinSchildkrautZhelezovUpperBound

/--
**Bloom–Sawin–Schildkraut–Zhelezov numerical upper bound for the real sum-product exponent.** The
real sum-product exponent $C$ satisfies $C \le 199999913/100000000 = 1.99999913$. Here, for a
finite set $A \subset \mathbb{R}$, $A + A$ and $A \cdot A$ are the sets of sums $a + b$ and
products $ab$ with $a, b \in A$, and $M(A) = \max(|A + A|, |A \cdot A|)$; for $n \ge 2$, $m(n)$
is the minimum of $\log M(A) / \log |A|$ over all $A \subset \mathbb{R}$ with $|A| = n$; and
$C = \liminf_{n \to \infty} m(n)$.

Bloom, Sawin, Schildkraut and Zhelezov sketch, in the section "Numerical estimates" of
arXiv:2605.28781, a quantified version of their construction that gives arbitrarily large finite
sets $A \subset \mathbb{R}$ with $M(A) \le |A|^{2 - 0.00000087}$; they call this value
non-optimized. Optimization Problems 84b lists it as the explicit upper bound $1.99999913$.

Source: Paul Erdős and Endre Szemerédi, On sums and products of integers, Studies in Pure
Mathematics (1983), 213-218, https://doi.org/10.1007/978-3-0348-5438-2_19; György Elekes, On the
number of sums and products, Acta Arithmetica 81 (1997), no. 4, 365-367,
https://doi.org/10.4064/aa-81-4-365-367; József Solymosi, On the number of sums and products,
Bulletin of the London Mathematical Society 37 (2005), no. 4, 491-494,
https://doi.org/10.1112/S0024609305004261; József Solymosi, Bounding multiplicative energy by
the sumset, Advances in Mathematics 222 (2009), no. 2, 402-408,
https://doi.org/10.1016/j.aim.2009.04.006; Misha Rudnev and Sophie Stevens, An update on the
sum-product problem, Mathematical Proceedings of the Cambridge Philosophical Society 173 (2022),
no. 2, 411-430, https://arxiv.org/abs/2005.11145; Thomas F. Bloom, A history of the sum-product
problem, https://thomasbloom.org/notes/sumproduct.html; Adam Cushman, A note on the sum-product
problem and the convex sumset problem, arXiv:2512.13849 (2025),
https://arxiv.org/abs/2512.13849; Thomas F. Bloom, Will Sawin, Carl Schildkraut, and Dmitrii
Zhelezov, The sum-product conjecture is false for real numbers, arXiv:2605.28781 (2026),
https://arxiv.org/abs/2605.28781; Optimization Problems, record 84b, Sum-product exponent for
the reals, tables of known upper and lower bounds (source commit
2c1968cd520b60f1cf3cf50749f7285e800e4e15),
https://github.com/teorth/optimizationproblems/blob/2c1968cd520b60f1cf3cf50749f7285e800e4e15/constants/84b.md.
Moved from `OpenConjectures/Combinatorics/RealSumProductExponent`.
-/
public theorem_wanted bloomSawinSchildkrautZhelezovNumericalUpperBound_holds : bloomSawinSchildkrautZhelezovNumericalUpperBound

/--
**Trivial lower bound for the real sum-product exponent.** The real sum-product exponent is at
least $1$. Here the exponent is $\liminf_{n \to \infty} m(n)$, where $m(n)$ is the infimum of
$\log \max(|A+A|, |AA|) / \log |A|$ over all sets $A$ of $n$ real numbers, and $A+A$ and $AA$ are
the sumset and the product set of $A$.

Optimization Problems 84b lists this bound as trivial, since $|A+A| \ge 2|A| - 1$.

Source: Paul Erdős and Endre Szemerédi, On sums and products of
integers, Studies in Pure Mathematics (1983), 213-218,
https://doi.org/10.1007/978-3-0348-5438-2_19; György Elekes, On the number of sums and products,
Acta Arithmetica 81 (1997), no. 4, 365-367, https://doi.org/10.4064/aa-81-4-365-367; József
Solymosi, On the number of sums and products, Bulletin of the London Mathematical Society 37
(2005), no. 4, 491-494, https://doi.org/10.1112/S0024609305004261; József Solymosi, Bounding
multiplicative energy by the sumset, Advances in Mathematics 222 (2009), no. 2, 402-408,
https://doi.org/10.1016/j.aim.2009.04.006; Misha Rudnev and Sophie Stevens, An update on the
sum-product problem, Mathematical Proceedings of the Cambridge Philosophical Society 173 (2022),
no. 2, 411-430, https://arxiv.org/abs/2005.11145; Thomas F. Bloom, A history of the sum-product
problem, https://thomasbloom.org/notes/sumproduct.html; Adam Cushman, A note on the sum-product
problem and the convex sumset problem, arXiv:2512.13849 (2025),
https://arxiv.org/abs/2512.13849; Thomas F. Bloom, Will Sawin, Carl Schildkraut, and Dmitrii
Zhelezov, The sum-product conjecture is false for real numbers, arXiv:2605.28781 (2026),
https://arxiv.org/abs/2605.28781; Optimization Problems, record 84b, Sum-product exponent for
the reals, tables of known upper and lower bounds (source commit
2c1968cd520b60f1cf3cf50749f7285e800e4e15),
https://github.com/teorth/optimizationproblems/blob/2c1968cd520b60f1cf3cf50749f7285e800e4e15/constants/84b.md.
Moved from `OpenConjectures/Combinatorics/RealSumProductExponent`.
-/
public theorem_wanted trivialLowerBound_holds : trivialLowerBound

/--
**Elekes's lower bound for the real sum-product exponent.** For a finite set $A \subset \mathbb{R}$
write $A + A$ and $AA$ for the sets of all sums $a + b$ and all products $ab$ with $a, b \in A$,
and let the real sum-product exponent $C_{84b}$ be the limit inferior, as $n \to \infty$, of the
least value of $\log \max(|A + A|, |AA|) / \log n$ over sets $A \subset \mathbb{R}$ with
$|A| = n$. Then $C_{84b} \ge 5/4$.

Elekes proved, using the Szemerédi–Trotter theorem, that $\max(|A + A|, |AA|) \gg |A|^{5/4}$ for
finite sets $A \subset \mathbb{R}$.

Source: Paul Erdős and Endre Szemerédi, On sums and products of integers,
Studies in Pure Mathematics (1983), 213-218, https://doi.org/10.1007/978-3-0348-5438-2_19;
György Elekes, On the number of sums and products, Acta Arithmetica 81 (1997), no. 4, 365-367,
https://doi.org/10.4064/aa-81-4-365-367; József Solymosi, On the number of sums and products,
Bulletin of the London Mathematical Society 37 (2005), no. 4, 491-494,
https://doi.org/10.1112/S0024609305004261; József Solymosi, Bounding multiplicative energy by
the sumset, Advances in Mathematics 222 (2009), no. 2, 402-408,
https://doi.org/10.1016/j.aim.2009.04.006; Misha Rudnev and Sophie Stevens, An update on the
sum-product problem, Mathematical Proceedings of the Cambridge Philosophical Society 173 (2022),
no. 2, 411-430, https://arxiv.org/abs/2005.11145; Thomas F. Bloom, A history of the sum-product
problem, https://thomasbloom.org/notes/sumproduct.html; Adam Cushman, A note on the sum-product
problem and the convex sumset problem, arXiv:2512.13849 (2025),
https://arxiv.org/abs/2512.13849; Thomas F. Bloom, Will Sawin, Carl Schildkraut, and Dmitrii
Zhelezov, The sum-product conjecture is false for real numbers, arXiv:2605.28781 (2026),
https://arxiv.org/abs/2605.28781; Optimization Problems, record 84b, Sum-product exponent for
the reals, tables of known upper and lower bounds (source commit
2c1968cd520b60f1cf3cf50749f7285e800e4e15),
https://github.com/teorth/optimizationproblems/blob/2c1968cd520b60f1cf3cf50749f7285e800e4e15/constants/84b.md.
Moved from `OpenConjectures/Combinatorics/RealSumProductExponent`.
-/
public theorem_wanted elekesLowerBound_holds : elekesLowerBound

/--
**Solymosi's $14/11$ lower bound for the real sum-product exponent.** Let $C$ be the real
sum-product exponent: the limit inferior, as $n \to \infty$, of the least value of
$\log \max(|A + A|, |AA|) / \log |A|$ over $n$-element sets $A \subset \mathbb{R}$, where
$A + A$ and $AA$ are the sets of sums $a + b$ and products $ab$ of elements $a, b \in A$. Then
$C \ge 14/11$.

Optimization Problems 84b lists the lower bound $14/11$ [So05] (Solymosi, Bull. London Math.
Soc. 37 (2005)); Bloom's history lists Solymosi 2005 with exponent $1 + 3/11$.

Source: Paul Erdős and Endre Szemerédi, On sums and products of integers,
Studies in Pure Mathematics (1983), 213-218, https://doi.org/10.1007/978-3-0348-5438-2_19;
György Elekes, On the number of sums and products, Acta Arithmetica 81 (1997), no. 4, 365-367,
https://doi.org/10.4064/aa-81-4-365-367; József Solymosi, On the number of sums and products,
Bulletin of the London Mathematical Society 37 (2005), no. 4, 491-494,
https://doi.org/10.1112/S0024609305004261; József Solymosi, Bounding multiplicative energy by
the sumset, Advances in Mathematics 222 (2009), no. 2, 402-408,
https://doi.org/10.1016/j.aim.2009.04.006; Misha Rudnev and Sophie Stevens, An update on the
sum-product problem, Mathematical Proceedings of the Cambridge Philosophical Society 173 (2022),
no. 2, 411-430, https://arxiv.org/abs/2005.11145; Thomas F. Bloom, A history of the sum-product
problem, https://thomasbloom.org/notes/sumproduct.html; Adam Cushman, A note on the sum-product
problem and the convex sumset problem, arXiv:2512.13849 (2025),
https://arxiv.org/abs/2512.13849; Thomas F. Bloom, Will Sawin, Carl Schildkraut, and Dmitrii
Zhelezov, The sum-product conjecture is false for real numbers, arXiv:2605.28781 (2026),
https://arxiv.org/abs/2605.28781; Optimization Problems, record 84b, Sum-product exponent for
the reals, tables of known upper and lower bounds (source commit
2c1968cd520b60f1cf3cf50749f7285e800e4e15),
https://github.com/teorth/optimizationproblems/blob/2c1968cd520b60f1cf3cf50749f7285e800e4e15/constants/84b.md.
Moved from `OpenConjectures/Combinatorics/RealSumProductExponent`.
-/
public theorem_wanted solymosiFourteenEleventhsLowerBound_holds : solymosiFourteenEleventhsLowerBound

/--
**Solymosi's $4/3$ lower bound for the real sum-product exponent.** Let $C$ be the real
sum-product exponent: the limit inferior, as $n \to \infty$, of the least value of
$\log \max(|A + A|, |AA|) / \log |A|$ over $n$-element sets $A \subset \mathbb{R}$, where
$A + A$ and $AA$ are the sets of sums $a + b$ and products $ab$ of elements $a, b \in A$. Then
$C \ge 4/3$.

Optimization Problems 84b lists the lower bound $4/3$ [So09] (Solymosi, Adv. Math. 222 (2009));
Bloom's history lists Solymosi 2009 with exponent $1 + 1/3$.

Source: Paul Erdős and Endre Szemerédi, On sums and products of integers, Studies in Pure
Mathematics (1983), 213-218, https://doi.org/10.1007/978-3-0348-5438-2_19; György Elekes, On the
number of sums and products, Acta Arithmetica 81 (1997), no. 4, 365-367,
https://doi.org/10.4064/aa-81-4-365-367; József Solymosi, On the number of sums and products,
Bulletin of the London Mathematical Society 37 (2005), no. 4, 491-494,
https://doi.org/10.1112/S0024609305004261; József Solymosi, Bounding multiplicative energy by
the sumset, Advances in Mathematics 222 (2009), no. 2, 402-408,
https://doi.org/10.1016/j.aim.2009.04.006; Misha Rudnev and Sophie Stevens, An update on the
sum-product problem, Mathematical Proceedings of the Cambridge Philosophical Society 173 (2022),
no. 2, 411-430, https://arxiv.org/abs/2005.11145; Thomas F. Bloom, A history of the sum-product
problem, https://thomasbloom.org/notes/sumproduct.html; Adam Cushman, A note on the sum-product
problem and the convex sumset problem, arXiv:2512.13849 (2025),
https://arxiv.org/abs/2512.13849; Thomas F. Bloom, Will Sawin, Carl Schildkraut, and Dmitrii
Zhelezov, The sum-product conjecture is false for real numbers, arXiv:2605.28781 (2026),
https://arxiv.org/abs/2605.28781; Optimization Problems, record 84b, Sum-product exponent for
the reals, tables of known upper and lower bounds (source commit
2c1968cd520b60f1cf3cf50749f7285e800e4e15),
https://github.com/teorth/optimizationproblems/blob/2c1968cd520b60f1cf3cf50749f7285e800e4e15/constants/84b.md.
Moved from `OpenConjectures/Combinatorics/RealSumProductExponent`.
-/
public theorem_wanted solymosiFourThirdsLowerBound_holds : solymosiFourThirdsLowerBound

/--
**Rudnev–Stevens lower bound for the real sum-product exponent.** Let $C$ be the real
sum-product exponent: the limit inferior, as $n \to \infty$, of the least value of
$\log \max(|A + A|, |AA|) / \log |A|$ over $n$-element sets $A \subset \mathbb{R}$, where
$A + A$ and $AA$ are the sets of sums $a + b$ and products $ab$ of elements $a, b \in A$. Then
$C \ge 1558/1167$.

Rudnev and Stevens (arXiv:2005.11145, abstract) prove
$\max(|A + A|, |AA|) \ge |A|^{4/3 + 2/1167 - o(1)}$ for finite $A \subset \mathbb{R}$, and
$4/3 + 2/1167 = 1558/1167$; Optimization Problems 84b lists this bound [RuSt22].

Source: Paul Erdős and Endre Szemerédi,
On sums and products of integers, Studies in Pure Mathematics (1983), 213-218,
https://doi.org/10.1007/978-3-0348-5438-2_19; György Elekes, On the number of sums and products,
Acta Arithmetica 81 (1997), no. 4, 365-367, https://doi.org/10.4064/aa-81-4-365-367; József
Solymosi, On the number of sums and products, Bulletin of the London Mathematical Society 37
(2005), no. 4, 491-494, https://doi.org/10.1112/S0024609305004261; József Solymosi, Bounding
multiplicative energy by the sumset, Advances in Mathematics 222 (2009), no. 2, 402-408,
https://doi.org/10.1016/j.aim.2009.04.006; Misha Rudnev and Sophie Stevens, An update on the
sum-product problem, Mathematical Proceedings of the Cambridge Philosophical Society 173 (2022),
no. 2, 411-430, https://arxiv.org/abs/2005.11145; Thomas F. Bloom, A history of the sum-product
problem, https://thomasbloom.org/notes/sumproduct.html; Adam Cushman, A note on the sum-product
problem and the convex sumset problem, arXiv:2512.13849 (2025),
https://arxiv.org/abs/2512.13849; Thomas F. Bloom, Will Sawin, Carl Schildkraut, and Dmitrii
Zhelezov, The sum-product conjecture is false for real numbers, arXiv:2605.28781 (2026),
https://arxiv.org/abs/2605.28781; Optimization Problems, record 84b, Sum-product exponent for
the reals, tables of known upper and lower bounds (source commit
2c1968cd520b60f1cf3cf50749f7285e800e4e15),
https://github.com/teorth/optimizationproblems/blob/2c1968cd520b60f1cf3cf50749f7285e800e4e15/constants/84b.md.
Moved from `OpenConjectures/Combinatorics/RealSumProductExponent`.
-/
public theorem_wanted rudnevStevensLowerBound_holds : rudnevStevensLowerBound

/--
**Bloom's lower bound for the real sum-product exponent.** The real sum-product exponent $C$ is
at least $1270/951$. Here, for a finite set $A \subset \mathbb{R}$, $A + A$ and $A \cdot A$ are
the sets of sums $a + b$ and products $ab$ with $a, b \in A$, and
$M(A) = \max(|A + A|, |A \cdot A|)$; for $n \ge 2$, $m(n)$ is the minimum of
$\log M(A) / \log |A|$ over all $A \subset \mathbb{R}$ with $|A| = n$; and
$C = \liminf_{n \to \infty} m(n)$.

Optimization Problems 84b lists this lower bound as Bloom 2025; Bloom's history of the
sum-product problem attributes it to Bloom, Control and its applications in additive
combinatorics. It also follows from Cushman's larger lower bound $4/3 + 10/4407$.

Source: Paul Erdős and Endre Szemerédi, On sums and products of integers, Studies in Pure
Mathematics (1983), 213-218, https://doi.org/10.1007/978-3-0348-5438-2_19; György Elekes, On the
number of sums and products, Acta Arithmetica 81 (1997), no. 4, 365-367,
https://doi.org/10.4064/aa-81-4-365-367; József Solymosi, On the number of sums and products,
Bulletin of the London Mathematical Society 37 (2005), no. 4, 491-494,
https://doi.org/10.1112/S0024609305004261; József Solymosi, Bounding multiplicative energy by
the sumset, Advances in Mathematics 222 (2009), no. 2, 402-408,
https://doi.org/10.1016/j.aim.2009.04.006; Misha Rudnev and Sophie Stevens, An update on the
sum-product problem, Mathematical Proceedings of the Cambridge Philosophical Society 173 (2022),
no. 2, 411-430, https://arxiv.org/abs/2005.11145; Thomas F. Bloom, A history of the sum-product
problem, https://thomasbloom.org/notes/sumproduct.html; Adam Cushman, A note on the sum-product
problem and the convex sumset problem, arXiv:2512.13849 (2025),
https://arxiv.org/abs/2512.13849; Thomas F. Bloom, Will Sawin, Carl Schildkraut, and Dmitrii
Zhelezov, The sum-product conjecture is false for real numbers, arXiv:2605.28781 (2026),
https://arxiv.org/abs/2605.28781; Optimization Problems, record 84b, Sum-product exponent for
the reals, tables of known upper and lower bounds (source commit
2c1968cd520b60f1cf3cf50749f7285e800e4e15),
https://github.com/teorth/optimizationproblems/blob/2c1968cd520b60f1cf3cf50749f7285e800e4e15/constants/84b.md.
Moved from `OpenConjectures/Combinatorics/RealSumProductExponent`.
-/
public theorem_wanted bloomLowerBound_holds : bloomLowerBound

/--
**Cushman's lower bound for the real sum-product exponent.** The real sum-product exponent $C$ is
at least $4/3 + 10/4407$. Here, for a finite set $A \subset \mathbb{R}$, $A + A$ and $A \cdot A$
are the sets of sums $a + b$ and products $ab$ with $a, b \in A$, and
$M(A) = \max(|A + A|, |A \cdot A|)$; for $n \ge 2$, $m(n)$ is the minimum of
$\log M(A) / \log |A|$ over all $A \subset \mathbb{R}$ with $|A| = n$; and
$C = \liminf_{n \to \infty} m(n)$.

Cushman (arXiv:2512.13849) proves $M(A) \gg_\varepsilon |A|^{4/3 + 10/4407 - \varepsilon}$ for
every finite $A \subset \mathbb{R}$; Optimization Problems 84b lists this as the current record.

Source: Paul Erdős and Endre Szemerédi, On sums and products of integers, Studies in Pure
Mathematics (1983), 213-218, https://doi.org/10.1007/978-3-0348-5438-2_19; György Elekes, On the
number of sums and products, Acta Arithmetica 81 (1997), no. 4, 365-367,
https://doi.org/10.4064/aa-81-4-365-367; József Solymosi, On the number of sums and products,
Bulletin of the London Mathematical Society 37 (2005), no. 4, 491-494,
https://doi.org/10.1112/S0024609305004261; József Solymosi, Bounding multiplicative energy by
the sumset, Advances in Mathematics 222 (2009), no. 2, 402-408,
https://doi.org/10.1016/j.aim.2009.04.006; Misha Rudnev and Sophie Stevens, An update on the
sum-product problem, Mathematical Proceedings of the Cambridge Philosophical Society 173 (2022),
no. 2, 411-430, https://arxiv.org/abs/2005.11145; Thomas F. Bloom, A history of the sum-product
problem, https://thomasbloom.org/notes/sumproduct.html; Adam Cushman, A note on the sum-product
problem and the convex sumset problem, arXiv:2512.13849 (2025),
https://arxiv.org/abs/2512.13849; Thomas F. Bloom, Will Sawin, Carl Schildkraut, and Dmitrii
Zhelezov, The sum-product conjecture is false for real numbers, arXiv:2605.28781 (2026),
https://arxiv.org/abs/2605.28781; Optimization Problems, record 84b, Sum-product exponent for
the reals, tables of known upper and lower bounds (source commit
2c1968cd520b60f1cf3cf50749f7285e800e4e15),
https://github.com/teorth/optimizationproblems/blob/2c1968cd520b60f1cf3cf50749f7285e800e4e15/constants/84b.md.
Moved from `OpenConjectures/Combinatorics/RealSumProductExponent`.
-/
public theorem_wanted cushmanCurrentLowerBound_holds : cushmanCurrentLowerBound

end MathlibExt.Combinatorics.RealSumProductExponentWanted
