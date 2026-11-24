/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Topology.Order.Monotone
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import MathlibExt.Combinatorics.SolymosiSumProduct

/-!
# Optimization Problem 84b: real sum-product exponent

Source: `optimizationproblems/constants/84b.md` at commit
`2c1968cd520b60f1cf3cf50749f7285e800e4e15`, SHA-256
`896f56513ea43dfaba160dde68ad73e49f0894150fea48922b8cece636fdeac8`.

The historical equality `C₈₄ᵦ = 2` was refuted in May 2026. The source's
unverified `1.999281` forum row and its approximate-only lower rows are
recorded in metadata, not promoted to exact Lean bounds.
-/

@[expose] public section

open scoped Pointwise

namespace MathlibExt.Combinatorics.RealSumProductExponentWanted

noncomputable section

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

open Filter

private theorem one_le_sumProductMaxCard {A : Finset ℝ} (hA : A.Nonempty) :
    1 ≤ sumProductMaxCard A :=
  (Finset.one_le_card.mpr hA).trans
    ((Finset.card_le_card_add_left hA).trans (le_max_left _ _))

private theorem card_rpow_le_maxCard_iff {A : Finset ℝ} (hA : 2 ≤ A.card) (t : ℝ) :
    (A.card : ℝ) ^ t ≤ sumProductMaxCard A ↔ t ≤ sumProductRatio A := by
  have hcard : (1 : ℝ) < A.card := by exact_mod_cast hA
  have hmax : 0 < sumProductMaxCard A :=
    one_le_sumProductMaxCard (Finset.card_pos.mp (by omega))
  rw [Real.rpow_le_iff_le_log (zero_lt_one.trans hcard) (by exact_mod_cast hmax),
    sumProductRatio, le_div_iff₀ (Real.log_pos hcard)]

private theorem hasUniformSumProductLowerGrowth_exponent :
    HasUniformSumProductLowerGrowth sumProductExponent := by
  intro ε hε
  let t := sumProductExponent - ε
  have ht : t < sumProductExponent := sub_lt_self _ hε
  have htail := eventually_lt_of_lt_liminf ht sumProductLevelMinimum_isBoundedUnder_ge
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((eventually_ge_atTop 2).and htail)
  -- Below the cutoff, |A|^t is at most B and the sumset is nonempty.
  let B := (N : ℝ) ^ max t 0
  have hNpos : (1 : ℝ) ≤ N := by exact_mod_cast (one_le_two.trans (hN N le_rfl).1)
  have hB : 1 ≤ B := Real.one_le_rpow hNpos (le_max_right _ _)
  refine ⟨B⁻¹, inv_pos.mpr (zero_lt_one.trans_le hB), ?_⟩
  intro A hA
  have hcard : (1 : ℝ) ≤ A.card := by exact_mod_cast Finset.one_le_card.mpr hA
  by_cases hn : N ≤ A.card
  · obtain ⟨h₂, hmin⟩ := hN A.card hn
    apply (mul_le_of_le_one_left (Real.rpow_nonneg (by positivity) t)
      (inv_le_one_of_one_le₀ hB)).trans
    apply (card_rpow_le_maxCard_iff h₂ t).2
    exact hmin.le.trans ((sumProductLevelMinimum_isLeast A.card).2 ⟨A, rfl, rfl⟩)
  · have hmax : (1 : ℝ) ≤ sumProductMaxCard A := by exact_mod_cast one_le_sumProductMaxCard hA
    refine le_trans ?_ hmax
    apply (inv_mul_le_one₀ (zero_lt_one.trans_le hB)).2
    exact (Real.rpow_le_rpow_of_exponent_le hcard (le_max_left t 0)).trans
      (Real.rpow_le_rpow (by positivity) (by exact_mod_cast le_of_not_ge hn) (le_max_right _ _))

private theorem le_sumProductExponent_of_uniformGrowth {s : ℝ}
    (hs : HasUniformSumProductLowerGrowth s) : s ≤ sumProductExponent := by
  apply (le_liminf_iff' sumProductLevelMinimum_isBoundedUnder_le.isCoboundedUnder_ge
    sumProductLevelMinimum_isBoundedUnder_ge).2
  intro t ht
  let δ := (s - t) / 2
  have hδ : 0 < δ := half_pos (sub_pos.mpr ht)
  obtain ⟨K, hK, hbound⟩ := hs δ hδ
  -- Eventually n^δ absorbs the reciprocal of the uniform constant.
  have hgrow : Tendsto (fun n : ℕ => (n : ℝ) ^ δ) atTop atTop :=
    (tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 2, hgrow.eventually_ge_atTop K⁻¹] with n hn hlarge
  obtain ⟨A, rfl, hmin⟩ := (sumProductLevelMinimum_isLeast n).1
  rw [hmin, ← card_rpow_le_maxCard_iff hn]
  have hA : A.Nonempty := Finset.card_pos.mp (by omega)
  have hpos : (0 : ℝ) < A.card := by exact_mod_cast Finset.card_pos.mpr hA
  calc
    (A.card : ℝ) ^ t ≤ (K * (A.card : ℝ) ^ δ) * (A.card : ℝ) ^ t :=
      le_mul_of_one_le_left (Real.rpow_nonneg hpos.le _) ((inv_le_iff_one_le_mul₀' hK).1 hlarge)
    _ = K * (A.card : ℝ) ^ (s - δ) := by
      rw [mul_assoc, ← Real.rpow_add hpos, show δ + t = s - δ by dsimp [δ]; ring]
    _ ≤ sumProductMaxCard A := hbound A hA

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
public theorem epsilonUniformLowerGrowthCharacterization_holds :
    epsilonUniformLowerGrowthCharacterization :=
  ⟨hasUniformSumProductLowerGrowth_exponent, fun _ hs => le_sumProductExponent_of_uniformGrowth hs⟩

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
theorem erdosSzemerediHistoricalUpperBound_holds : erdosSzemerediHistoricalUpperBound :=
  Filter.liminf_le_of_frequently_le
    (eventually_sumProductLevelMinimum_mem_Icc.mono fun _ hn => hn.2).frequently
    sumProductLevelMinimum_isBoundedUnder_ge

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
public theorem trivialLowerBound_holds : trivialLowerBound := by
  change (1 : ℝ) ≤ Filter.liminf sumProductLevelMinimum Filter.atTop
  apply Filter.le_liminf_of_le sumProductLevelMinimum_isBoundedUnder_le.isCoboundedUnder_ge
  filter_upwards [Filter.eventually_ge_atTop 2] with n hn
  obtain ⟨A, hcard, hvalue⟩ := (sumProductLevelMinimum_isLeast n).1
  have hA : 2 ≤ A.card := hcard.symm ▸ hn
  have hAone : (1 : ℝ) < A.card := by exact_mod_cast hA
  have hAnonempty : A.Nonempty := Finset.card_pos.mp (Nat.zero_lt_two.trans_le hA)
  -- Translating A by any one of its elements already gives |A| distinct sums.
  have hsum : A.card ≤ (A + A).card := Finset.card_le_card_add_left hAnonempty
  have hmax : A.card ≤ sumProductMaxCard A := hsum.trans (Nat.le_max_left _ _)
  rw [hvalue, sumProductRatio, le_div_iff₀ (Real.log_pos hAone), one_mul]
  exact Real.log_le_log (zero_lt_one.trans hAone) (by exact_mod_cast hmax)

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
public theorem solymosiFourThirdsLowerBound_holds : solymosiFourThirdsLowerBound := by
  apply (le_liminf_iff' sumProductLevelMinimum_isBoundedUnder_le.isCoboundedUnder_ge
    sumProductLevelMinimum_isBoundedUnder_ge).2
  intro t ht
  -- The logarithmic loss in the finite estimate is absorbed by n^(4 - 3t).
  let δ := 4 - 3 * t
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have h₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog := ((isLittleO_log_rpow_atTop hδ).comp_tendsto tendsto_natCast_atTop_atTop).bound
    (show 0 < Real.log 2 / 1296 by positivity)
  filter_upwards [eventually_ge_atTop 2, hlog] with n hn hlog
  obtain ⟨A, rfl, hmin⟩ := (sumProductLevelMinimum_isLeast n).1
  rw [hmin, ← card_rpow_le_maxCard_iff hn]
  have hn' : (1 : ℝ) < A.card := by exact_mod_cast hn
  have hcard := zero_lt_one.trans hn'
  have hl : Real.log A.card ≤ Real.log 2 / 1296 * (A.card : ℝ) ^ δ := by
    simpa only [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg (Real.log_pos hn').le,
      abs_of_nonneg (Real.rpow_nonneg hcard.le δ)] using hlog
  let M : ℝ := sumProductMaxCard A
  have hs : ((A + A).card : ℝ) ≤ M := by
    dsimp [M, sumProductMaxCard]
    exact_mod_cast (le_max_left _ _)
  have hp : ((A * A).card : ℝ) ≤ M := by
    dsimp [M, sumProductMaxCard]
    exact_mod_cast (le_max_right _ _)
  change (A.card : ℝ) ^ t ≤ M
  apply le_of_pow_le_pow_left₀ (n := 3) (by decide) (by dsimp [M]; positivity)
  apply le_of_mul_le_mul_right (a := Real.log 2 * (A.card : ℝ) ^ δ) _ (by positivity)
  calc
    ((A.card : ℝ) ^ t) ^ 3 * (Real.log 2 * (A.card : ℝ) ^ δ) =
        Real.log 2 * (A.card : ℝ) ^ 4 := by
      rw [mul_left_comm, ← Real.rpow_mul_natCast hcard.le, ← Real.rpow_add hcard,
        show t * (3 : ℕ) + δ = (4 : ℝ) by dsimp [δ]; ring]
      norm_num
    _ ≤ _ := solymosi_sum_product A hn
    _ ≤ 1296 * M * M ^ 2 * (Real.log 2 / 1296 * (A.card : ℝ) ^ δ) := by gcongr
    _ = M ^ 3 * (Real.log 2 * (A.card : ℝ) ^ δ) := by ring

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

end MathlibExt.Combinatorics.RealSumProductExponentWanted
