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

/-- The cardinality of the larger of the pointwise sumset and product set. -/
def sumProductMaxCard (A : Finset ℝ) : ℕ :=
  max (A + A).card (A * A).card

/-- The normalized logarithmic sum-product growth of a finite real set. -/
def sumProductRatio (A : Finset ℝ) : ℝ :=
  Real.log (sumProductMaxCard A : ℝ) / Real.log (A.card : ℝ)

/-- All sum-product ratios attained by real finsets of cardinality `n`. -/
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

/-- The source's attained fixed-cardinality minimum. -/
def sumProductLevelMinimum (n : ℕ) : ℝ :=
  sInf (fixedCardinalityRatios n)

/-- The fixed-cardinality infimum is attained for every natural cardinality. -/
theorem sumProductLevelMinimum_isLeast (n : ℕ) :
    IsLeast (fixedCardinalityRatios n) (sumProductLevelMinimum n) := by
  simpa only [sumProductLevelMinimum] using
    (fixedCardinalityRatios_finite n).isClosed.isLeast_csInf
      (fixedCardinalityRatios_nonempty n)
      (fixedCardinalityRatios_bddBelow n)

/-- Every nonempty finite real set has nonnegative normalized growth. -/
theorem sumProductRatio_nonneg (A : Finset ℝ) (hA : A.Nonempty) :
    0 ≤ sumProductRatio A := by
  have hone : 1 ≤ A.card := Finset.one_le_card.mpr hA
  have hsum : A.card ≤ (A + A).card :=
    Finset.card_le_card_add_left hA
  have hmax : 1 ≤ sumProductMaxCard A := by
    exact hone.trans (hsum.trans (Nat.le_max_left _ _))
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast hmax))
    (Real.log_nonneg (by exact_mod_cast hone))

/-- At cardinality at least two, normalized growth is at most two. -/
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

/-- The fixed-cardinality minima are nonnegative at positive levels. -/
theorem sumProductLevelMinimum_nonneg (n : ℕ) (hn : 0 < n) :
    0 ≤ sumProductLevelMinimum n := by
  rcases (sumProductLevelMinimum_isLeast n).1 with ⟨A, hcard, hvalue⟩
  rw [hvalue]
  apply sumProductRatio_nonneg
  exact Finset.card_pos.mp (hcard.symm ▸ hn)

/-- The fixed-cardinality minima are at most two from level two onward. -/
theorem sumProductLevelMinimum_le_two (n : ℕ) (hn : 2 ≤ n) :
    sumProductLevelMinimum n ≤ 2 := by
  let A : Finset ℝ :=
    (Finset.range n).map (Nat.castEmbedding : ℕ ↪ ℝ)
  have hcard : A.card = n := by simp [A]
  have hmem : sumProductRatio A ∈ fixedCardinalityRatios n :=
    ⟨A, hcard, rfl⟩
  exact ((sumProductLevelMinimum_isLeast n).2 hmem).trans
    (sumProductRatio_le_two A (hcard.symm ▸ hn))

/-- Eventually, all fixed-cardinality minima lie in the interval `[0, 2]`. -/
theorem eventually_sumProductLevelMinimum_mem_Icc :
    ∀ᶠ n : ℕ in Filter.atTop,
      sumProductLevelMinimum n ∈ Set.Icc (0 : ℝ) 2 := by
  filter_upwards [Filter.eventually_ge_atTop 2] with n hn
  exact ⟨sumProductLevelMinimum_nonneg n (Nat.zero_lt_two.trans_le hn),
    sumProductLevelMinimum_le_two n hn⟩

/-- The level-minimum sequence is eventually bounded above. -/
theorem sumProductLevelMinimum_isBoundedUnder_le :
    Filter.atTop.IsBoundedUnder (· ≤ ·) sumProductLevelMinimum :=
  Filter.isBoundedUnder_of_eventually_le
    (eventually_sumProductLevelMinimum_mem_Icc.mono fun _ hn => hn.2)

/-- The level-minimum sequence is eventually bounded below. -/
theorem sumProductLevelMinimum_isBoundedUnder_ge :
    Filter.atTop.IsBoundedUnder (· ≥ ·) sumProductLevelMinimum :=
  Filter.isBoundedUnder_of_eventually_ge
    (eventually_sumProductLevelMinimum_mem_Icc.mono fun _ hn => hn.1)

/-- The real sum-product exponent: the real liminf of attained level minima. -/
def sumProductExponent : ℝ :=
  Filter.liminf sumProductLevelMinimum Filter.atTop

/-- The totalized levels `n = 0, 1` do not affect the exponent. -/
theorem sumProductExponent_eq_liminf_add_two :
    sumProductExponent =
      Filter.liminf (fun n : ℕ => sumProductLevelMinimum (n + 2)) Filter.atTop :=
  (Filter.liminf_nat_add sumProductLevelMinimum 2).symm

/-- Uniform lower growth with one positive constant depending on `ε`, not on `A`.
The standard nonempty-set convention avoids assigning mathematical meaning to
`0 ^ (s - ε)` when `ε = s`; singleton sets remain included. -/
def HasUniformSumProductLowerGrowth (s : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ K : ℝ, 0 < K ∧
      ∀ A : Finset ℝ,
        A.Nonempty →
          K * Real.rpow (A.card : ℝ) (s - ε) ≤ (sumProductMaxCard A : ℝ)

/-- The source's equivalent characterization: the exponent is the largest uniform growth rate. -/
def epsilonUniformLowerGrowthCharacterization : Prop :=
  IsGreatest {s : ℝ | HasUniformSumProductLowerGrowth s} sumProductExponent

/-- The historical Erdős--Szemerédi conjecture for real sets. -/
def erdosSzemerediHistoricalConjecture : Prop :=
  sumProductExponent = 2

/-- The May 2026 refutation of the historical real-set conjecture. -/
def bloomSawinSchildkrautZhelezovRefutation : Prop :=
  sumProductExponent < 2

/-- The historical upper bound `C₈₄ᵦ ≤ 2`. -/
def erdosSzemerediHistoricalUpperBound : Prop :=
  sumProductExponent ≤ 2

/-- The qualitative 2026 improvement by one absolute positive constant. -/
def bloomSawinSchildkrautZhelezovUpperBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ sumProductExponent ≤ 2 - c

/-- The nonoptimized explicit upper bound from the quantified version of the 2026 argument. -/
def bloomSawinSchildkrautZhelezovNumericalUpperBound : Prop :=
  sumProductExponent ≤ (199999913 : ℝ) / 100000000

/-- The trivial exact lower bound. -/
def trivialLowerBound : Prop :=
  (1 : ℝ) ≤ sumProductExponent

/-- Elekes's exact lower bound. -/
def elekesLowerBound : Prop :=
  (5 : ℝ) / 4 ≤ sumProductExponent

/-- Solymosi's 2005 exact lower bound. -/
def solymosiFourteenEleventhsLowerBound : Prop :=
  (14 : ℝ) / 11 ≤ sumProductExponent

/-- Solymosi's 2009 exact lower bound. -/
def solymosiFourThirdsLowerBound : Prop :=
  (4 : ℝ) / 3 ≤ sumProductExponent

/-- Rudnev and Stevens's exact lower bound. -/
def rudnevStevensLowerBound : Prop :=
  (1558 : ℝ) / 1167 ≤ sumProductExponent

/-- Bloom's source-reported exact lower bound. -/
def bloomLowerBound : Prop :=
  (1270 : ℝ) / 951 ≤ sumProductExponent

/-- Cushman's source-reported current exact lower endpoint. -/
def cushmanCurrentLowerBound : Prop :=
  (4 : ℝ) / 3 + (10 : ℝ) / 4407 ≤ sumProductExponent

end

/--
Resolved false: Every registered target is settled. The historical Erdős–Szemerédi conjecture
C84b = 2 for real sets is refuted: Bloom, Sawin, Schildkraut and Zhelezov (arXiv:2605.28781,
2026) construct arbitrarily large A ⊂ ℝ with max(|A+A|, |AA|) ≤ |A|^(2−c), as recorded on
erdosproblems.com/52 and in Optimization Problems 84b. The other registered targets hold by the
sources that list records: the ε-uniform characterization of C84b, the upper bounds 2, 2 − c and
1.99999913 (the last from the authors' sketched explicit version of their argument), and the
lower bounds 1, 5/4, 14/11, 4/3, 1558/1167, 1270/951 and 4/3 + 10/4407. The exact value of C84b
remains open and is not a registered target; the integer sum-product question (Erdős Problem 52)
is open and not formalized here. This target holds: Optimization Problems 84b gives this as an
equivalent definition of C84b: the largest s with max(|A+A|, |AA|) >>_ε |A|^(s-ε) for every ε >
0 and every finite A ⊂ ℝ. Source: Paul Erdős and Endre Szemerédi, On sums and products of
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
Resolved false: Every registered target is settled. The historical Erdős–Szemerédi conjecture
C84b = 2 for real sets is refuted: Bloom, Sawin, Schildkraut and Zhelezov (arXiv:2605.28781,
2026) construct arbitrarily large A ⊂ ℝ with max(|A+A|, |AA|) ≤ |A|^(2−c), as recorded on
erdosproblems.com/52 and in Optimization Problems 84b. The other registered targets hold by the
sources that list records: the ε-uniform characterization of C84b, the upper bounds 2, 2 − c and
1.99999913 (the last from the authors' sketched explicit version of their argument), and the
lower bounds 1, 5/4, 14/11, 4/3, 1558/1167, 1270/951 and 4/3 + 10/4407. The exact value of C84b
remains open and is not a registered target; the integer sum-product question (Erdős Problem 52)
is open and not formalized here. This target is refuted: Bloom, Sawin, Schildkraut and Zhelezov
(arXiv:2605.28781, abstract): arbitrarily large A ⊂ ℝ with max(|A+A|, |AA|) ≤ |A|^(2-c) for an
absolute c > 0, so C84b ≤ 2 - c < 2; recorded as the disproof in Optimization Problems 84b and
on erdosproblems.com/52. Source: Paul Erdős and Endre Szemerédi, On sums and products of
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
Resolved false: Every registered target is settled. The historical Erdős–Szemerédi conjecture
C84b = 2 for real sets is refuted: Bloom, Sawin, Schildkraut and Zhelezov (arXiv:2605.28781,
2026) construct arbitrarily large A ⊂ ℝ with max(|A+A|, |AA|) ≤ |A|^(2−c), as recorded on
erdosproblems.com/52 and in Optimization Problems 84b. The other registered targets hold by the
sources that list records: the ε-uniform characterization of C84b, the upper bounds 2, 2 − c and
1.99999913 (the last from the authors' sketched explicit version of their argument), and the
lower bounds 1, 5/4, 14/11, 4/3, 1558/1167, 1270/951 and 4/3 + 10/4407. The exact value of C84b
remains open and is not a registered target; the integer sum-product question (Erdős Problem 52)
is open and not formalized here. This target holds: Bloom, Sawin, Schildkraut and Zhelezov
(arXiv:2605.28781, abstract): max(|A+A|, |AA|) ≤ |A|^(2-c) for arbitrarily large real A and an
absolute c > 0, which gives C84b < 2; Optimization Problems 84b records that they 'showed C84b <
2'. Source: Paul Erdős and Endre Szemerédi, On sums and products of integers, Studies in Pure
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
Resolved false: Every registered target is settled. The historical Erdős–Szemerédi conjecture
C84b = 2 for real sets is refuted: Bloom, Sawin, Schildkraut and Zhelezov (arXiv:2605.28781,
2026) construct arbitrarily large A ⊂ ℝ with max(|A+A|, |AA|) ≤ |A|^(2−c), as recorded on
erdosproblems.com/52 and in Optimization Problems 84b. The other registered targets hold by the
sources that list records: the ε-uniform characterization of C84b, the upper bounds 2, 2 − c and
1.99999913 (the last from the authors' sketched explicit version of their argument), and the
lower bounds 1, 5/4, 14/11, 4/3, 1558/1167, 1270/951 and 4/3 + 10/4407. The exact value of C84b
remains open and is not a registered target; the integer sum-product question (Erdős Problem 52)
is open and not formalized here. This target holds: Optimization Problems 84b, upper bound 2
[ErSz83]; it also follows from max(|A+A|, |AA|) ≤ |A|^2, as the entry's own lemma
sumProductLevelMinimum_le_two proves. Source: Paul Erdős and Endre Szemerédi, On sums and
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
Resolved false: Every registered target is settled. The historical Erdős–Szemerédi conjecture
C84b = 2 for real sets is refuted: Bloom, Sawin, Schildkraut and Zhelezov (arXiv:2605.28781,
2026) construct arbitrarily large A ⊂ ℝ with max(|A+A|, |AA|) ≤ |A|^(2−c), as recorded on
erdosproblems.com/52 and in Optimization Problems 84b. The other registered targets hold by the
sources that list records: the ε-uniform characterization of C84b, the upper bounds 2, 2 − c and
1.99999913 (the last from the authors' sketched explicit version of their argument), and the
lower bounds 1, 5/4, 14/11, 4/3, 1558/1167, 1270/951 and 4/3 + 10/4407. The exact value of C84b
remains open and is not a registered target; the integer sum-product question (Erdős Problem 52)
is open and not formalized here. This target holds: Bloom, Sawin, Schildkraut and Zhelezov
(arXiv:2605.28781, abstract): an absolute constant c > 0 with max(|A+A|, |AA|) ≤ |A|^(2-c) for
arbitrarily large real A, hence C84b ≤ 2 - c (Optimization Problems 84b, upper bound 2 - c).
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
Resolved false: Every registered target is settled. The historical Erdős–Szemerédi conjecture
C84b = 2 for real sets is refuted: Bloom, Sawin, Schildkraut and Zhelezov (arXiv:2605.28781,
2026) construct arbitrarily large A ⊂ ℝ with max(|A+A|, |AA|) ≤ |A|^(2−c), as recorded on
erdosproblems.com/52 and in Optimization Problems 84b. The other registered targets hold by the
sources that list records: the ε-uniform characterization of C84b, the upper bounds 2, 2 − c and
1.99999913 (the last from the authors' sketched explicit version of their argument), and the
lower bounds 1, 5/4, 14/11, 4/3, 1558/1167, 1270/951 and 4/3 + 10/4407. The exact value of C84b
remains open and is not a registered target; the integer sum-product question (Erdős Problem 52)
is open and not formalized here. This target holds: Bloom, Sawin, Schildkraut and Zhelezov,
Section 'Numerical estimates' of arXiv:2605.28781 (source TeX read): a sketch of the quantified
construction yields arbitrarily large A ⊂ ℝ with max(|A+A|, |AA|) ≤ |A|^(2-0.00000087); the
authors call the value non-optimized ('should not be taken too seriously, and can certainly be
improved'). Optimization Problems 84b lists it as the explicit upper bound 1.99999913. Source:
Paul Erdős and Endre Szemerédi, On sums and products of integers, Studies in Pure Mathematics
(1983), 213-218, https://doi.org/10.1007/978-3-0348-5438-2_19; György Elekes, On the number of
sums and products, Acta Arithmetica 81 (1997), no. 4, 365-367,
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
Resolved false: Every registered target is settled. The historical Erdős–Szemerédi conjecture
C84b = 2 for real sets is refuted: Bloom, Sawin, Schildkraut and Zhelezov (arXiv:2605.28781,
2026) construct arbitrarily large A ⊂ ℝ with max(|A+A|, |AA|) ≤ |A|^(2−c), as recorded on
erdosproblems.com/52 and in Optimization Problems 84b. The other registered targets hold by the
sources that list records: the ε-uniform characterization of C84b, the upper bounds 2, 2 − c and
1.99999913 (the last from the authors' sketched explicit version of their argument), and the
lower bounds 1, 5/4, 14/11, 4/3, 1558/1167, 1270/951 and 4/3 + 10/4407. The exact value of C84b
remains open and is not a registered target; the integer sum-product question (Erdős Problem 52)
is open and not formalized here. This target holds: Optimization Problems 84b, lower bound 1
(trivial, |A+A| ≥ 2|A| - 1). Source: Paul Erdős and Endre Szemerédi, On sums and products of
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
Resolved false: Every registered target is settled. The historical Erdős–Szemerédi conjecture
C84b = 2 for real sets is refuted: Bloom, Sawin, Schildkraut and Zhelezov (arXiv:2605.28781,
2026) construct arbitrarily large A ⊂ ℝ with max(|A+A|, |AA|) ≤ |A|^(2−c), as recorded on
erdosproblems.com/52 and in Optimization Problems 84b. The other registered targets hold by the
sources that list records: the ε-uniform characterization of C84b, the upper bounds 2, 2 − c and
1.99999913 (the last from the authors' sketched explicit version of their argument), and the
lower bounds 1, 5/4, 14/11, 4/3, 1558/1167, 1270/951 and 4/3 + 10/4407. The exact value of C84b
remains open and is not a registered target; the integer sum-product question (Erdős Problem 52)
is open and not formalized here. This target holds: Optimization Problems 84b, lower bound 5/4
[El97] (Elekes, Acta Arith. 81 (1997), via Szemerédi-Trotter); Bloom's history lists Elekes 1997
with exponent 1 + 1/4. Source: Paul Erdős and Endre Szemerédi, On sums and products of integers,
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
Resolved false: Every registered target is settled. The historical Erdős–Szemerédi conjecture
C84b = 2 for real sets is refuted: Bloom, Sawin, Schildkraut and Zhelezov (arXiv:2605.28781,
2026) construct arbitrarily large A ⊂ ℝ with max(|A+A|, |AA|) ≤ |A|^(2−c), as recorded on
erdosproblems.com/52 and in Optimization Problems 84b. The other registered targets hold by the
sources that list records: the ε-uniform characterization of C84b, the upper bounds 2, 2 − c and
1.99999913 (the last from the authors' sketched explicit version of their argument), and the
lower bounds 1, 5/4, 14/11, 4/3, 1558/1167, 1270/951 and 4/3 + 10/4407. The exact value of C84b
remains open and is not a registered target; the integer sum-product question (Erdős Problem 52)
is open and not formalized here. This target holds: Optimization Problems 84b, lower bound 14/11
[So05] (Solymosi, Bull. London Math. Soc. 37 (2005)); Bloom's history lists Solymosi 2005 with
exponent 1 + 3/11. Source: Paul Erdős and Endre Szemerédi, On sums and products of integers,
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
Resolved false: Every registered target is settled. The historical Erdős–Szemerédi conjecture
C84b = 2 for real sets is refuted: Bloom, Sawin, Schildkraut and Zhelezov (arXiv:2605.28781,
2026) construct arbitrarily large A ⊂ ℝ with max(|A+A|, |AA|) ≤ |A|^(2−c), as recorded on
erdosproblems.com/52 and in Optimization Problems 84b. The other registered targets hold by the
sources that list records: the ε-uniform characterization of C84b, the upper bounds 2, 2 − c and
1.99999913 (the last from the authors' sketched explicit version of their argument), and the
lower bounds 1, 5/4, 14/11, 4/3, 1558/1167, 1270/951 and 4/3 + 10/4407. The exact value of C84b
remains open and is not a registered target; the integer sum-product question (Erdős Problem 52)
is open and not formalized here. This target holds: Optimization Problems 84b, lower bound 4/3
[So09] (Solymosi, Adv. Math. 222 (2009)); Bloom's history lists Solymosi 2009 with exponent 1 +
1/3. Source: Paul Erdős and Endre Szemerédi, On sums and products of integers, Studies in Pure
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
Resolved false: Every registered target is settled. The historical Erdős–Szemerédi conjecture
C84b = 2 for real sets is refuted: Bloom, Sawin, Schildkraut and Zhelezov (arXiv:2605.28781,
2026) construct arbitrarily large A ⊂ ℝ with max(|A+A|, |AA|) ≤ |A|^(2−c), as recorded on
erdosproblems.com/52 and in Optimization Problems 84b. The other registered targets hold by the
sources that list records: the ε-uniform characterization of C84b, the upper bounds 2, 2 − c and
1.99999913 (the last from the authors' sketched explicit version of their argument), and the
lower bounds 1, 5/4, 14/11, 4/3, 1558/1167, 1270/951 and 4/3 + 10/4407. The exact value of C84b
remains open and is not a registered target; the integer sum-product question (Erdős Problem 52)
is open and not formalized here. This target holds: Rudnev and Stevens (arXiv:2005.11145,
abstract): max(|A+A|, |AA|) ≥ |A|^(4/3 + 2/1167 - o(1)) for finite A ⊂ ℝ, and 4/3 + 2/1167 =
1558/1167; Optimization Problems 84b lists it [RuSt22]. Source: Paul Erdős and Endre Szemerédi,
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
Resolved false: Every registered target is settled. The historical Erdős–Szemerédi conjecture
C84b = 2 for real sets is refuted: Bloom, Sawin, Schildkraut and Zhelezov (arXiv:2605.28781,
2026) construct arbitrarily large A ⊂ ℝ with max(|A+A|, |AA|) ≤ |A|^(2−c), as recorded on
erdosproblems.com/52 and in Optimization Problems 84b. The other registered targets hold by the
sources that list records: the ε-uniform characterization of C84b, the upper bounds 2, 2 − c and
1.99999913 (the last from the authors' sketched explicit version of their argument), and the
lower bounds 1, 5/4, 14/11, 4/3, 1558/1167, 1270/951 and 4/3 + 10/4407. The exact value of C84b
remains open and is not a registered target; the integer sum-product question (Erdős Problem 52)
is open and not formalized here. This target holds: Optimization Problems 84b, lower bound
1270/951 [Bl25]; Bloom's history of the sum-product problem lists it as Bloom 2025, Control and
its applications in additive combinatorics. It is also implied by the larger bound 4/3 + 10/4407
of Cushman. Source: Paul Erdős and Endre Szemerédi, On sums and products of integers, Studies in
Pure Mathematics (1983), 213-218, https://doi.org/10.1007/978-3-0348-5438-2_19; György Elekes,
On the number of sums and products, Acta Arithmetica 81 (1997), no. 4, 365-367,
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
Resolved false: Every registered target is settled. The historical Erdős–Szemerédi conjecture
C84b = 2 for real sets is refuted: Bloom, Sawin, Schildkraut and Zhelezov (arXiv:2605.28781,
2026) construct arbitrarily large A ⊂ ℝ with max(|A+A|, |AA|) ≤ |A|^(2−c), as recorded on
erdosproblems.com/52 and in Optimization Problems 84b. The other registered targets hold by the
sources that list records: the ε-uniform characterization of C84b, the upper bounds 2, 2 − c and
1.99999913 (the last from the authors' sketched explicit version of their argument), and the
lower bounds 1, 5/4, 14/11, 4/3, 1558/1167, 1270/951 and 4/3 + 10/4407. The exact value of C84b
remains open and is not a registered target; the integer sum-product question (Erdős Problem 52)
is open and not formalized here. This target holds: Cushman (arXiv:2512.13849, abstract):
max(|A+A|, |AA|) >>_ε |A|^(4/3 + 10/4407 - ε) for finite A ⊂ ℝ; Optimization Problems 84b lists
it as the current record [Cu25]. Source: Paul Erdős and Endre Szemerédi, On sums and products of
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
public theorem_wanted cushmanCurrentLowerBound_holds : cushmanCurrentLowerBound

end MathlibExt.Combinatorics.RealSumProductExponentWanted
