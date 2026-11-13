/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.AssociationTests.CochranArmitage
public import MathlibExt.Probability.LindebergFeller
public import MathlibExt.Probability.Distributions.Hypergeometric

/-!
# The Cochran–Armitage test under the fixed-margin (case–control) design

`MathlibExt.Biology.StatisticalGenetics.AssociationTests.CochranArmitage` proves that the
Cochran–Armitage trend statistic is asymptotically `χ²₁` under *prospective* (multinomial)
sampling, where the numbers of cases and controls are random. A case–control study instead fixes
the number `R` of cases and the number `S` of controls and samples genotypes within each group:
*product-binomial* (for three genotype classes, product-multinomial) sampling. This file treats
that design.

## The design and the null

Subjects `0, …, R - 1` are the cases and `R, …, R + S - 1` the controls; subject `k` has genotype
class `G k`. The genotypes are independent, the cases with law `πcase` and the controls with law
`πctrl`. The null hypothesis of no association is `πcase = πctrl`. The table has row margins
`R, S` fixed by design and column margins `n i` (the genotype totals, `genotypeTotal`) random.

## Conditional null law

`measureReal_caseCount_genotypeTotal`: under the null, conditional on the genotype margin `n`,
the case counts `r` have the **multivariate hypergeometric** law
`H(r ∣ n) = ∏ᵢ C(nᵢ, rᵢ) / C(R + S, R)` (`mvHypergeometricReal`), whatever the common genotype
law. It is stated for any finite set of genotype classes and without division,
`P(case counts = r, margin = n) = H(r ∣ n) · P(margin = n)`, so it also holds when the margin has
probability zero. The proof writes both events as sets of genotype vectors, each vector of class
counts `n` having probability `∏ᵢ π{i}^{nᵢ}`, and counts them
(`card_classCount_eq_mul_prod_factorial`, `card_caseCount_mul_choose`).

`measureReal_fmStat_mem_genotypeTotal` pushes this law through the statistic: conditional on the
margin, the trend statistic is `trendStat(r, n - r)` with `r ~ H(· ∣ n)`. This is the permutation
law behind the exact (conditional) Cochran–Armitage test.

## Asymptotic `χ²₁`

`tendstoInDistribution_fmStat`: for designs of size `N` with `R N` cases and `N - R N` controls,
genotypes independent within each design (a triangular array: designs of different sizes need not
share subjects), under the null and with positive genotype-score variance, the trend statistic
converges in distribution to `χ²₁` **whenever `R N → ∞` and `N - R N → ∞`**. No condition on the
case fraction `R N / N` is imposed.

Proof. With scores `x k ∈ {0, 1, 2}`, mean `μ` and variance `v` under the common law, the
statistic equals `W² / V` (`fmStat_eq`), where
`W = ∑_{k < N} w k (x k - μ) / √(R S N v)` with contrast weights `w k = S` for cases and `-R`
for controls (`fmWeight`), and `V = (N ∑ x² - (∑ x)²) / (N² v)` is the pooled score variance
divided by `v`. The summands of `W` have total variance `1` and squares uniformly
`O(1/R + 1/S)`, so the Lindeberg–Feller theorem
(`ProbabilityTheory.lindeberg_feller_clt_triangular`) gives `W ⇒ N(0, 1)`; a Chebyshev weak law
for the triangular array gives `V → 1` in probability; and
Slutsky's theorem with `N(0, 1)² = χ²₁` (`gaussianReal_map_sq`) finishes. The centring `μ` is
never estimated separately: the weights sum to `0`, so `U = ∑ w k x k` is free of `μ`.

## Regime conditions and boundary cases

* **Both groups must grow.** The hypotheses are `R N → ∞` and `N - R N → ∞`. Whether the `χ²₁`
  limit fails when one group stays bounded is not addressed here.
* **Degenerate designs.** A design without cases or without controls has statistic `0`
  (`fmStat_zero_cases`, `fmStat_zero_controls`). The classical statistic is undefined there (its
  denominator vanishes); the value `0` comes from Lean's convention `x / 0 = 0`.
* **Singular genotype law.** If all genotypes are one class the statistic is `0`
  (`fmStat_eq_zero_of_const`), again by the convention `x / 0 = 0`, since the classical
  statistic is undefined at zero score variance; if this holds almost surely for every design the
  statistic has no `χ²₁` limit (`not_tendstoInDistribution_fmStat_of_const`), so the positive
  score variance hypothesis cannot be dropped.
* **Finite samples.** For fixed `R, S` the conditional law above is exact and discrete; `χ²₁` is
  only its limit.

Not covered: alternatives (`πcase ≠ πctrl`) and power, estimation of the common genotype law, and
the allelic test.

The counts `caseCount`, `controlCount` index cases by their position in the design; they differ
from `CochranArmitage.caseCount`, which reads the case status from a random sample.

## Main results

* `measureReal_caseCount_genotypeTotal`: the multivariate hypergeometric conditional null law;
  `mvHypergeometricReal_fin_two` identifies the two-class case with `hypergeometricReal`.
* `measureReal_fmStat_mem_genotypeTotal`: the exact conditional null law of the statistic.
* `tendstoInDistribution_fmStat`: asymptotic `χ²₁` under the fixed-margin design.
* `fmStat_eq`: the statistic as a squared normalized contrast over a variance ratio.
* `not_tendstoInDistribution_fmStat_of_const`: no `χ²₁` limit for a singular genotype law.

## Source receipt

The statistic is `GenomicPrediction.ArmitageTrend.trendStat` (scores `0, 1, 2`), the one used by
`CochranArmitage.caStat`, here evaluated on the case and control counts of a fixed-margin design
(`fmStat`). Armitage (1955) introduces the trend test for proportions and refers it to `χ²₁`;
Mantel (1963) gives the trend test conditional on all margins, with hypergeometric moments. The
Lindeberg–Feller theorem is `MathlibExt.Probability.LindebergFeller`; Slutsky's theorem is
`MathlibExt.Probability.Statistics.Slutsky`.

## References

* W. G. Cochran, *Some methods for strengthening the common χ² tests*, Biometrics 10 (1954),
  417–451.
* P. Armitage, *Tests for linear trends in proportions and frequencies*, Biometrics 11 (1955),
  375–386.
* N. Mantel, *Chi-square tests with one degree of freedom; extensions of the Mantel–Haenszel
  procedure*, J. Amer. Statist. Assoc. 58 (1963), 690–700.
* P. D. Sasieni, *From genotypes to genes: doubling the sample size*, Biometrics 53 (1997),
  1253–1261.
* P. Billingsley, *Probability and Measure*, 3rd ed., Wiley (1995), Theorem 27.2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology Nat

namespace MathlibExt.Biology.StatisticalGenetics.CochranArmitageFixedMargin

/-! ### Counting genotype vectors with prescribed class counts -/

section Counting

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The class counts of a genotype vector: `classCount v i` is the number of positions `j` with
`v j = i`. -/
def classCount {M : ℕ} (v : Fin M → ι) (i : ι) : ℕ := #{j | v j = i}

omit [Fintype ι] in
/-- Prepending `a` adds one to the count of class `a`. -/
theorem classCount_cons {M : ℕ} (a : ι) (v : Fin M → ι) (i : ι) :
    classCount (Fin.cons a v : Fin (M + 1) → ι) i = classCount v i + if a = i then 1 else 0 := by
  simp only [classCount, card_filter, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  ring

/-- The class counts of a vector of length `M` sum to `M`. -/
theorem sum_classCount {M : ℕ} (v : Fin M → ι) : ∑ i, classCount v i = M := by
  simp only [classCount]
  rw [← card_eq_sum_card_fiberwise (fun j _ ↦ mem_univ (v j))]
  simp

/-- **Counting vectors with prescribed class counts**: there are `M! / ∏ mᵢ!` vectors
`Fin M → ι` whose class counts are `m`, stated without division. -/
theorem card_classCount_eq_mul_prod_factorial (M : ℕ) (m : ι → ℕ) (hm : ∑ i, m i = M) :
    #{v : Fin M → ι | classCount v = m} * ∏ i, (m i)! = M ! := by
  induction M generalizing m with
  | zero =>
    have hm0 : m = 0 := funext fun i ↦ (sum_eq_zero_iff.1 hm) i (mem_univ i)
    subst hm0
    have : ({v : Fin 0 → ι | classCount v = 0} : Finset _) = univ := by
      ext v
      simp only [mem_filter, mem_univ, true_and, iff_true]
      funext i
      simp [classCount]
    rw [this, card_univ]
    simp
  | succ M ih =>
    have hsplit : #{v : Fin (M + 1) → ι | classCount v = m} =
        ∑ a, #{w : Fin M → ι | classCount (Fin.cons a w : Fin (M + 1) → ι) = m} := by
      rw [card_filter, ← (Fin.consEquiv fun _ ↦ ι).sum_comp, Fintype.sum_prod_type]
      simp only [Fin.consEquiv, Equiv.coe_fn_mk, card_filter]
      rfl
    have hterm : ∀ a, #{w : Fin M → ι | classCount (Fin.cons a w : Fin (M + 1) → ι) = m} *
        ∏ i, (m i)! = m a * M ! := by
      intro a
      by_cases ha : m a = 0
      · have : ({w : Fin M → ι | classCount (Fin.cons a w : Fin (M + 1) → ι) = m} : Finset _)
            = ∅ := by
          refine filter_eq_empty_iff.2 fun w _ hw ↦ ?_
          have := congrFun hw a
          rw [classCount_cons, ha] at this
          simp at this
        simp [this, ha]
      · set m' := Function.update m a (m a - 1) with hm'
        have hset : ({w : Fin M → ι | classCount (Fin.cons a w : Fin (M + 1) → ι) = m} :
            Finset _) = ({w | classCount w = m'} : Finset (Fin M → ι)) := by
          ext w
          simp only [mem_filter, mem_univ, true_and]
          constructor
          · intro hw
            funext i
            have := congrFun hw i
            rw [classCount_cons] at this
            by_cases hi : i = a
            · subst hi; simp [hm'] at this ⊢; omega
            · simp [hm', hi, Ne.symm hi] at this ⊢; omega
          · intro hw
            funext i
            rw [classCount_cons, hw]
            by_cases hi : i = a
            · subst hi; simp [hm']; omega
            · simp [hm', hi, Ne.symm hi]
        have hsum' : ∑ i, m' i = M := by
          have h1 := Finset.sum_update_of_mem (mem_univ a) m (m a - 1)
          rw [hm', h1]
          have h2 := Finset.add_sum_erase univ m (mem_univ a)
          have : ∑ x ∈ univ \ {a}, m x = ∑ x ∈ univ.erase a, m x := by
            rw [sdiff_singleton_eq_erase]
          omega
        have hprod : ∏ i, (m i)! = m a * ∏ i, (m' i)! := by
          rw [← mul_prod_erase univ (fun i ↦ (m i)!) (mem_univ a),
            ← mul_prod_erase univ (fun i ↦ (m' i)!) (mem_univ a)]
          have herase : ∏ i ∈ univ.erase a, (m' i)! = ∏ i ∈ univ.erase a, (m i)! :=
            prod_congr rfl fun i hi ↦ by
              rw [hm', Function.update_of_ne (ne_of_mem_erase hi)]
          rw [herase, hm', Function.update_self]
          obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero ha
          rw [hk, Nat.factorial_succ, Nat.succ_sub_one, Nat.succ_eq_add_one]
          ring
        rw [hset, hprod, mul_left_comm, ih m' hsum']
    rw [hsplit, sum_mul, sum_congr rfl fun a _ ↦ hterm a, ← sum_mul, hm, Nat.factorial_succ]

omit [Fintype ι] in
/-- The class counts of a concatenation are the sums of the class counts. -/
theorem classCount_append {R S : ℕ} (x : Fin R → ι) (y : Fin S → ι) :
    classCount (Fin.append x y) = classCount x + classCount y := by
  funext i
  simp only [classCount, card_filter, Fin.sum_univ_add, Fin.append_left, Fin.append_right,
    Pi.add_apply]

/-- **Two-sample counting identity.** Among the vectors `z : Fin (R + S) → ι` with class counts
`n`, those whose first `R` coordinates have class counts `r` (with `∑ r = R`) make up the
fraction `∏ᵢ C(nᵢ, rᵢ) / C(R + S, R)`; stated without division. -/
theorem card_caseCount_mul_choose (R S : ℕ) (r n : ι → ℕ) (hr : ∑ i, r i = R) :
    #{z : Fin (R + S) → ι | classCount (fun j ↦ z (Fin.castAdd S j)) = r ∧ classCount z = n} *
        (R + S).choose R =
      (∏ i, (n i).choose (r i)) * #{z : Fin (R + S) → ι | classCount z = n} := by
  -- Rewrite both counts over pairs `(x, y)` of case and control vectors.
  have hpair : ∀ p : (Fin (R + S) → ι) → Prop, [DecidablePred p] →
      #{z | p z} = #{xy : (Fin R → ι) × (Fin S → ι) | p (Fin.append xy.1 xy.2)} := by
    intro p _
    simp only [card_filter]
    exact ((Fin.appendEquiv R S).sum_comp fun z ↦ if p z then 1 else 0).symm
  have hA' : #{z : Fin (R + S) → ι | classCount (fun j ↦ z (Fin.castAdd S j)) = r ∧
      classCount z = n} =
      #{xy : (Fin R → ι) × (Fin S → ι) | classCount xy.1 = r ∧
        classCount xy.1 + classCount xy.2 = n} := by
    rw [hpair]
    congr 1
    refine filter_congr fun xy _ ↦ ?_
    have : (fun j ↦ Fin.append xy.1 xy.2 (Fin.castAdd S j)) = xy.1 :=
      funext fun j ↦ Fin.append_left _ _ j
    rw [this, classCount_append]
  have hB' : #{z : Fin (R + S) → ι | classCount z = n} =
      #{xy : (Fin R → ι) × (Fin S → ι) | classCount xy.1 + classCount xy.2 = n} := by
    rw [hpair]
    congr 1
    exact filter_congr fun xy _ ↦ by rw [classCount_append]
  rw [hA', hB']
  by_cases hn : ∑ i, n i = R + S
  swap
  · have hempty : ({xy : (Fin R → ι) × (Fin S → ι) | classCount xy.1 + classCount xy.2 = n} :
        Finset _) = ∅ := by
      refine filter_eq_empty_iff.2 fun xy _ hxy ↦ hn ?_
      rw [← hxy]
      simp [sum_add_distrib, sum_classCount]
    have hempty' : ({xy : (Fin R → ι) × (Fin S → ι) | classCount xy.1 = r ∧
          classCount xy.1 + classCount xy.2 = n} : Finset _) = ∅ :=
      filter_eq_empty_iff.2 fun xy _ hxy ↦ (filter_eq_empty_iff.1 hempty) (mem_univ xy) hxy.2
    rw [hempty, hempty']
    simp
  by_cases hrn : ∀ i, r i ≤ n i
  swap
  · push Not at hrn
    obtain ⟨i, hi⟩ := hrn
    have hzero : ∏ i, (n i).choose (r i) = 0 :=
      prod_eq_zero (mem_univ i) (Nat.choose_eq_zero_of_lt hi)
    have hempty : ({xy : (Fin R → ι) × (Fin S → ι) | classCount xy.1 = r ∧
          classCount xy.1 + classCount xy.2 = n} : Finset _) = ∅ := by
      refine filter_eq_empty_iff.2 fun xy _ hxy ↦ ?_
      have h := congrFun hxy.2 i
      rw [Pi.add_apply, show classCount xy.1 i = r i from congrFun hxy.1 i] at h
      omega
    rw [hempty, hzero]
    simp
  -- Main case: the pairs factor as (cases with counts `r`) × (controls with counts `n - r`).
  set s : ι → ℕ := fun i ↦ n i - r i with hs
  have hprodset : ({xy : (Fin R → ι) × (Fin S → ι) | classCount xy.1 = r ∧
        classCount xy.1 + classCount xy.2 = n} : Finset _) =
      ({x : Fin R → ι | classCount x = r} : Finset _) ×ˢ
        ({y : Fin S → ι | classCount y = s} : Finset _) := by
    ext ⟨x, y⟩
    simp only [mem_filter, mem_univ, true_and, mem_product]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, funext fun i ↦ ?_⟩
      have := congrFun h2 i
      rw [Pi.add_apply, congrFun h1 i] at this
      simp only [hs]
      omega
    · rintro ⟨h1, h2⟩
      refine ⟨h1, funext fun i ↦ ?_⟩
      rw [Pi.add_apply, congrFun h1 i, congrFun h2 i]
      simp only [hs]
      have := hrn i
      omega
  rw [hprodset, card_product, ← hB']
  have hsS : ∑ i, s i = S := by
    have : ∑ i, (s i + r i) = ∑ i, n i := sum_congr rfl fun i _ ↦ by
      simp only [hs]; have := hrn i; omega
    rw [sum_add_distrib, hn, hr] at this
    omega
  have hA := card_classCount_eq_mul_prod_factorial R r hr
  have hB := card_classCount_eq_mul_prod_factorial S s hsS
  have hN := card_classCount_eq_mul_prod_factorial (R + S) n hn
  have hpos : 0 < (∏ i, (r i)!) * ∏ i, (s i)! := by positivity
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  have hchoose : (∏ i, (n i).choose (r i)) * ((∏ i, (r i)!) * ∏ i, (s i)!) =
      ∏ i, (n i)! := by
    rw [← prod_mul_distrib, ← prod_mul_distrib]
    refine prod_congr rfl fun i _ ↦ ?_
    rw [← mul_assoc, Nat.choose_mul_factorial_mul_factorial (hrn i)]
  have hRS : (R + S).choose R * R ! * S ! = (R + S)! := by
    have := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right R S)
    rwa [Nat.add_sub_cancel_left] at this
  calc #{x : Fin R → ι | classCount x = r} * #{y : Fin S → ι | classCount y = s} *
          (R + S).choose R * ((∏ i, (r i)!) * ∏ i, (s i)!)
        = (R + S).choose R * (#{x : Fin R → ι | classCount x = r} * ∏ i, (r i)!) *
            (#{y : Fin S → ι | classCount y = s} * ∏ i, (s i)!) := by ring
      _ = (R + S)! := by rw [hA, hB, hRS]
      _ = (∏ i, (n i).choose (r i)) * #{z : Fin (R + S) → ι | classCount z = n} *
            ((∏ i, (r i)!) * ∏ i, (s i)!) := by
        rw [mul_right_comm, hchoose, mul_comm, hN]

/-- The **multivariate hypergeometric** mass function: drawing `R` balls without replacement from
an urn with `nᵢ` balls of colour `i` gives the colour counts `r` with probability
`∏ᵢ C(nᵢ, rᵢ) / C(∑ᵢ nᵢ, R)` when `∑ᵢ rᵢ = R` (and `0` otherwise). -/
noncomputable def mvHypergeometricReal (R : ℕ) (n r : ι → ℕ) : ℝ :=
  if ∑ i, r i = R then (∏ i, ((n i).choose (r i) : ℝ)) / ((∑ i, n i).choose R : ℝ) else 0

omit [DecidableEq ι] in
/-- With two colours the multivariate hypergeometric law is the hypergeometric law
`ProbabilityTheory.hypergeometricReal`: `K` marked balls among `N`, `R` draws, `k` marked. -/
theorem mvHypergeometricReal_fin_two {N K R k : ℕ} (hK : K ≤ N) (hk : k ≤ R) :
    mvHypergeometricReal R ![K, N - K] ![k, R - k] = hypergeometricReal N K R k := by
  have hr : ∑ i, (![k, R - k] : Fin 2 → ℕ) i = R := by simp [Fin.sum_univ_two]; omega
  have hn : ∑ i, (![K, N - K] : Fin 2 → ℕ) i = N := by simp [Fin.sum_univ_two]; omega
  simp only [mvHypergeometricReal, hr, hn, hypergeometricReal, hk, ↓reduceIte]
  simp [Fin.prod_univ_two]

end Counting

/-! ### The fixed-margin design and its conditional null law -/

section Design

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The number of cases with genotype class `i` in a design whose subjects `0, …, R - 1` are the
`R` cases; subject `k` has genotype class `g k`. -/
def caseCount (R : ℕ) (g : ℕ → ι) (i : ι) : ℕ := #{k ∈ range R | g k = i}

/-- The number of controls with genotype class `i` in a design whose subjects `R, …, N - 1` are
the `N - R` controls. -/
def controlCount (R N : ℕ) (g : ℕ → ι) (i : ι) : ℕ := #{k ∈ Ico R N | g k = i}

/-- The genotype margin: the number of subjects `k < N` (cases and controls together) with
genotype class `i`. -/
def genotypeTotal (N : ℕ) (g : ℕ → ι) (i : ι) : ℕ := #{k ∈ range N | g k = i}

omit [Fintype ι] in
/-- Counting over `range M` is counting over the vector `Fin M → ι`. -/
theorem card_filter_range_eq_classCount (M : ℕ) (g : ℕ → ι) (i : ι) :
    #{k ∈ range M | g k = i} = classCount (fun j : Fin M ↦ g j) i := by
  simp only [classCount, card_filter]
  exact (Fin.sum_univ_eq_sum_range (fun k ↦ if g k = i then 1 else 0) M).symm

omit [Fintype ι] in
/-- The genotype margin is the sum of the case and control counts. -/
theorem caseCount_add_controlCount {R N : ℕ} (hRN : R ≤ N) (g : ℕ → ι) (i : ι) :
    caseCount R g i + controlCount R N g i = genotypeTotal N g i := by
  simp only [caseCount, controlCount, genotypeTotal, card_filter]
  exact sum_range_add_sum_Ico _ hRN

/-- The case counts sum to the number `R` of cases. -/
theorem sum_caseCount (R : ℕ) (g : ℕ → ι) : ∑ i, caseCount R g i = R := by
  simp only [caseCount, card_filter_range_eq_classCount, sum_classCount]

end Design

section ConditionalLaw

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- Under independence with a common genotype law `π`, the probability of a genotype vector `z`
is `∏ᵢ π{i} ^ (number of coordinates of z equal to i)`. -/
private theorem measureReal_vector_eq (M : ℕ) {G : ℕ → Ω → ι}
    (hind : iIndepFun (fun j : Fin M ↦ G j) P) {π : Measure ι}
    (hlaw : ∀ j : Fin M, HasLaw (G j) π P) (z : Fin M → ι) :
    P.real {ω | (fun j : Fin M ↦ G j ω) = z} = ∏ i, π.real {i} ^ classCount z i := by
  have hset : {ω | (fun j : Fin M ↦ G j ω) = z} = ⋂ j ∈ (univ : Finset (Fin M)),
      (fun j : Fin M ↦ G j) j ⁻¹' {z j} := by
    ext ω
    simp [funext_iff]
  rw [hset, measureReal_def,
    hind.measure_inter_preimage_eq_mul univ (fun j _ ↦ measurableSet_singleton (z j)),
    ENNReal.toReal_prod]
  have hj : ∀ j : Fin M, (P (G j ⁻¹' {z j})).toReal = π.real {z j} := by
    intro j
    rw [← (hlaw j).map_eq, map_measureReal_apply_of_aemeasurable (hlaw j).aemeasurable
      (measurableSet_singleton _), measureReal_def]
  simp only [hj]
  rw [← prod_fiberwise univ z (fun j ↦ π.real {z j})]
  refine prod_congr rfl fun i _ ↦ ?_
  rw [prod_congr rfl fun j hj ↦ by rw [(mem_filter.1 hj).2], prod_const, classCount]

/-- **Conditional null law of the fixed-margin case–control table.** In the product-binomial
design, `R` cases (subjects `0, …, R - 1`) and `S` controls (subjects `R, …, R + S - 1`) are
sampled independently, the cases with genotype law `πcase` and the controls with genotype law
`πctrl`. Under the null `πcase = πctrl`, conditional on the genotype margin `n` (the class totals
over all `R + S` subjects), the case counts `r` follow the multivariate hypergeometric law
`∏ᵢ C(nᵢ, rᵢ) / C(R + S, R)`, which does not depend on the common genotype law.

The conditional probability is stated without division:
`P(case counts = r, margin = n) = H(r ∣ n) · P(margin = n)`, so it also holds for margins of
probability zero. -/
theorem measureReal_caseCount_genotypeTotal (R S : ℕ) {G : ℕ → Ω → ι}
    (hind : iIndepFun (fun j : Fin (R + S) ↦ G j) P) {πcase πctrl : Measure ι}
    (hcase : ∀ k < R, HasLaw (G k) πcase P)
    (hctrl : ∀ k, R ≤ k → k < R + S → HasLaw (G k) πctrl P) (hnull : πcase = πctrl)
    (r n : ι → ℕ) :
    P.real {ω | caseCount R (G · ω) = r ∧ genotypeTotal (R + S) (G · ω) = n} =
      mvHypergeometricReal R n r * P.real {ω | genotypeTotal (R + S) (G · ω) = n} := by
  subst hnull
  set π := πcase
  have hlaw : ∀ j : Fin (R + S), HasLaw (G j) π P := fun j ↦ by
    by_cases hj : (j : ℕ) < R
    · exact hcase j hj
    · exact hctrl j (not_lt.1 hj) j.isLt
  set Z : Ω → Fin (R + S) → ι := fun ω j ↦ G j ω with hZdef
  have hZ : AEMeasurable Z P := AEMeasurable.of_eval fun j ↦ (hlaw j).aemeasurable
  -- The probability of `Z ∈ A` for a finite set `A` of genotype vectors.
  have hfin : ∀ A : Finset (Fin (R + S) → ι), P.real (Z ⁻¹' ↑A) =
      ∑ z ∈ A, ∏ i, π.real {i} ^ classCount z i := by
    intro A
    rw [← map_measureReal_apply_of_aemeasurable hZ (Set.toFinite _).measurableSet,
      ← sum_measureReal_singleton]
    refine sum_congr rfl fun z _ ↦ ?_
    rw [map_measureReal_apply_of_aemeasurable hZ (measurableSet_singleton z)]
    exact measureReal_vector_eq (R + S) hind hlaw z
  set A : Finset (Fin (R + S) → ι) :=
    {z | classCount (fun j ↦ z (Fin.castAdd S j)) = r ∧ classCount z = n} with hA
  set B : Finset (Fin (R + S) → ι) := {z | classCount z = n} with hB
  have hcaseEq : ∀ ω, caseCount R (G · ω) = classCount (fun j ↦ Z ω (Fin.castAdd S j)) := by
    intro ω
    funext i
    simp [caseCount, card_filter_range_eq_classCount, hZdef]
  have htotEq : ∀ ω, genotypeTotal (R + S) (G · ω) = classCount (Z ω) := by
    intro ω
    funext i
    simp [genotypeTotal, card_filter_range_eq_classCount, hZdef]
  have hevA : {ω | caseCount R (G · ω) = r ∧ genotypeTotal (R + S) (G · ω) = n} = Z ⁻¹' ↑A := by
    ext ω
    simp [hA, hcaseEq, htotEq]
  have hevB : {ω | genotypeTotal (R + S) (G · ω) = n} = Z ⁻¹' ↑B := by
    ext ω
    simp [hB, htotEq]
  set w : ℝ := ∏ i, π.real {i} ^ n i with hw
  have hsumA : ∑ z ∈ A, ∏ i, π.real {i} ^ classCount z i = #A * w := by
    rw [sum_congr rfl fun z hz ↦ by rw [(mem_filter.1 hz).2.2], sum_const, nsmul_eq_mul]
  have hsumB : ∑ z ∈ B, ∏ i, π.real {i} ^ classCount z i = #B * w := by
    rw [sum_congr rfl fun z hz ↦ by rw [(mem_filter.1 hz).2], sum_const, nsmul_eq_mul]
  rw [hevA, hevB, hfin, hfin, hsumA, hsumB, mvHypergeometricReal]
  by_cases hr : ∑ i, r i = R
  swap
  · have hA0 : A = ∅ := filter_eq_empty_iff.2 fun z _ hz ↦ hr (by
      rw [← hz.1, sum_classCount])
    simp [hA0, hr]
  have hcard := card_caseCount_mul_choose R S r n hr
  simp only [hr, ↓reduceIte]
  by_cases hn : ∑ i, n i = R + S
  · rw [hn]
    have hC : (0 : ℝ) < ((R + S).choose R : ℝ) := by
      exact_mod_cast Nat.choose_pos (Nat.le_add_right R S)
    field_simp
    have := congrArg (fun x : ℕ ↦ (x : ℝ)) hcard
    push_cast at this
    rw [← hA, ← hB] at this
    linear_combination w * this
  · have hB0 : B = ∅ := filter_eq_empty_iff.2 fun z _ hz ↦ hn (by
      rw [← hz, sum_classCount])
    have hA0 : #A = 0 := by
      rw [← hA, ← hB, hB0, card_empty, mul_zero] at hcard
      exact (Nat.mul_eq_zero.1 hcard).resolve_right (Nat.choose_pos (Nat.le_add_right R S)).ne'
    simp [hB0, hA0]

omit [Fintype ι] [DecidableEq ι] [MeasurableSingletonClass ι] [IsProbabilityMeasure P] in
private theorem nullMeasurableSet_caseCount_genotypeTotal [Finite ι] [DecidableEq ι]
    [MeasurableSingletonClass ι] (R S : ℕ) {G : ℕ → Ω → ι}
    (hG : ∀ j : Fin (R + S), AEMeasurable (G j) P) (r n : ι → ℕ) :
    NullMeasurableSet {ω | caseCount R (G · ω) = r ∧ genotypeTotal (R + S) (G · ω) = n} P := by
  have hZ : AEMeasurable (fun ω (j : Fin (R + S)) ↦ G j ω) P := AEMeasurable.of_eval hG
  have hset : {ω | caseCount R (G · ω) = r ∧ genotypeTotal (R + S) (G · ω) = n} =
      (fun ω (j : Fin (R + S)) ↦ G j ω) ⁻¹'
        {z | classCount (fun j ↦ z (Fin.castAdd S j)) = r ∧ classCount z = n} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    have h1 : caseCount R (G · ω) = classCount (fun j : Fin R ↦ G (Fin.castAdd S j : ℕ) ω) := by
      funext i
      simp [caseCount, card_filter_range_eq_classCount]
    have h2 : genotypeTotal (R + S) (G · ω) = classCount (fun j : Fin (R + S) ↦ G j ω) := by
      funext i
      simp [genotypeTotal, card_filter_range_eq_classCount]
    rw [h1, h2]
  rw [hset]
  exact hZ.nullMeasurable (Set.toFinite _).measurableSet

end ConditionalLaw

/-! ### The Cochran–Armitage statistic of a fixed-margin design -/

section Statistic

open MathlibExt.Biology.StatisticalGenetics.GenomicPrediction
open MathlibExt.Biology.StatisticalGenetics.CochranArmitage (score)

/-- The **Cochran–Armitage trend statistic of a fixed-margin design**: subjects `0, …, R - 1` are
the cases and `R, …, N - 1` the controls, subject `k` has genotype class `g k ∈ {0, 1, 2}`, and
the statistic is `GenomicPrediction.ArmitageTrend.trendStat` of the resulting `2 × 3` table. -/
noncomputable def fmStat (R N : ℕ) (g : ℕ → Fin 3) : ℝ :=
  ArmitageTrend.trendStat (fun i ↦ (caseCount R g i : ℝ)) (fun i ↦ (controlCount R N g i : ℝ))

/-- The contrast weight of subject `k`: `N - R` for a case (`k < R`), `-R` for a control. The
trend numerator is `U = ∑_{k < N} weight k · score (g k)`. -/
noncomputable def fmWeight (R N k : ℕ) : ℝ := if k < R then (N : ℝ) - R else -(R : ℝ)

/-- The weight of a case. -/
theorem fmWeight_of_lt {R N k : ℕ} (hk : k < R) : fmWeight R N k = (N : ℝ) - R := by
  simp [fmWeight, hk]

/-- The weight of a control. -/
theorem fmWeight_of_le {R N k : ℕ} (hk : R ≤ k) : fmWeight R N k = -(R : ℝ) := by
  simp [fmWeight, not_lt.2 hk]

private theorem sum_mul_card_filter {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℝ)
    (s : Finset ℕ) (g : ℕ → ι) :
    ∑ i, f i * (#{k ∈ s | g k = i} : ℝ) = ∑ k ∈ s, f (g k) := by
  simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, mul_sum,
    mul_ite, mul_one, mul_zero]
  rw [sum_comm]
  exact sum_congr rfl fun k _ ↦ by simp [eq_comm]

/-- **The fixed-margin statistic as a normalized contrast.** For `R ≤ N` and any centring `μ` and
scale `v > 0`, with `B = √(R (N - R) N v)`,
`fmStat R N g = (U / B)² / ((N ∑ x² - (∑ x)²) / (N² v))`, where `x k = score (g k)` and
`U = ∑_{k < N} fmWeight R N k · (x k - μ)` is the trend numerator. Degenerate designs
(`R = 0` or `R = N`) and tables with zero score variance give `0` on both sides. -/
theorem fmStat_eq (R N : ℕ) (hRN : R ≤ N) (g : ℕ → Fin 3) (μ v : ℝ) (hv : 0 < v) :
    fmStat R N g =
      ((∑ k ∈ range N, fmWeight R N k * (score (g k) - μ)) /
          √(R * ((N : ℝ) - R) * N * v)) ^ 2 /
        ((N * ∑ k ∈ range N, score (g k) ^ 2 - (∑ k ∈ range N, score (g k)) ^ 2) /
          ((N : ℝ) ^ 2 * v)) := by
  set a := ∑ k ∈ range R, score (g k) with ha
  set b := ∑ k ∈ Ico R N, score (g k) with hb
  set q := ∑ k ∈ range N, score (g k) ^ 2 with hq
  have hsplit : ∀ f : ℕ → ℝ, ∑ k ∈ range N, f k = ∑ k ∈ range R, f k + ∑ k ∈ Ico R N, f k :=
    fun f ↦ (sum_range_add_sum_Ico f hRN).symm
  have hcase : ∀ f : Fin 3 → ℝ, ∑ i, f i * (caseCount R g i : ℝ) = ∑ k ∈ range R, f (g k) :=
    fun f ↦ sum_mul_card_filter f _ g
  have hctrl : ∀ f : Fin 3 → ℝ, ∑ i, f i * (controlCount R N g i : ℝ) =
      ∑ k ∈ Ico R N, f (g k) := fun f ↦ sum_mul_card_filter f _ g
  have hR : ∑ i, (caseCount R g i : ℝ) = R := by
    simpa using hcase (fun _ ↦ 1)
  have hS : ∑ i, (controlCount R N g i : ℝ) = N - R := by
    have := hctrl (fun _ ↦ 1)
    simp only [one_mul, sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one] at this
    rw [this, Nat.cast_sub hRN]
  have hT : ArmitageTrend.total (fun i ↦ (caseCount R g i : ℝ))
      (fun i ↦ (controlCount R N g i : ℝ)) = N := by
    simp only [ArmitageTrend.total, sum_add_distrib, hR, hS]
    ring
  have hU : ArmitageTrend.numer (fun i ↦ (caseCount R g i : ℝ))
      (fun i ↦ (controlCount R N g i : ℝ)) = ((N : ℝ) - R) * a - R * b := by
    simp only [ArmitageTrend.numer, hR, hS]
    have e : ∀ i : Fin 3, ((i : ℕ) : ℝ) * ((caseCount R g i : ℝ) * ((N : ℝ) - R) -
        (controlCount R N g i : ℝ) * R) = (score i * ((N : ℝ) - R)) * caseCount R g i -
          (score i * R) * controlCount R N g i := fun i ↦ by simp only [score]; ring
    rw [sum_congr rfl fun i _ ↦ e i, sum_sub_distrib, hcase (fun i ↦ score i * ((N : ℝ) - R)),
      hctrl (fun i ↦ score i * R), ha, hb, mul_sum, mul_sum]
    congr 1 <;> exact sum_congr rfl fun k _ ↦ by ring
  have hn1 : ∑ i : Fin 3, ((i : ℕ) : ℝ) * ((caseCount R g i : ℝ) + controlCount R N g i) =
      a + b := by
    simp only [mul_add, sum_add_distrib]
    rw [hcase, hctrl]
    rfl
  have hn2 : ∑ i : Fin 3, ((i : ℕ) : ℝ) ^ 2 * ((caseCount R g i : ℝ) + controlCount R N g i) =
      q := by
    simp only [mul_add, sum_add_distrib]
    rw [hcase (fun i ↦ ((i : ℕ) : ℝ) ^ 2), hctrl (fun i ↦ ((i : ℕ) : ℝ) ^ 2), hq, hsplit]
    rfl
  have hnum : ∑ k ∈ range N, fmWeight R N k * (score (g k) - μ) = ((N : ℝ) - R) * a - R * b := by
    rw [hsplit]
    have e1 : ∑ k ∈ range R, fmWeight R N k * (score (g k) - μ) =
        ((N : ℝ) - R) * a - ((N : ℝ) - R) * R * μ := by
      rw [sum_congr rfl fun k hk ↦ by rw [fmWeight_of_lt (mem_range.1 hk)], ← mul_sum,
        sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, ha]
      ring
    have e2 : ∑ k ∈ Ico R N, fmWeight R N k * (score (g k) - μ) =
        -(R * b) + R * ((N : ℝ) - R) * μ := by
      rw [sum_congr rfl fun k hk ↦ by rw [fmWeight_of_le (mem_Ico.1 hk).1],
        ← mul_sum, sum_sub_distrib, sum_const, Nat.card_Ico, nsmul_eq_mul, hb, Nat.cast_sub hRN]
      ring
    rw [e1, e2]
    ring
  have hsum : ∑ k ∈ range N, score (g k) = a + b := hsplit _
  rw [fmStat, ArmitageTrend.trendStat, hT, hU, hR, hS, hn1, hn2, hnum, hsum]
  set U := ((N : ℝ) - R) * a - R * b
  set D := (N : ℝ) * q - (a + b) ^ 2
  rcases Nat.eq_zero_or_pos R with hR0 | hRpos
  · simp [hR0]
  rcases eq_or_lt_of_le hRN with hRN' | hRlt
  · simp [hRN']
  have hRr : (0 : ℝ) < R := by exact_mod_cast hRpos
  have hSr : (0 : ℝ) < (N : ℝ) - R := by
    have : (R : ℝ) < N := by exact_mod_cast hRlt
    linarith
  have hNr : (0 : ℝ) < N := by linarith
  have hB : √(R * ((N : ℝ) - R) * N * v) ^ 2 = R * ((N : ℝ) - R) * N * v :=
    Real.sq_sqrt (by positivity)
  rw [div_pow, hB]
  rcases eq_or_ne D 0 with hD | hD
  · simp [hD]
  field_simp

/-- A design without cases has statistic `0`. The classical statistic is undefined here (the
factor `R` of its denominator vanishes); the value `0` is Lean's convention `x / 0 = 0`. -/
theorem fmStat_zero_cases (N : ℕ) (g : ℕ → Fin 3) : fmStat 0 N g = 0 :=
  CochranArmitage.trendStat_eq_zero_of_no_cases _ _ (by simp [caseCount])

/-- A design without controls has statistic `0`. The classical statistic is undefined here (the
factor `S` of its denominator vanishes); the value `0` is Lean's convention `x / 0 = 0`. -/
theorem fmStat_zero_controls (N : ℕ) (g : ℕ → Fin 3) : fmStat N N g = 0 :=
  CochranArmitage.trendStat_eq_zero_of_no_controls _ _ (by simp [controlCount])

/-- **Singular design**: if every subject `k < N` has the same genotype class `c`, the score has
zero sample variance and the statistic is `0`. The classical statistic is undefined here (the
score-variance factor of its denominator vanishes); the value `0` is Lean's convention
`x / 0 = 0`. -/
theorem fmStat_eq_zero_of_const {R N : ℕ} (hRN : R ≤ N) {g : ℕ → Fin 3} {c : Fin 3}
    (hg : ∀ k < N, g k = c) : fmStat R N g = 0 := by
  refine CochranArmitage.trendStat_eq_zero_of_single_genotype _ _ c (fun i hi ↦ ?_)
    fun i hi ↦ ?_
  · simp only [caseCount, Nat.cast_eq_zero, card_eq_zero, filter_eq_empty_iff, mem_range]
    intro k hk h
    exact hi (h ▸ hg k (by omega))
  · simp only [controlCount, Nat.cast_eq_zero, card_eq_zero, filter_eq_empty_iff, mem_Ico]
    intro k hk h
    exact hi (h ▸ hg k hk.2)

end Statistic

/-! ### The exact conditional null law of the statistic -/

section ConditionalStatisticLaw

open MathlibExt.Biology.StatisticalGenetics.GenomicPrediction

/-- Given the case counts `r` and the genotype margin `n`, the fixed-margin statistic is the
trend statistic of the table with cases `r` and controls `n - r`. -/
theorem fmStat_eq_of_counts {R S : ℕ} {g : ℕ → Fin 3} {r n : Fin 3 → ℕ}
    (hr : caseCount R g = r) (hn : genotypeTotal (R + S) g = n) :
    fmStat R (R + S) g =
      ArmitageTrend.trendStat (fun i ↦ (r i : ℝ)) (fun i ↦ ((n i - r i : ℕ) : ℝ)) := by
  have hc : ∀ i, controlCount R (R + S) g i = n i - r i := fun i ↦ by
    have := caseCount_add_controlCount (Nat.le_add_right R S) g i
    rw [hr, hn] at this
    omega
  simp only [fmStat, hr, hc]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

open scoped Classical in
/-- **Exact conditional null law of the Cochran–Armitage statistic.** Under the fixed-margin
null of `measureReal_caseCount_genotypeTotal`, conditional on the genotype margin `n`, the trend
statistic is distributed as `trendStat(r, n - r)` with `r` multivariate hypergeometric: for every
set `T` of values,
`P(fmStat ∈ T, margin = n) = (∑ {H(r ∣ n) : r ≤ n, trendStat(r, n - r) ∈ T}) · P(margin = n)`.
This is the permutation distribution behind the exact Cochran–Armitage test; it does not depend
on the common genotype law. -/
theorem measureReal_fmStat_mem_genotypeTotal (R S : ℕ) {G : ℕ → Ω → Fin 3}
    (hind : iIndepFun (fun j : Fin (R + S) ↦ G j) P) {πcase πctrl : Measure (Fin 3)}
    (hcase : ∀ k < R, HasLaw (G k) πcase P)
    (hctrl : ∀ k, R ≤ k → k < R + S → HasLaw (G k) πctrl P) (hnull : πcase = πctrl)
    (T : Set ℝ) (n : Fin 3 → ℕ) :
    P.real {ω | fmStat R (R + S) (G · ω) ∈ T ∧ genotypeTotal (R + S) (G · ω) = n} =
      (∑ r ∈ Fintype.piFinset (fun i ↦ range (n i + 1)) with
          ArmitageTrend.trendStat (fun i ↦ (r i : ℝ)) (fun i ↦ ((n i - r i : ℕ) : ℝ)) ∈ T,
        mvHypergeometricReal R n r) *
        P.real {ω | genotypeTotal (R + S) (G · ω) = n} := by
  set F := (Fintype.piFinset (fun i ↦ range (n i + 1))).filter (fun r : Fin 3 → ℕ ↦
    ArmitageTrend.trendStat (fun i ↦ (r i : ℝ)) (fun i ↦ ((n i - r i : ℕ) : ℝ)) ∈ T) with hF
  have hG : ∀ j : Fin (R + S), AEMeasurable (G j) P := fun j ↦ by
    by_cases hj : (j : ℕ) < R
    · exact (hcase j hj).aemeasurable
    · exact (hctrl j (not_lt.1 hj) j.isLt).aemeasurable
  have hset : {ω | fmStat R (R + S) (G · ω) ∈ T ∧ genotypeTotal (R + S) (G · ω) = n} =
      ⋃ r ∈ F, {ω | caseCount R (G · ω) = r ∧ genotypeTotal (R + S) (G · ω) = n} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨hT, hn⟩
      refine ⟨caseCount R (G · ω), ?_, rfl, hn⟩
      simp only [hF, mem_filter, Fintype.mem_piFinset, mem_range]
      refine ⟨fun i ↦ ?_, ?_⟩
      · have := caseCount_add_controlCount (Nat.le_add_right R S) (G · ω) i
        rw [hn] at this
        omega
      · rwa [← fmStat_eq_of_counts rfl hn]
    · rintro ⟨r, hr, hcr, hn⟩
      refine ⟨?_, hn⟩
      rw [fmStat_eq_of_counts hcr hn]
      exact (mem_filter.1 hr).2
  rw [hset, measureReal_biUnion_finset₀, sum_mul]
  · exact sum_congr rfl fun r _ ↦
      measureReal_caseCount_genotypeTotal R S hind hcase hctrl hnull r n
  · intro r _ r' _ hrr'
    refine Disjoint.aedisjoint (Set.disjoint_left.2 fun ω h h' ↦ hrr' ?_)
    exact h.1.symm.trans h'.1
  · exact fun r _ ↦ nullMeasurableSet_caseCount_genotypeTotal R S hG r n

end ConditionalStatisticLaw

/-! ### Asymptotics -/

section Asymptotics

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Weak law of large numbers for a bounded triangular array** (Chebyshev): if each row
`Y N 0, …, Y N (N - 1)` is independent, `|Y N k| ≤ K` and every entry has mean `m`, the row
means converge to `m` in probability. -/
private theorem tendstoInMeasure_rowMean {Y : ℕ → ℕ → Ω → ℝ} {m K : ℝ}
    (hind : ∀ N, iIndepFun (fun j : Fin N ↦ Y N j) P) (hmeas : ∀ N k, Measurable (Y N k))
    (hbd : ∀ N k ω, |Y N k ω| ≤ K) (hmean : ∀ N, ∀ k < N, ∫ ω, Y N k ω ∂P = m) :
    TendstoInMeasure P (fun (N : ℕ) ω ↦ (∑ k ∈ range N, Y N k ω) / N) atTop (fun _ ↦ m) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have hL2 : ∀ N k, MemLp (Y N k) 2 P := fun N k ↦
    memLp_of_bounded (a := -K) (b := K) (ae_of_all _ fun ω ↦ abs_le.1 (hbd N k ω))
      (hmeas N k).aestronglyMeasurable 2
  have hMeq : ∀ N : ℕ, (fun ω ↦ (∑ k ∈ range N, Y N k ω) / N) =
      fun ω ↦ (N : ℝ)⁻¹ * ∑ j : Fin N, Y N j ω := by
    intro N
    funext ω
    rw [div_eq_inv_mul, Fin.sum_univ_eq_sum_range (fun k ↦ Y N k ω) N]
  have hML2 : ∀ N : ℕ, MemLp (fun ω ↦ (∑ k ∈ range N, Y N k ω) / N) 2 P := fun N ↦ by
    rw [hMeq]
    exact (memLp_finsetSum (f := fun j : Fin N ↦ Y N j) univ fun j _ ↦ hL2 N j).const_mul _
  have hmeanM : ∀ N : ℕ, 1 ≤ N → ∫ ω, (∑ k ∈ range N, Y N k ω) / N ∂P = m := by
    intro N hN
    rw [integral_div, integral_finsetSum _ fun k _ ↦ (hL2 N k).integrable one_le_two,
      sum_congr rfl fun k hk ↦ hmean N k (mem_range.1 hk), sum_const, card_range, nsmul_eq_mul]
    have : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hN)
    field_simp
  have hvarM : ∀ N : ℕ, 1 ≤ N →
      Var[fun ω ↦ (∑ k ∈ range N, Y N k ω) / N; P] ≤ K ^ 2 / N := by
    intro N hN
    rw [hMeq, variance_const_mul]
    have hsum : Var[fun ω ↦ ∑ j : Fin N, Y N j ω; P] = ∑ j : Fin N, Var[Y N j; P] := by
      have := IndepFun.variance_sum (μ := P) (X := fun j : Fin N ↦ Y N j) (s := univ)
        (fun j _ ↦ hL2 N j) (fun i _ j _ hij ↦ (hind N).indepFun hij)
      rw [← this]
      congr 1
      funext ω
      simp
    have hle : ∀ j : Fin N, Var[Y N j; P] ≤ K ^ 2 := by
      intro j
      have := variance_le_sq_of_bounded (μ := P) (a := -K) (b := K)
        (ae_of_all _ fun ω ↦ abs_le.1 (hbd N j ω)) (hmeas N j).aemeasurable
      calc Var[Y N j; P] ≤ ((K - -K) / 2) ^ 2 := this
        _ = K ^ 2 := by ring
    rw [hsum]
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    calc (N : ℝ)⁻¹ ^ 2 * ∑ j : Fin N, Var[Y N j; P] ≤ (N : ℝ)⁻¹ ^ 2 * ∑ _j : Fin N, K ^ 2 := by
          gcongr with j; exact hle j
      _ = K ^ 2 / N := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
  have hcheb : ∀ N : ℕ, 1 ≤ N →
      P {ω | ε ≤ dist ((∑ k ∈ range N, Y N k ω) / N) m} ≤ ENNReal.ofReal (K ^ 2 / N / ε ^ 2) := by
    intro N hN
    have h := meas_ge_le_variance_div_sq (hML2 N) hε
    rw [hmeanM N hN] at h
    simp only [Real.dist_eq]
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    gcongr
    exact hvarM N hN
  have hlim : Tendsto (fun N : ℕ ↦ ENNReal.ofReal (K ^ 2 / N / ε ^ 2)) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    refine ENNReal.tendsto_ofReal ?_
    simpa using (tendsto_const_div_atTop_nhds_zero_nat (K ^ 2)).div_const (ε ^ 2)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ ↦ zero_le) (eventually_atTop.2 ⟨1, hcheb⟩)

omit [IsProbabilityMeasure P] in
/-- Convergence in probability to constants is preserved by differences. -/
private theorem tendstoInMeasure_sub_const {A C : ℕ → Ω → ℝ} {a c : ℝ}
    (hA : TendstoInMeasure P A atTop (fun _ ↦ a)) (hC : TendstoInMeasure P C atTop (fun _ ↦ c)) :
    TendstoInMeasure P (fun N ω ↦ A N ω - C N ω) atTop (fun _ ↦ a - c) := by
  rw [tendstoInMeasure_iff_dist] at hA hC ⊢
  intro ε hε
  have h2 := (hA (ε / 2) (by positivity)).add (hC (ε / 2) (by positivity))
  rw [add_zero] at h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2 (fun _ ↦ zero_le)
    fun N ↦ (measure_mono fun ω hω ↦ ?_).trans (measure_union_le _ _)
  simp only [Set.mem_ofPred_eq, Real.dist_eq] at hω ⊢
  by_contra h
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at h
  have := abs_sub (A N ω - a) (C N ω - c)
  rw [show A N ω - C N ω - (a - c) = (A N ω - a) - (C N ω - c) by ring] at hω
  linarith [h.1, h.2]

open MathlibExt.Biology.StatisticalGenetics.CochranArmitage (score) in
/-- **The Cochran–Armitage test under the fixed-margin case–control design is asymptotically
`χ²₁`.**

For each sample size `N` the design has `R N ≤ N` cases (subjects `k < R N`) and `N - R N`
controls (subjects `R N ≤ k < N`), with genotype classes `G N k ∈ {0, 1, 2}` independent within
the design; cases have genotype law `πcase` and controls `πctrl` (product-binomial sampling: the
numbers of cases and controls are fixed, not random). Under the null `πcase = πctrl`, if the
genotype score has positive variance and both the number of cases and the number of controls
tend to infinity, then the trend statistic `fmStat (R N) N` converges in distribution to `χ²₁`.

No condition on the case fraction `R N / N` is needed: it may oscillate or tend to `0` or `1`.

Measurability `Measurable (G N k)` is assumed for every `k`, including the entries `k ≥ N` that
the statistic never reads; a caller can set those entries to a constant. -/
theorem tendstoInDistribution_fmStat {R : ℕ → ℕ} (hRN : ∀ N, R N ≤ N)
    (hR : Tendsto R atTop atTop) (hS : Tendsto (fun N ↦ N - R N) atTop atTop)
    {G : ℕ → ℕ → Ω → Fin 3} (hmeas : ∀ N k, Measurable (G N k))
    (hind : ∀ N, iIndepFun (fun j : Fin N ↦ G N j) P) {πcase πctrl : Measure (Fin 3)}
    (hcase : ∀ N, ∀ k < R N, HasLaw (G N k) πcase P)
    (hctrl : ∀ N k, R N ≤ k → k < N → HasLaw (G N k) πctrl P) (hnull : πcase = πctrl)
    (hscore : 0 < Var[score; πcase])
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (chiSquareMeasure 1) P') :
    TendstoInDistribution (fun N ω ↦ fmStat (R N) N (G N · ω)) atTop Z (fun _ ↦ P) P' := by
  subst hnull
  set π := πcase
  have hlaw : ∀ N, ∀ k < N, HasLaw (G N k) π P := fun N k hk ↦ by
    by_cases h : k < R N
    · exact hcase N k h
    · exact hctrl N k (not_lt.1 h) hk
  obtain ⟨N₀, hN₀⟩ : ∃ N₀, 1 ≤ R N₀ := (hR.eventually_ge_atTop 1).exists
  have : IsProbabilityMeasure π := by
    have h := hcase N₀ 0 (by omega)
    rw [← h.map_eq]
    exact (Measure.isProbabilityMeasure_map_iff h.aemeasurable).2 inferInstance
  have hsc : Measurable score := measurable_of_countable _
  set μ := ∫ y, score y ∂π with hμ
  set v := Var[score; π] with hv
  set K := 2 + |μ| with hK
  have hsc_Icc : ∀ y : Fin 3, score y ∈ Set.Icc (0 : ℝ) 2 := by
    intro y
    fin_cases y <;> norm_num [score]
  have hxbd : ∀ y : Fin 3, |score y - μ| ≤ K := by
    intro y
    have h := hsc_Icc y
    have : |score y| ≤ 2 := by rw [abs_le]; constructor <;> linarith [h.1, h.2]
    calc |score y - μ| ≤ |score y| + |μ| := abs_sub _ _
      _ ≤ K := by rw [hK]; linarith
  have hK0 : 0 ≤ K := by positivity
  have hxmeas : ∀ N k, Measurable (fun ω ↦ score (G N k ω)) := fun N k ↦ hsc.comp (hmeas N k)
  have hxL2 : ∀ N k, MemLp (fun ω ↦ score (G N k ω)) 2 P := fun N k ↦
    memLp_of_bounded (a := 0) (b := 2) (ae_of_all _ fun ω ↦ hsc_Icc _)
      (hxmeas N k).aestronglyMeasurable 2
  have hxmean : ∀ N, ∀ k < N, ∫ ω, score (G N k ω) ∂P = μ := fun N k hk ↦ by
    simpa [Function.comp_def] using (hlaw N k hk).integral_comp hsc.aestronglyMeasurable
  have hxvar : ∀ N, ∀ k < N, ∫ ω, (score (G N k ω) - μ) ^ 2 ∂P = v := fun N k hk ↦ by
    rw [hv, variance_eq_integral hsc.aemeasurable]
    simpa [Function.comp_def] using (hlaw N k hk).integral_comp
      (f := fun y ↦ (score y - μ) ^ 2) (by fun_prop)
  -- The normalized contrast `W N = ∑_{k < N} X N k`.
  set B : ℕ → ℝ := fun N ↦ √(R N * ((N : ℝ) - R N) * N * v) with hB
  set X : ℕ → ℕ → Ω → ℝ := fun N k ω ↦ fmWeight (R N) N k / B N * (score (G N k ω) - μ)
    with hX
  have hXmeas : ∀ N, ∀ k ∈ range N, Measurable (X N k) := fun N k _ ↦
    measurable_const.mul ((hxmeas N k).sub_const μ)
  have hXind : ∀ N, iIndepFun (m := fun _ ↦ inferInstance) ((range N).restrict (X N)) P := by
    intro N
    have h1 : iIndepFun (fun j : Fin N ↦ X N j) P :=
      (hind N).comp (fun j y ↦ fmWeight (R N) N j / B N * (score y - μ))
        (fun j ↦ measurable_of_countable _)
    exact h1.precomp (g := fun k : range N ↦ (⟨k, mem_range.1 k.2⟩ : Fin N))
      (fun a b h ↦ Subtype.ext (by simpa using congrArg Fin.val h))
  have hXmean : ∀ N, ∀ k ∈ range N, ∫ ω, X N k ω ∂P = 0 := fun N k hk ↦ by
    simp only [hX]
    rw [integral_const_mul, integral_sub ((hxL2 N k).integrable one_le_two) (integrable_const μ),
      hxmean N k (mem_range.1 hk)]
    simp
  have hXL2 : ∀ N k, MemLp (X N k) 2 P := fun N k ↦
    ((hxL2 N k).sub (memLp_const μ)).const_mul _
  have hXint2 : ∀ N, ∀ k ∈ range N, Integrable (fun ω ↦ (X N k ω) ^ 2) P := fun N k _ ↦
    (hXL2 N k).integrable_sq
  -- Eventually both groups are nonempty.
  have hRr : Tendsto (fun N ↦ (R N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hR
  have hSr : Tendsto (fun N : ℕ ↦ (N : ℝ) - R N) atTop atTop := by
    refine (tendsto_natCast_atTop_atTop.comp hS).congr fun N ↦ ?_
    simp [Nat.cast_sub (hRN N)]
  have hev : ∀ᶠ N in atTop, (1 : ℝ) ≤ R N ∧ (1 : ℝ) ≤ (N : ℝ) - R N :=
    (hRr.eventually_ge_atTop 1).and (hSr.eventually_ge_atTop 1)
  have hBsq : ∀ N : ℕ, (1 : ℝ) ≤ R N → (1 : ℝ) ≤ (N : ℝ) - R N →
      B N ^ 2 = R N * ((N : ℝ) - R N) * N * v := fun N h1 h2 ↦ by
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    exact Real.sq_sqrt (by have := hscore.le; positivity)
  have hvar : Tendsto (fun N ↦ ∑ k ∈ range N, ∫ ω, (X N k ω) ^ 2 ∂P) atTop
      (𝓝 ((1 : ℝ) ^ 2)) := by
    rw [one_pow]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with N ⟨h1, h2⟩
    have hterm : ∀ k ∈ range N, ∫ ω, (X N k ω) ^ 2 ∂P = (fmWeight (R N) N k) ^ 2 / B N ^ 2 * v :=
      fun k hk ↦ by
        simp only [hX, mul_pow, div_pow]
        rw [integral_const_mul, hxvar N k (mem_range.1 hk)]
    rw [sum_congr rfl hterm, ← sum_mul, ← sum_div, hBsq N h1 h2]
    have hw : ∑ k ∈ range N, fmWeight (R N) N k ^ 2 = R N * ((N : ℝ) - R N) * N := by
      rw [← sum_range_add_sum_Ico _ (hRN N)]
      rw [sum_congr rfl fun k hk ↦ congrArg (· ^ 2) (fmWeight_of_lt (N := N) (mem_range.1 hk)),
        sum_congr rfl fun k hk ↦ congrArg (· ^ 2) (fmWeight_of_le (N := N) (mem_Ico.1 hk).1)]
      simp only [sum_const, card_range, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub (hRN N)]
      ring
    rw [hw]
    have hN : (0 : ℝ) < N := by linarith
    field_simp
  -- Lindeberg: every normalized summand is uniformly small.
  have hXsq : ∀ N, (1 : ℝ) ≤ R N → (1 : ℝ) ≤ (N : ℝ) - R N → ∀ k < N, ∀ ω,
      X N k ω ^ 2 ≤ K ^ 2 * ((R N * v)⁻¹ + (((N : ℝ) - R N) * v)⁻¹) := by
    intro N h1 h2 k hk ω
    have hN : (0 : ℝ) < N := by linarith
    have hRle : (R N : ℝ) ≤ N := by exact_mod_cast hRN N
    have hw : fmWeight (R N) N k ^ 2 / B N ^ 2 ≤ (R N * v)⁻¹ + (((N : ℝ) - R N) * v)⁻¹ := by
      rw [hBsq N h1 h2]
      have hRv : 0 < (R N : ℝ) * v := by positivity
      have hSv : 0 < ((N : ℝ) - R N) * v := by positivity
      by_cases hkR : k < R N
      · rw [fmWeight_of_lt hkR]
        calc ((N : ℝ) - R N) ^ 2 / (R N * ((N : ℝ) - R N) * N * v)
            = ((N : ℝ) - R N) / N * (R N * v)⁻¹ := by field_simp
          _ ≤ 1 * (R N * v)⁻¹ := by
            gcongr
            rw [div_le_one hN]
            linarith
          _ ≤ (R N * v)⁻¹ + (((N : ℝ) - R N) * v)⁻¹ := by
            rw [one_mul]; exact le_add_of_nonneg_right (inv_nonneg.2 hSv.le)
      · rw [fmWeight_of_le (not_lt.1 hkR)]
        calc (-(R N : ℝ)) ^ 2 / (R N * ((N : ℝ) - R N) * N * v)
            = (R N : ℝ) / N * (((N : ℝ) - R N) * v)⁻¹ := by field_simp
          _ ≤ 1 * (((N : ℝ) - R N) * v)⁻¹ := by
            gcongr
            rw [div_le_one hN]
            exact hRle
          _ ≤ (R N * v)⁻¹ + (((N : ℝ) - R N) * v)⁻¹ := by
            rw [one_mul]; exact le_add_of_nonneg_left (inv_nonneg.2 hRv.le)
    have hx2 : (score (G N k ω) - μ) ^ 2 ≤ K ^ 2 := by
      have := hxbd (G N k ω)
      nlinarith [abs_nonneg (score (G N k ω) - μ), sq_abs (score (G N k ω) - μ)]
    simp only [hX, mul_pow, div_pow]
    calc fmWeight (R N) N k ^ 2 / B N ^ 2 * (score (G N k ω) - μ) ^ 2
        ≤ ((R N * v)⁻¹ + (((N : ℝ) - R N) * v)⁻¹) * K ^ 2 := by
          gcongr
      _ = K ^ 2 * ((R N * v)⁻¹ + (((N : ℝ) - R N) * v)⁻¹) := by ring
  have hδ : Tendsto (fun N : ℕ ↦ K ^ 2 * ((R N * v)⁻¹ + (((N : ℝ) - R N) * v)⁻¹)) atTop
      (𝓝 0) := by
    have h1 := tendsto_inv_atTop_zero.comp (hRr.atTop_mul_const hscore)
    have h2 := tendsto_inv_atTop_zero.comp (hSr.atTop_mul_const hscore)
    simpa using (h1.add h2).const_mul (K ^ 2)
  have hL : LindebergConditionTriangular X P := by
    intro ε hε
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev, hδ.eventually (gt_mem_nhds (pow_pos hε 2))] with N ⟨h1, h2⟩ hNδ
    symm
    refine sum_eq_zero fun k hk ↦ ?_
    have hzero : ∀ ω, Set.indicator {ω' | ε < |X N k ω'|} (1 : Ω → ℝ) ω = 0 := by
      intro ω
      refine Set.indicator_of_notMem (fun hmem ↦ ?_) _
      change ε < |X N k ω| at hmem
      have hlt : X N k ω ^ 2 < ε ^ 2 := (hXsq N h1 h2 k (mem_range.1 hk) ω).trans_lt hNδ
      have : ε ^ 2 < |X N k ω| ^ 2 := by gcongr
      rw [sq_abs] at this
      linarith
    simp [hzero]
  -- The CLT for the normalized contrast.
  set W : ℕ → Ω → ℝ := fun N ω ↦ ∑ k ∈ range N, X N k ω with hW
  have hWmeas : ∀ N, Measurable (W N) := fun N ↦
    Finset.measurable_sum _ fun k hk ↦ hXmeas N k hk
  have hWclt : TendstoInDistribution W atTop id (fun _ ↦ P) (gaussianReal 0 1) := by
    rw [tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
      (fun N ↦ (hWmeas N).aemeasurable) measurable_id.aemeasurable]
    intro f
    have h := lindeberg_feller_clt_triangular X hXind hXmeas hXmean hXint2 1 one_pos hvar hL f
    have e : (⟨(1 : ℝ) ^ 2, sq_nonneg 1⟩ : NNReal) = 1 := by ext; simp
    rw [e] at h
    exact h.congr fun n ↦
      integral_map (hWmeas n).aemeasurable f.continuous.aestronglyMeasurable
  -- The pooled score variance, normalized by `v`, tends to `1` in probability.
  have hind2 : ∀ N, iIndepFun (fun j : Fin N ↦ fun ω ↦ (score (G N j ω) - μ) ^ 2) P :=
    fun N ↦ (hind N).comp (fun _ y ↦ (score y - μ) ^ 2) fun _ ↦ measurable_of_countable _
  have hind1 : ∀ N, iIndepFun (fun j : Fin N ↦ fun ω ↦ score (G N j ω) - μ) P :=
    fun N ↦ (hind N).comp (fun _ y ↦ score y - μ) fun _ ↦ measurable_of_countable _
  have ha : TendstoInMeasure P
      (fun (N : ℕ) ω ↦ (∑ k ∈ range N, (score (G N k ω) - μ) ^ 2) / N) atTop (fun _ ↦ v) :=
    tendstoInMeasure_rowMean (Y := fun N k ω ↦ (score (G N k ω) - μ) ^ 2) (K := K ^ 2) hind2
      (fun N k ↦ ((hxmeas N k).sub_const μ).pow_const 2)
      (fun N k ω ↦ by
        rw [abs_of_nonneg (sq_nonneg _)]
        have := hxbd (G N k ω)
        nlinarith [abs_nonneg (score (G N k ω) - μ), sq_abs (score (G N k ω) - μ)])
      hxvar
  have hb : TendstoInMeasure P
      (fun (N : ℕ) ω ↦ (∑ k ∈ range N, (score (G N k ω) - μ)) / N) atTop (fun _ ↦ 0) :=
    tendstoInMeasure_rowMean (Y := fun N k ω ↦ score (G N k ω) - μ) (K := K) hind1
      (fun N k ↦ (hxmeas N k).sub_const μ) (fun N k ω ↦ hxbd _)
      (fun N k hk ↦ by
        rw [integral_sub ((hxL2 N k).integrable one_le_two) (integrable_const μ),
          hxmean N k hk]
        simp)
  have hb2 := hb.comp_const_of_continuousAt (f := fun x : ℝ ↦ x ^ 2)
    (continuous_pow 2).continuousAt
  have hab := (tendstoInMeasure_sub_const ha hb2).comp_const_of_continuousAt
    (f := fun x : ℝ ↦ x / v) (continuous_id.div_const v).continuousAt
  set V : ℕ → Ω → ℝ := fun N ω ↦
    ((N : ℝ) * ∑ k ∈ range N, score (G N k ω) ^ 2 - (∑ k ∈ range N, score (G N k ω)) ^ 2) /
      ((N : ℝ) ^ 2 * v) with hV
  have hVeq : ∀ N ω, V N ω = ((∑ k ∈ range N, (score (G N k ω) - μ) ^ 2) / N -
      ((∑ k ∈ range N, (score (G N k ω) - μ)) / N) ^ 2) / v := by
    intro N ω
    simp only [hV]
    have e1 : ∑ k ∈ range N, (score (G N k ω) - μ) ^ 2 =
        ∑ k ∈ range N, score (G N k ω) ^ 2 - 2 * μ * ∑ k ∈ range N, score (G N k ω) +
          N * μ ^ 2 := by
      have : ∀ k, (score (G N k ω) - μ) ^ 2 =
          score (G N k ω) ^ 2 - 2 * μ * score (G N k ω) + μ ^ 2 := fun k ↦ by ring
      simp only [this, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, card_range,
        nsmul_eq_mul]
    have e2 : ∑ k ∈ range N, (score (G N k ω) - μ) = ∑ k ∈ range N, score (G N k ω) - N * μ := by
      simp [sum_sub_distrib]
    rw [e1, e2]
    rcases Nat.eq_zero_or_pos N with hN | hN
    · simp [hN]
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    field_simp
    ring
  have hVlim : TendstoInMeasure P V atTop (fun _ ↦ 1) := by
    have e : (v - (0 : ℝ) ^ 2) / v = 1 := by
      rw [zero_pow two_ne_zero, sub_zero, div_self hscore.ne']
    rw [e] at hab
    exact hab.congr_left fun N ↦ ae_of_all _ fun ω ↦ (hVeq N ω).symm
  have hVmeas : ∀ N, AEMeasurable (V N) P := fun N ↦ by
    simp only [hV]
    fun_prop (disch := exact hxmeas N _)
  -- Slutsky and the continuous mapping theorem.
  have hW2 := hWclt.continuous_comp (g := fun x : ℝ ↦ x ^ 2) (continuous_pow 2)
  have hratio := hW2.div_of_tendstoInMeasure_const one_ne_zero hVlim hVmeas
  have hfm : ∀ N ω, fmStat (R N) N (G N · ω) = W N ω ^ 2 / V N ω := by
    intro N ω
    rw [fmStat_eq (R N) N (hRN N) (G N · ω) μ v hscore]
    simp only [hW, hX, hV, hB]
    congr 2
    rw [sum_div]
    exact sum_congr rfl fun k _ ↦ by ring
  refine (hratio.congr (fun N ↦ ae_of_all _ fun ω ↦ ?_) (ae_of_all _ fun x ↦ ?_)).congr_hasLaw
    (Y := fun x : ℝ ↦ x ^ 2) ⟨by fun_prop, gaussianReal_map_sq⟩ hZ
  · simp [hfm]
  · simp

/-- `χ²₁` has no atom at `0`. -/
private theorem chiSquareMeasure_one_singleton_zero : chiSquareMeasure 1 {0} = 0 := by
  rw [chiSquareMeasure, gammaMeasure, withDensity_apply _ (measurableSet_singleton 0)]
  exact setLIntegral_measure_zero _ _ Real.volume_singleton

/-- **The singular design has no `χ²₁` limit.** If every genotype is almost surely the same
class `c` (zero score variance), the fixed-margin statistic is almost surely `0` for every `N`,
so it converges to the Dirac mass at `0` and not to `χ²₁`: the positive-variance hypothesis of
`tendstoInDistribution_fmStat` cannot be dropped. -/
theorem not_tendstoInDistribution_fmStat_of_const {R : ℕ → ℕ} (hRN : ∀ N, R N ≤ N)
    {G : ℕ → ℕ → Ω → Fin 3} {c : Fin 3} (hc : ∀ N, ∀ k < N, ∀ᵐ ω ∂P, G N k ω = c)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (chiSquareMeasure 1) P') :
    ¬ TendstoInDistribution (fun N ω ↦ fmStat (R N) N (G N · ω)) atTop Z (fun _ ↦ P) P' := by
  intro h
  have h0 : ∀ N, (fun ω ↦ fmStat (R N) N (G N · ω)) =ᵐ[P] fun _ ↦ (0 : ℝ) := by
    intro N
    have hall : ∀ᵐ ω ∂P, ∀ k ∈ range N, G N k ω = c :=
      (eventually_all_finset _).2 fun k hk ↦ hc N k (mem_range.1 hk)
    filter_upwards [hall] with ω hω
    exact fmStat_eq_zero_of_const (hRN N) fun k hk ↦ hω k (mem_range.2 hk)
  have hconst : TendstoInDistribution (fun N ω ↦ fmStat (R N) N (G N · ω)) atTop
      (fun _ : Ω ↦ (0 : ℝ)) (fun _ ↦ P) P :=
    (tendstoInDistribution_const (Z := fun _ : Ω ↦ (0 : ℝ)) (l := atTop)
      aemeasurable_const).congr (fun N ↦ (h0 N).symm) (ae_of_all _ fun _ ↦ rfl)
  have huniq := tendstoInDistribution_unique _ h hconst
  rw [hZ.map_eq, Measure.map_const, measure_univ, one_smul] at huniq
  have := congrArg (fun μ : Measure ℝ ↦ μ {0}) huniq
  simp only [chiSquareMeasure_one_singleton_zero] at this
  simp at this

end Asymptotics

end MathlibExt.Biology.StatisticalGenetics.CochranArmitageFixedMargin
