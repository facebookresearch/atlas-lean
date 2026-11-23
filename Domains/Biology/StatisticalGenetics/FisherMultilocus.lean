/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.StatisticalGenetics.FisherDecomposition
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring

/-!
# Fisher's decomposition and covariances of relatives over independent loci

Finitely many autosomal loci `l : L`; locus `l` has a finite allele set `A l`, allele frequencies
`p l` and symmetric genotypic values `G l`. The population is in Hardy–Weinberg proportions at
every locus and in linkage equilibrium, so the ordered multilocus genotype `g` (a pair of alleles
at every locus) has frequency `genoFreq p g = ∏ l, p l (g l).1 * p l (g l).2`. There is no
epistasis: the genotypic value is the sum over loci, `totalValue G g = ∑ l, G l (g l).1 (g l).2`.
Relatives are formed with Mendelian segregation independently at every locus (unlinked loci) and
with unrelated, non-inbred mates.

Fisher (1918) states that under these assumptions the genetic variance, its additive and
dominance components, and the covariances of relatives are sums of the one-locus quantities of
`FisherDecomposition.lean`. Environmental variation is not modeled.

## Main results

* `multiMean_eq_sum`, `multiGenVar_eq_sum`, `multiAddVar_eq_sum`, `multiDomVar_eq_sum`: the mean,
  genetic, additive and dominance variances are sums over loci.
* `totalValue_eq`: the multilocus decomposition `value = mean + breeding value + ∑ δ`.
* `multiGenVar_eq_multiAddVar_add_multiDomVar`: `V_G = V_A + V_D` over all loci.
* `multiDomVar_le`: every fit additive over all genes at all loci has mean squared error at
  least `V_D`.
* `covParentOffspringMulti_eq_sum`, `covHalfSibsMulti_eq_sum`, `covFullSibsMulti_eq_sum`: the
  covariances of relatives are sums of the one-locus covariances, hence
  `V_A / 2`, `V_A / 4` and `V_A / 2 + V_D / 4` with the multilocus components.

## References

* R. A. Fisher, *The correlation between relatives on the supposition of Mendelian
  inheritance*, Trans. R. Soc. Edinb. 52 (1918), 399–433.
* D. S. Falconer, T. F. C. Mackay, *Introduction to Quantitative Genetics*, 4th ed., Longman,
  1996, ch. 8–9.
-/

@[expose] public section

open Finset
open MathlibExt.Biology.StatisticalGenetics.FisherDecomposition

namespace Domains.Biology.StatisticalGenetics.FisherMultilocus

/-- The weight `∏ l, p l (g l).1 * p l (g l).2` of the ordered multilocus genotype `g`; when every
`p l` is a probability vector, it is the frequency of `g` under Hardy–Weinberg proportions at every
locus and linkage equilibrium. -/
noncomputable def genoFreq {L : Type*} [Fintype L] {A : L → Type*} (p : ∀ l, A l → ℝ)
    (g : ∀ l, A l × A l) : ℝ :=
  ∏ l, (p l (g l).1 * p l (g l).2)

/-- The genotypic value of `g` with no epistasis: the sum of the one-locus values. -/
noncomputable def totalValue {L : Type*} [Fintype L] {A : L → Type*}
    (G : ∀ l, A l → A l → ℝ) (g : ∀ l, A l × A l) : ℝ :=
  ∑ l, G l (g l).1 (g l).2

/-- The weighted sum `∑ g, genoFreq p g * totalValue G g`; when every `p l` is a probability vector,
it is the population mean genotypic value over all loci. -/
noncomputable def multiMean {L : Type*} [Fintype L] [DecidableEq L] {A : L → Type*}
    [∀ l, Fintype (A l)] (p : ∀ l, A l → ℝ) (G : ∀ l, A l → A l → ℝ) : ℝ :=
  ∑ g : (∀ l, A l × A l), genoFreq p g * totalValue G g

/-- The weighted sum `∑ g, genoFreq p g * (totalValue G g - multiMean p G) ^ 2`; when every `p l` is
a probability vector, it is the genetic variance over all loci. -/
noncomputable def multiGenVar {L : Type*} [Fintype L] [DecidableEq L] {A : L → Type*}
    [∀ l, Fintype (A l)] (p : ∀ l, A l → ℝ) (G : ∀ l, A l → A l → ℝ) : ℝ :=
  ∑ g : (∀ l, A l × A l), genoFreq p g * (totalValue G g - multiMean p G) ^ 2

/-- The breeding value of `g`: the sum over loci of the one-locus average effects of its two
genes. -/
noncomputable def breedingValue {L : Type*} [Fintype L] {A : L → Type*} [∀ l, Fintype (A l)]
    (p : ∀ l, A l → ℝ) (G : ∀ l, A l → A l → ℝ) (g : ∀ l, A l × A l) : ℝ :=
  ∑ l, (avgEffect (p l) (G l) (g l).1 + avgEffect (p l) (G l) (g l).2)

/-- The additive genetic variance over all loci: the weighted sum of squares
`∑ g, genoFreq p g * breedingValue p G g ^ 2` of the breeding value. When every `p l` is a
probability vector, the breeding value has mean `0` and this is its variance. -/
noncomputable def multiAddVar {L : Type*} [Fintype L] [DecidableEq L] {A : L → Type*}
    [∀ l, Fintype (A l)] (p : ∀ l, A l → ℝ) (G : ∀ l, A l → A l → ℝ) : ℝ :=
  ∑ g : (∀ l, A l × A l), genoFreq p g * breedingValue p G g ^ 2

/-- The dominance variance over all loci: the weighted sum of squares of the summed dominance
deviations. When every `p l` is a probability vector, they have mean `0` and this is their
variance. -/
noncomputable def multiDomVar {L : Type*} [Fintype L] [DecidableEq L] {A : L → Type*}
    [∀ l, Fintype (A l)] (p : ∀ l, A l → ℝ) (G : ∀ l, A l → A l → ℝ) : ℝ :=
  ∑ g : (∀ l, A l × A l), genoFreq p g * (∑ l, domDev (p l) (G l) (g l).1 (g l).2) ^ 2

/-- The covariance of a parent and its offspring over unlinked loci. At locus `l` the configuration
`(i, j, k, b)` is the parent's genotype `(i, j)`, the mate's gene `k` and the choice `b` of the
transmitted parental gene `cond b i j`, with weight `p i p j p k / 2`; configurations at different
loci are independent, and both genotypic values are centred at `multiMean p G`. For real weights it
is this weighted sum; when every `p l` is a probability vector, it is the covariance of the
genotypic values of a parent and its offspring. -/
noncomputable def covParentOffspringMulti {L : Type*} [Fintype L] [DecidableEq L]
    {A : L → Type*} [∀ l, Fintype (A l)] (p : ∀ l, A l → ℝ) (G : ∀ l, A l → A l → ℝ) : ℝ :=
  ∑ x : (∀ l, A l × A l × A l × Bool),
    (∏ l, p l (x l).1 * p l (x l).2.1 * p l (x l).2.2.1 / 2) *
      ((∑ l, G l (x l).1 (x l).2.1 - multiMean p G) *
        (∑ l, G l (cond (x l).2.2.2 (x l).1 (x l).2.1) (x l).2.2.1 - multiMean p G))

/-- The covariance of half sibs over unlinked loci. At locus `l` the configuration
`(i, j, k, m, b, b')` is the common parent's genotype `(i, j)`, the genes `k` and `m` from two
unrelated mates, and the independent choices `b`, `b'` of the parental gene transmitted to each
offspring, with weight `p i p j p k p m / 4`; loci are independent, and both genotypic values are
centred at `multiMean p G`. For real weights it is this weighted sum; when every `p l` is a
probability vector, it is the covariance of the genotypic values of two half sibs. -/
noncomputable def covHalfSibsMulti {L : Type*} [Fintype L] [DecidableEq L] {A : L → Type*}
    [∀ l, Fintype (A l)] (p : ∀ l, A l → ℝ) (G : ∀ l, A l → A l → ℝ) : ℝ :=
  ∑ x : (∀ l, A l × A l × A l × A l × Bool × Bool),
    (∏ l, p l (x l).1 * p l (x l).2.1 * p l (x l).2.2.1 * p l (x l).2.2.2.1 / 4) *
      ((∑ l, G l (cond (x l).2.2.2.2.1 (x l).1 (x l).2.1) (x l).2.2.1 - multiMean p G) *
        (∑ l, G l (cond (x l).2.2.2.2.2 (x l).1 (x l).2.1) (x l).2.2.2.1 - multiMean p G))

/-- The covariance of full sibs over unlinked loci. At locus `l` the configuration
`((i, j, k, m), (b, b', e, e'))` is the sire's genotype `(i, j)`, the dam's genotype `(k, m)`, and
the independent transmission choices: the first offspring receives `cond b i j` and `cond e k m`,
the second `cond b' i j` and `cond e' k m`; the weight is `p i p j p k p m / 16` and loci are
independent, and both genotypic values are centred at `multiMean p G`. For real weights it is this
weighted sum; when every `p l` is a probability vector, it is the covariance of the genotypic values
of two full sibs. -/
noncomputable def covFullSibsMulti {L : Type*} [Fintype L] [DecidableEq L] {A : L → Type*}
    [∀ l, Fintype (A l)] (p : ∀ l, A l → ℝ) (G : ∀ l, A l → A l → ℝ) : ℝ :=
  ∑ x : (∀ l, (A l × A l × A l × A l) × (Bool × Bool × Bool × Bool)),
    (∏ l, p l (x l).1.1 * p l (x l).1.2.1 * p l (x l).1.2.2.1 * p l (x l).1.2.2.2 / 16) *
      ((∑ l, G l (cond (x l).2.1 (x l).1.1 (x l).1.2.1)
          (cond (x l).2.2.2.1 (x l).1.2.2.1 (x l).1.2.2.2) - multiMean p G) *
        (∑ l, G l (cond (x l).2.2.1 (x l).1.1 (x l).1.2.1)
          (cond (x l).2.2.2.2 (x l).1.2.2.1 (x l).1.2.2.2) - multiMean p G))

private theorem product_coordinate {L : Type*} [Fintype L] [DecidableEq L]
    {Ω : L → Type*} [∀ l, Fintype (Ω l)] (q : ∀ l, Ω l → ℝ)
    (hq : ∀ l, ∑ x, q l x = 1) (F : ∀ l, Ω l → ℝ) (m : L) :
    ∑ x : ∀ l, Ω l, (∏ l, q l (x l)) * F m (x m) = ∑ y, q m y * F m y := by
  have he : ∀ x : ∀ l, Ω l, (∏ l, q l (x l)) * F m (x m) =
      ∏ l, q l (x l) * (if l = m then F l (x l) else 1) := by
    intro x
    rw [prod_mul_distrib]
    simp
  simp only [he]
  rw [← Fintype.prod_sum (fun l y => q l y * (if l = m then F l y else 1))]
  rw [prod_eq_single m]
  · simp
  · intro l _ hl
    simp [hl, hq l]
  · simp

private theorem product_pair {L : Type*} [Fintype L] [DecidableEq L]
    {Ω : L → Type*} [∀ l, Fintype (Ω l)] (q : ∀ l, Ω l → ℝ)
    (hq : ∀ l, ∑ x, q l x = 1) (F H : ∀ l, Ω l → ℝ) (l m : L) (hlm : l ≠ m) :
    ∑ x : ∀ l, Ω l, (∏ i, q i (x i)) * (F l (x l) * H m (x m)) =
      (∑ y, q l y * F l y) * (∑ y, q m y * H m y) := by
  have he : ∀ x : ∀ l, Ω l, (∏ i, q i (x i)) * (F l (x l) * H m (x m)) =
      ∏ i, q i (x i) *
        ((if i = l then F i (x i) else 1) * (if i = m then H i (x i) else 1)) := by
    intro x
    rw [prod_mul_distrib, prod_mul_distrib]
    simp
  have hi : ∀ i, (∑ y, q i y *
      ((if i = l then F i y else 1) * (if i = m then H i y else 1))) =
      (if i = l then ∑ y, q i y * F i y else 1) *
        (if i = m then ∑ y, q i y * H i y else 1) := by
    intro i
    by_cases hil : i = l
    · subst i
      simp [hlm]
    · by_cases him : i = m
      · subst i
        simp [hil]
      · simp [hil, him, hq i]
  simp only [he]
  rw [← Fintype.prod_sum (fun i y => q i y *
    ((if i = l then F i y else 1) * (if i = m then H i y else 1)))]
  simp only [hi, prod_mul_distrib]
  simp

private theorem product_sum {L : Type*} [Fintype L] [DecidableEq L]
    {Ω : L → Type*} [∀ l, Fintype (Ω l)] (q : ∀ l, Ω l → ℝ)
    (hq : ∀ l, ∑ x, q l x = 1) (F : ∀ l, Ω l → ℝ) :
    ∑ x : ∀ l, Ω l, (∏ l, q l (x l)) * (∑ l, F l (x l)) =
      ∑ l, ∑ y, q l y * F l y := by
  simp only [mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun l _ => product_coordinate q hq F l

private theorem product_centered {L : Type*} [Fintype L] [DecidableEq L]
    {Ω : L → Type*} [∀ l, Fintype (Ω l)] (q : ∀ l, Ω l → ℝ)
    (hq : ∀ l, ∑ x, q l x = 1) (F H : ∀ l, Ω l → ℝ)
    (hF : ∀ l, ∑ y, q l y * F l y = 0) :
    ∑ x : ∀ l, Ω l, (∏ l, q l (x l)) * ((∑ l, F l (x l)) * (∑ l, H l (x l))) =
      ∑ l, ∑ y, q l y * (F l y * H l y) := by
  simp only [sum_mul, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro l _
  rw [sum_comm, sum_eq_single l]
  · exact product_coordinate q hq (fun i y => F i y * H i y) l
  · intro m _ hml
    rw [product_pair q hq F H m l hml, hF, zero_mul]
  · simp

private theorem pair_mass {A : Type*} [Fintype A] {p : A → ℝ}
    (hp : ∑ i, p i = 1) : ∑ x : A × A, p x.1 * p x.2 = 1 := by
  simp only [Fintype.sum_prod_type, ← mul_sum, hp, mul_one]

private theorem pair_center {A : Type*} [Fintype A] {p : A → ℝ}
    (hp : ∑ i, p i = 1) (G : A → A → ℝ) :
    ∑ x : A × A, p x.1 * p x.2 * (G x.1 x.2 - meanValue p G) = 0 := by
  simp only [mul_sub, sum_sub_distrib, ← sum_mul, pair_mass hp, one_mul]
  simp only [Fintype.sum_prod_type, meanValue, sub_self]

private theorem pair_add_center {A : Type*} [Fintype A] {p : A → ℝ}
    (hp : ∑ i, p i = 1) (G : A → A → ℝ) :
    ∑ x : A × A, p x.1 * p x.2 * (avgEffect p G x.1 + avgEffect p G x.2) = 0 := by
  simp only [Fintype.sum_prod_type, mul_add, sum_add_distrib]
  have h := sum_mul_avgEffect hp G
  simp only [mul_assoc, ← mul_sum, ← sum_mul, hp, one_mul, h, mul_zero, sum_const_zero,
    zero_add]

private theorem pair_dom_center {A : Type*} [Fintype A] {p : A → ℝ}
    (hp : ∑ i, p i = 1) (G : A → A → ℝ) :
    ∑ x : A × A, p x.1 * p x.2 * domDev p G x.1 x.2 = 0 := by
  simp only [Fintype.sum_prod_type, mul_assoc, ← mul_sum, sum_mul_domDev_right hp G,
    mul_zero, sum_const_zero]

private theorem pair_add_sq {A : Type*} [Fintype A] {p : A → ℝ}
    (hp : ∑ i, p i = 1) (G : A → A → ℝ) :
    ∑ x : A × A, p x.1 * p x.2 * (avgEffect p G x.1 + avgEffect p G x.2) ^ 2 =
      addVar p G := by
  let α := avgEffect p G
  have he : ∀ i j, p i * p j * (α i + α j) ^ 2 =
      p i * (p j * α i ^ 2) + p j * (p i * α j ^ 2) +
        2 * ((p i * α i) * (p j * α j)) := fun i j => by ring
  have t1 : ∑ i, ∑ j, p i * (p j * α i ^ 2) = ∑ i, p i * α i ^ 2 := by
    simp only [← mul_sum, ← sum_mul, hp, one_mul]
  have t2 : ∑ i, ∑ j, p j * (p i * α j ^ 2) = ∑ i, p i * α i ^ 2 := by
    rw [sum_comm]
    exact t1
  have t3 : ∑ i, ∑ j, 2 * ((p i * α i) * (p j * α j)) = 0 := by
    simp only [← mul_sum, sum_mul_avgEffect hp G, mul_zero, sum_const_zero, α]
  change ∑ x : A × A, p x.1 * p x.2 * (α x.1 + α x.2) ^ 2 = _
  simp only [Fintype.sum_prod_type, he, sum_add_distrib, t1, t2, t3, addVar]
  change (∑ i, p i * α i ^ 2) + (∑ i, p i * α i ^ 2) + 0 =
    2 * ∑ i, p i * α i ^ 2
  ring

private theorem parent_mass {A : Type*} [Fintype A] {p : A → ℝ}
    (hp : ∑ i, p i = 1) :
    ∑ x : A × A × A × Bool, p x.1 * p x.2.1 * p x.2.2.1 / 2 = 1 := by
  have hb : ∀ i j k, (∑ b : Bool, p i * p j * p k / 2) = p i * p j * p k := by
    intro i j k
    simp only [Fintype.sum_bool]
    ring
  simp only [Fintype.sum_prod_type, hb, ← mul_sum, hp, mul_one]

private theorem half_mass {A : Type*} [Fintype A] {p : A → ℝ}
    (hp : ∑ i, p i = 1) :
    ∑ x : A × A × A × A × Bool × Bool, p x.1 * p x.2.1 * p x.2.2.1 * p x.2.2.2.1 / 4 =
      1 := by
  have hb : ∀ i j k m, (∑ b : Bool, ∑ b' : Bool, p i * p j * p k * p m / 4) =
      p i * p j * p k * p m := by
    intro i j k m
    simp only [Fintype.sum_bool]
    ring
  simp only [Fintype.sum_prod_type, hb, ← mul_sum, hp, mul_one]

private theorem full_mass {A : Type*} [Fintype A] {p : A → ℝ}
    (hp : ∑ i, p i = 1) :
    ∑ x : (A × A × A × A) × (Bool × Bool × Bool × Bool),
      p x.1.1 * p x.1.2.1 * p x.1.2.2.1 * p x.1.2.2.2 / 16 = 1 := by
  have hb : ∀ i j k m, (∑ b : Bool, ∑ b' : Bool, ∑ e : Bool, ∑ e' : Bool,
      p i * p j * p k * p m / 16) = p i * p j * p k * p m := by
    intro i j k m
    simp only [Fintype.sum_bool]
    ring
  simp only [Fintype.sum_prod_type, hb, ← mul_sum, hp, mul_one]

private theorem parent_center {A : Type*} [Fintype A] {p : A → ℝ}
    (hp : ∑ i, p i = 1) (G : A → A → ℝ) :
    ∑ x : A × A × A × Bool, p x.1 * p x.2.1 * p x.2.2.1 / 2 *
      (G x.1 x.2.1 - meanValue p G) = 0 := by
  have hb : ∀ i j k, (∑ b : Bool, p i * p j * p k / 2 *
      (G i j - meanValue p G)) = p i * p j * p k * (G i j - meanValue p G) := by
    intro i j k
    simp only [Fintype.sum_bool]
    ring
  simp only [Fintype.sum_prod_type]
  simp_rw [hb]
  simp only [mul_assoc, ← mul_sum, ← sum_mul, hp, one_mul]
  simpa only [Fintype.sum_prod_type, mul_assoc, ← mul_sum] using pair_center hp G

private theorem half_center {A : Type*} [Fintype A] {p : A → ℝ}
    (hp : ∑ i, p i = 1) (G : A → A → ℝ) :
    ∑ x : A × A × A × A × Bool × Bool,
      p x.1 * p x.2.1 * p x.2.2.1 * p x.2.2.2.1 / 4 *
        (G (cond x.2.2.2.2.1 x.1 x.2.1) x.2.2.1 - meanValue p G) = 0 := by
  have hrow : ∀ i, ∑ j, p j * (G i j - meanValue p G) = avgEffect p G i := by
    intro i
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, hp, one_mul, avgEffect]
  have hkm : ∀ i j, (∑ k, ∑ m, ∑ b : Bool, ∑ b' : Bool,
      p i * p j * p k * p m / 4 * (G (cond b i j) k - meanValue p G)) =
      p i * p j / 2 * (avgEffect p G i + avgEffect p G j) := by
    intro i j
    have he : ∀ k m, (∑ b : Bool, ∑ b' : Bool,
        p i * p j * p k * p m / 4 * (G (cond b i j) k - meanValue p G)) =
        p i * p j / 2 * p m *
          (p k * (G i k - meanValue p G) + p k * (G j k - meanValue p G)) := by
      intro k m
      simp only [Fintype.sum_bool, Bool.cond_true, Bool.cond_false]
      ring
    simp_rw [he]
    simp only [mul_assoc, ← sum_mul, hp, one_mul, ← mul_sum, sum_add_distrib, hrow]
  simp only [Fintype.sum_prod_type]
  simp_rw [hkm]
  simp only [div_mul_eq_mul_div, ← sum_div]
  have ha : ∑ i, ∑ j, p i * p j * (avgEffect p G i + avgEffect p G j) = 0 := by
    simpa only [Fintype.sum_prod_type] using pair_add_center hp G
  rw [ha, zero_div]

private theorem full_center {A : Type*} [Fintype A] {p : A → ℝ}
    (hp : ∑ i, p i = 1) (G : A → A → ℝ) :
    ∑ x : (A × A × A × A) × (Bool × Bool × Bool × Bool),
      p x.1.1 * p x.1.2.1 * p x.1.2.2.1 * p x.1.2.2.2 / 16 *
        (G (cond x.2.1 x.1.1 x.1.2.1) (cond x.2.2.2.1 x.1.2.2.1 x.1.2.2.2) -
          meanValue p G) = 0 := by
  let X := fun i j => G i j - meanValue p G
  have hrow : ∀ i, ∑ j, p j * X i j = avgEffect p G i := by
    intro i
    simp only [X, mul_sub, sum_sub_distrib, ← sum_mul, hp, one_mul, avgEffect]
  have hkm : ∀ i j, (∑ k, ∑ m, ∑ b : Bool, ∑ b' : Bool, ∑ e : Bool, ∑ e' : Bool,
      p i * p j * p k * p m / 16 * X (cond b i j) (cond e k m)) =
      p i * p j / 2 * (avgEffect p G i + avgEffect p G j) := by
    intro i j
    have he : ∀ k m, (∑ b : Bool, ∑ b' : Bool, ∑ e : Bool, ∑ e' : Bool,
        p i * p j * p k * p m / 16 * X (cond b i j) (cond e k m)) =
        p i * p j / 4 * (p m * (p k * X i k) + p k * (p m * X i m) +
          p m * (p k * X j k) + p k * (p m * X j m)) := by
      intro k m
      simp only [Fintype.sum_bool, Bool.cond_true, Bool.cond_false]
      ring
    simp_rw [he]
    simp only [← mul_sum, sum_add_distrib, ← sum_mul, hp, one_mul, hrow]
    ring
  change (∑ x : (A × A × A × A) × (Bool × Bool × Bool × Bool),
    p x.1.1 * p x.1.2.1 * p x.1.2.2.1 * p x.1.2.2.2 / 16 *
      X (cond x.2.1 x.1.1 x.1.2.1) (cond x.2.2.2.1 x.1.2.2.1 x.1.2.2.2)) = 0
  simp only [Fintype.sum_prod_type]
  simp_rw [hkm]
  simp only [div_mul_eq_mul_div, ← sum_div]
  have ha : ∑ i, ∑ j, p i * p j * (avgEffect p G i + avgEffect p G j) = 0 := by
    simpa only [Fintype.sum_prod_type] using pair_add_center hp G
  rw [ha, zero_div]

private theorem pair_dom_add {A : Type*} [Fintype A] {p : A → ℝ}
    (hp : ∑ i, p i = 1) {G : A → A → ℝ} (hG : ∀ i j, G i j = G j i)
    (b : A → ℝ) :
    ∑ x : A × A, p x.1 * p x.2 * (domDev p G x.1 x.2 * (b x.1 + b x.2)) = 0 := by
  have he : ∀ i j, p i * p j * (domDev p G i j * (b i + b j)) =
      (p i * b i) * (p j * domDev p G i j) +
        (p j * b j) * (p i * domDev p G i j) := fun i j => by ring
  have t1 : ∑ i, ∑ j, (p i * b i) * (p j * domDev p G i j) = 0 := by
    simp only [← mul_sum, sum_mul_domDev_right hp G, mul_zero, sum_const_zero]
  have t2 : ∑ i, ∑ j, (p j * b j) * (p i * domDev p G i j) = 0 := by
    rw [sum_comm]
    simp only [← mul_sum, sum_mul_domDev_left hp hG, mul_zero, sum_const_zero]
  simp only [Fintype.sum_prod_type, he, sum_add_distrib, t1, t2, zero_add]

/-- If the allele weights sum to `1` at every locus (`∑ a, p l a = 1`; no sign condition), the mean
genotypic value is the sum of the one-locus means. -/
theorem multiMean_eq_sum {L : Type*} [Fintype L] [DecidableEq L] {A : L → Type*}
    [∀ l, Fintype (A l)] {p : ∀ l, A l → ℝ} (hp : ∀ l, ∑ a, p l a = 1)
    (G : ∀ l, A l → A l → ℝ) : multiMean p G = ∑ l, meanValue (p l) (G l) := by
  unfold multiMean genoFreq totalValue
  rw [product_sum (Ω := fun l => A l × A l)
    (fun l x => p l x.1 * p l x.2) (fun l => pair_mass (hp l))
    (fun l x => G l x.1 x.2)]
  simp only [Fintype.sum_prod_type, meanValue]

/-- If the allele weights sum to `1` at every locus (`∑ a, p l a = 1`; no sign condition), every
genotypic value decomposes as the mean, plus the breeding value, plus the sum of the one-locus
dominance deviations. -/
theorem totalValue_eq {L : Type*} [Fintype L] [DecidableEq L] {A : L → Type*}
    [∀ l, Fintype (A l)] {p : ∀ l, A l → ℝ} (hp : ∀ l, ∑ a, p l a = 1)
    (G : ∀ l, A l → A l → ℝ) (g : ∀ l, A l × A l) :
    totalValue G g = multiMean p G + breedingValue p G g +
      ∑ l, domDev (p l) (G l) (g l).1 (g l).2 := by
  rw [multiMean_eq_sum hp]
  simp only [totalValue, breedingValue, domDev, sum_sub_distrib, sum_add_distrib]
  ring

/-- If the allele weights sum to `1` at every locus (`∑ a, p l a = 1`; no sign condition), the
genetic variance is the sum of the one-locus genetic variances. -/
theorem multiGenVar_eq_sum {L : Type*} [Fintype L] [DecidableEq L] {A : L → Type*}
    [∀ l, Fintype (A l)] {p : ∀ l, A l → ℝ} (hp : ∀ l, ∑ a, p l a = 1)
    (G : ∀ l, A l → A l → ℝ) : multiGenVar p G = ∑ l, genVar (p l) (G l) := by
  simp only [multiGenVar, genoFreq, totalValue, multiMean_eq_sum hp, ← sum_sub_distrib,
    pow_two]
  simpa only [Fintype.sum_prod_type, genVar, pow_two] using
    product_centered (Ω := fun l => A l × A l)
      (fun l x => p l x.1 * p l x.2) (fun l => pair_mass (hp l))
      (fun l x => G l x.1 x.2 - meanValue (p l) (G l))
      (fun l x => G l x.1 x.2 - meanValue (p l) (G l))
      (fun l => pair_center (hp l) (G l))

/-- If the allele weights sum to `1` at every locus (`∑ a, p l a = 1`; no sign condition), the
additive genetic variance is the sum of the one-locus additive variances. -/
theorem multiAddVar_eq_sum {L : Type*} [Fintype L] [DecidableEq L] {A : L → Type*}
    [∀ l, Fintype (A l)] {p : ∀ l, A l → ℝ} (hp : ∀ l, ∑ a, p l a = 1)
    (G : ∀ l, A l → A l → ℝ) : multiAddVar p G = ∑ l, addVar (p l) (G l) := by
  unfold multiAddVar genoFreq breedingValue
  simp only [pow_two]
  rw [product_centered (Ω := fun l => A l × A l)
    (fun l x => p l x.1 * p l x.2) (fun l => pair_mass (hp l))
    (fun l x => avgEffect (p l) (G l) x.1 + avgEffect (p l) (G l) x.2)
    (fun l x => avgEffect (p l) (G l) x.1 + avgEffect (p l) (G l) x.2)
    (fun l => pair_add_center (hp l) (G l))]
  simp only [← pow_two, pair_add_sq (hp _) (G _)]

/-- If the allele weights sum to `1` at every locus (`∑ a, p l a = 1`; no sign condition), the
dominance variance is the sum of the one-locus dominance variances. -/
theorem multiDomVar_eq_sum {L : Type*} [Fintype L] [DecidableEq L] {A : L → Type*}
    [∀ l, Fintype (A l)] {p : ∀ l, A l → ℝ} (hp : ∀ l, ∑ a, p l a = 1)
    (G : ∀ l, A l → A l → ℝ) : multiDomVar p G = ∑ l, domVar (p l) (G l) := by
  unfold multiDomVar genoFreq
  simp only [pow_two]
  simpa only [Fintype.sum_prod_type, domVar, pow_two] using
    product_centered (Ω := fun l => A l × A l)
      (fun l x => p l x.1 * p l x.2) (fun l => pair_mass (hp l))
      (fun l x => domDev (p l) (G l) x.1 x.2)
      (fun l x => domDev (p l) (G l) x.1 x.2)
      (fun l => pair_dom_center (hp l) (G l))

/-- **Fisher's decomposition over independent loci.** For allele weights summing to `1` at every
locus and symmetric genotypic values (`G l i j = G l j i`), `V_G = V_A + V_D`. -/
theorem multiGenVar_eq_multiAddVar_add_multiDomVar {L : Type*} [Fintype L] [DecidableEq L]
    {A : L → Type*} [∀ l, Fintype (A l)] {p : ∀ l, A l → ℝ} (hp : ∀ l, ∑ a, p l a = 1)
    {G : ∀ l, A l → A l → ℝ} (hG : ∀ l i j, G l i j = G l j i) :
    multiGenVar p G = multiAddVar p G + multiDomVar p G := by
  rw [multiGenVar_eq_sum hp, multiAddVar_eq_sum hp, multiDomVar_eq_sum hp,
    ← sum_add_distrib]
  exact sum_congr rfl fun l _ => genVar_eq_addVar_add_domVar (hp l) (hG l)

/-- **Least squares over independent loci.** For allele frequencies (`0 ≤ p l a` and
`∑ a, p l a = 1` at every locus) and symmetric genotypic values, every fit
`c + ∑ l, (a l i_l + a l j_l)` of the genotypic value by a function additive over all genes at all
loci has mean squared error at least `V_D`. -/
theorem multiDomVar_le {L : Type*} [Fintype L] [DecidableEq L] {A : L → Type*}
    [∀ l, Fintype (A l)] {p : ∀ l, A l → ℝ} (hp0 : ∀ l a, 0 ≤ p l a)
    (hp : ∀ l, ∑ a, p l a = 1) {G : ∀ l, A l → A l → ℝ} (hG : ∀ l i j, G l i j = G l j i)
    (c : ℝ) (a : ∀ l, A l → ℝ) :
    multiDomVar p G ≤ ∑ g : (∀ l, A l × A l), genoFreq p g *
      (totalValue G g - c - ∑ l, (a l (g l).1 + a l (g l).2)) ^ 2 := by
  let D := fun g : ∀ l, A l × A l => ∑ l, domDev (p l) (G l) (g l).1 (g l).2
  let e := fun l i => avgEffect (p l) (G l) i - a l i
  let E := fun g : ∀ l, A l × A l => ∑ l, (e l (g l).1 + e l (g l).2)
  let k := multiMean p G - c
  have hD : ∑ g, genoFreq p g * D g = 0 := by
    change ∑ g, (∏ l, p l (g l).1 * p l (g l).2) * D g = 0
    rw [product_sum (Ω := fun l => A l × A l) _ (fun l => pair_mass (hp l))
      (fun l x => domDev (p l) (G l) x.1 x.2)]
    simp only [pair_dom_center (hp _) (G _), sum_const_zero]
  have hDE : ∑ g, genoFreq p g * (D g * E g) = 0 := by
    change ∑ g, (∏ l, p l (g l).1 * p l (g l).2) * (D g * E g) = 0
    rw [product_centered (Ω := fun l => A l × A l) _ (fun l => pair_mass (hp l))
      (fun l x => domDev (p l) (G l) x.1 x.2)
      (fun l x => e l x.1 + e l x.2) (fun l => pair_dom_center (hp l) (G l))]
    simp only [pair_dom_add (hp _) (hG _) (e _), sum_const_zero]
  have he : ∀ g, genoFreq p g *
      (totalValue G g - c - ∑ l, (a l (g l).1 + a l (g l).2)) ^ 2 =
      genoFreq p g * D g ^ 2 + 2 * (genoFreq p g * (D g * E g)) +
        2 * k * (genoFreq p g * D g) + genoFreq p g * (E g + k) ^ 2 := by
    intro g
    rw [totalValue_eq hp G g]
    simp only [D, E, e, k, breedingValue, sum_sub_distrib, sum_add_distrib]
    ring
  have hn : 0 ≤ ∑ g, genoFreq p g * (E g + k) ^ 2 :=
    sum_nonneg fun g _ => mul_nonneg
      (prod_nonneg fun l _ => mul_nonneg (hp0 l _) (hp0 l _)) (sq_nonneg _)
  simp_rw [he]
  change (∑ g, genoFreq p g * D g ^ 2) ≤ _
  simp only [sum_add_distrib, ← mul_sum, hDE, hD, mul_zero, add_zero]
  exact le_add_of_nonneg_right hn

/-- If the allele weights sum to `1` at every locus (`∑ a, p l a = 1`; no sign condition), the
parent–offspring covariance is the sum of the one-locus covariances. -/
theorem covParentOffspringMulti_eq_sum {L : Type*} [Fintype L] [DecidableEq L]
    {A : L → Type*} [∀ l, Fintype (A l)] {p : ∀ l, A l → ℝ} (hp : ∀ l, ∑ a, p l a = 1)
    (G : ∀ l, A l → A l → ℝ) :
    covParentOffspringMulti p G = ∑ l, covParentOffspring (p l) (G l) := by
  simp only [covParentOffspringMulti, multiMean_eq_sum hp, ← sum_sub_distrib]
  simpa only [Fintype.sum_prod_type, covParentOffspring] using
    product_centered (Ω := fun l => A l × A l × A l × Bool)
      (fun l x => p l x.1 * p l x.2.1 * p l x.2.2.1 / 2)
      (fun l => parent_mass (hp l))
      (fun l x => G l x.1 x.2.1 - meanValue (p l) (G l))
      (fun l x => G l (cond x.2.2.2 x.1 x.2.1) x.2.2.1 - meanValue (p l) (G l))
      (fun l => parent_center (hp l) (G l))

/-- **Parent and offspring over independent loci (Fisher 1918).** For allele weights summing to `1`
at every locus and symmetric genotypic values, `Cov(P, O) = V_A / 2`. -/
theorem covParentOffspringMulti_eq {L : Type*} [Fintype L] [DecidableEq L] {A : L → Type*}
    [∀ l, Fintype (A l)] {p : ∀ l, A l → ℝ} (hp : ∀ l, ∑ a, p l a = 1)
    {G : ∀ l, A l → A l → ℝ} (hG : ∀ l i j, G l i j = G l j i) :
    covParentOffspringMulti p G = multiAddVar p G / 2 := by
  rw [covParentOffspringMulti_eq_sum hp, multiAddVar_eq_sum hp, sum_div]
  exact sum_congr rfl fun l _ => covParentOffspring_eq (hp l) (hG l)

/-- If the allele weights sum to `1` at every locus (`∑ a, p l a = 1`; no sign condition), the
half-sib covariance is the sum of the one-locus covariances. -/
theorem covHalfSibsMulti_eq_sum {L : Type*} [Fintype L] [DecidableEq L] {A : L → Type*}
    [∀ l, Fintype (A l)] {p : ∀ l, A l → ℝ} (hp : ∀ l, ∑ a, p l a = 1)
    (G : ∀ l, A l → A l → ℝ) :
    covHalfSibsMulti p G = ∑ l, covHalfSibs (p l) (G l) := by
  simp only [covHalfSibsMulti, multiMean_eq_sum hp, ← sum_sub_distrib]
  simpa only [Fintype.sum_prod_type, covHalfSibs] using
    product_centered (Ω := fun l => A l × A l × A l × A l × Bool × Bool)
      (fun l x => p l x.1 * p l x.2.1 * p l x.2.2.1 * p l x.2.2.2.1 / 4)
      (fun l => half_mass (hp l))
      (fun l x => G l (cond x.2.2.2.2.1 x.1 x.2.1) x.2.2.1 - meanValue (p l) (G l))
      (fun l x => G l (cond x.2.2.2.2.2 x.1 x.2.1) x.2.2.2.1 - meanValue (p l) (G l))
      (fun l => half_center (hp l) (G l))

/-- **Half sibs over independent loci (Fisher 1918).** For allele weights summing to `1` at every
locus and any real genotypic values, `Cov(HS) = V_A / 4`. -/
theorem covHalfSibsMulti_eq {L : Type*} [Fintype L] [DecidableEq L] {A : L → Type*}
    [∀ l, Fintype (A l)] {p : ∀ l, A l → ℝ} (hp : ∀ l, ∑ a, p l a = 1)
    (G : ∀ l, A l → A l → ℝ) : covHalfSibsMulti p G = multiAddVar p G / 4 := by
  rw [covHalfSibsMulti_eq_sum hp, multiAddVar_eq_sum hp, sum_div]
  exact sum_congr rfl fun l _ => covHalfSibs_eq (hp l) (G l)

/-- If the allele weights sum to `1` at every locus (`∑ a, p l a = 1`; no sign condition), the
full-sib covariance is the sum of the one-locus covariances. -/
theorem covFullSibsMulti_eq_sum {L : Type*} [Fintype L] [DecidableEq L] {A : L → Type*}
    [∀ l, Fintype (A l)] {p : ∀ l, A l → ℝ} (hp : ∀ l, ∑ a, p l a = 1)
    (G : ∀ l, A l → A l → ℝ) :
    covFullSibsMulti p G = ∑ l, covFullSibs (p l) (G l) := by
  simp only [covFullSibsMulti, multiMean_eq_sum hp, ← sum_sub_distrib]
  simpa only [Fintype.sum_prod_type, covFullSibs] using
    product_centered (Ω := fun l => (A l × A l × A l × A l) ×
      (Bool × Bool × Bool × Bool))
      (fun l x => p l x.1.1 * p l x.1.2.1 * p l x.1.2.2.1 * p l x.1.2.2.2 / 16)
      (fun l => full_mass (hp l))
      (fun l x => G l (cond x.2.1 x.1.1 x.1.2.1)
        (cond x.2.2.2.1 x.1.2.2.1 x.1.2.2.2) - meanValue (p l) (G l))
      (fun l x => G l (cond x.2.2.1 x.1.1 x.1.2.1)
        (cond x.2.2.2.2 x.1.2.2.1 x.1.2.2.2) - meanValue (p l) (G l))
      (fun l => full_center (hp l) (G l))

/-- **Full sibs over independent loci (Fisher 1918).** For allele weights summing to `1` at every
locus and symmetric genotypic values, `Cov(FS) = V_A / 2 + V_D / 4`. -/
theorem covFullSibsMulti_eq {L : Type*} [Fintype L] [DecidableEq L] {A : L → Type*}
    [∀ l, Fintype (A l)] {p : ∀ l, A l → ℝ} (hp : ∀ l, ∑ a, p l a = 1)
    {G : ∀ l, A l → A l → ℝ} (hG : ∀ l i j, G l i j = G l j i) :
    covFullSibsMulti p G = multiAddVar p G / 2 + multiDomVar p G / 4 := by
  rw [covFullSibsMulti_eq_sum hp, multiAddVar_eq_sum hp, multiDomVar_eq_sum hp,
    sum_div, sum_div, ← sum_add_distrib]
  exact sum_congr rfl fun l _ => covFullSibs_eq (hp l) (hG l)

end Domains.Biology.StatisticalGenetics.FisherMultilocus
