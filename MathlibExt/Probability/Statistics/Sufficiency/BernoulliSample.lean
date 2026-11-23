/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.MeasureTheory.Measure.Trim
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Basic.ENNReal.Real
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Bool.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Data.Finset.Filter
public import MathlibExt.Probability.Statistics.Sufficiency.Basic
public import MathlibExt.Probability.Statistics.Likelihood

/-!
# Bernoulli n-sample count factorization at density level

For the `n`-trial Bernoulli family with success probability in the closed unit interval
`Set.Icc (0:ℝ) 1`, the count statistic is sufficient at the dominated-density level,
via the factorization criterion `isSufficient_comap_of_factorization_of_sigmaFinite_trim`.
The parameter type is the closed interval (endpoint-corrected contract): the density
formula integrates to one for every `p ∈ [0,1]`, so the endpoint laws `p = 0` and
`p = 1` are included in the family.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.Sufficiency

open MeasureTheory Filter Topology

open scoped BigOperators ENNReal NNReal

private theorem filter_false_eq_filter_not_true (n : ℕ) (ω : Fin n → Bool) :
    Finset.univ.filter (fun i => ω i = false) =
      Finset.univ.filter (fun i => ¬ω i = true) := by
  apply Finset.filter_congr
  intro i _
  constructor
  · intro h1 h2
    have hcon : (false : Bool) = true := h1.symm.trans h2
    exact Bool.false_ne_true hcon
  · intro h1
    exact Bool.eq_false_of_not_eq_true h1

private theorem card_true_add_card_false (n : ℕ) (ω : Fin n → Bool) :
    (Finset.univ.filter (fun i => ω i = true)).card +
      (Finset.univ.filter (fun i => ω i = false)).card = n := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun i : Fin n => ω i = true)
  have hfil : Finset.univ.filter (fun i : Fin n => ¬ω i = true) =
      Finset.univ.filter (fun i => ω i = false) :=
    (filter_false_eq_filter_not_true n ω).symm
  rw [hfil] at h
  rwa [Finset.card_univ, Fintype.card_fin] at h

private theorem card_false_eq_sub (n : ℕ) (ω : Fin n → Bool) :
    (Finset.univ.filter (fun i => ω i = false)).card =
      n - (Finset.univ.filter (fun i => ω i = true)).card := by
  have h := card_true_add_card_false n ω
  omega

private theorem prod_ite_eq_pow_mul_pow (n : ℕ) (ω : Fin n → Bool) (a b : ℝ≥0∞) :
    (∏ i, (if ω i then a else b)) =
      a ^ (Finset.univ.filter fun i => ω i = true).card *
        b ^ (Finset.univ.filter fun i => ω i = false).card := by
  have hsplit := Finset.prod_filter_mul_prod_filter_not Finset.univ
    (fun i : Fin n => ω i = true) (fun i => if ω i then a else b)
  have htrue : (∏ x ∈ Finset.univ with ω x = true, (if ω x then a else b)) =
      a ^ (Finset.univ.filter fun i => ω i = true).card := by
    have hfun : ∀ x ∈ Finset.univ.filter (fun i : Fin n => ω i = true),
        (if ω x then a else b) = a := by
      intro x hx
      have hmem : ω x = true := (Finset.mem_filter.mp hx).2
      simp [hmem]
    have hcongr : (Finset.univ.filter fun i : Fin n => ω i = true).prod
        (fun x => if ω x then a else b) =
        (Finset.univ.filter fun i : Fin n => ω i = true).prod (fun _ => a) :=
      Finset.prod_congr rfl hfun
    rw [hcongr, Finset.prod_const]
  have hfalse_not : (∏ x ∈ Finset.univ with ¬ω x = true, (if ω x then a else b)) =
      b ^ (Finset.univ.filter fun i : Fin n => ¬ω i = true).card := by
    have hfun : ∀ x ∈ Finset.univ.filter (fun i : Fin n => ¬ω i = true),
        (if ω x then a else b) = b := by
      intro x hx
      have hmem : ¬ω x = true := (Finset.mem_filter.mp hx).2
      simp [hmem]
    have hcongr : (Finset.univ.filter fun i : Fin n => ¬ω i = true).prod
        (fun x => if ω x then a else b) =
        (Finset.univ.filter fun i : Fin n => ¬ω i = true).prod (fun _ => b) :=
      Finset.prod_congr rfl hfun
    rw [hcongr, Finset.prod_const]
  have hfil : Finset.univ.filter (fun i : Fin n => ¬ω i = true) =
      Finset.univ.filter (fun i => ω i = false) :=
    (filter_false_eq_filter_not_true n ω).symm
  rw [← hsplit, htrue, hfalse_not, hfil]

private theorem withDensity_count_singleton (n : ℕ)
    (f : (Fin n → Bool) → ℝ≥0∞) (a : Fin n → Bool) :
    (Measure.count.withDensity f) {a} = f a := by
  rw [MeasureTheory.withDensity_apply f (measurableSet_singleton a),
    MeasureTheory.lintegral_singleton f a, Measure.count_singleton a, mul_one]

/-- The `n`-trial Bernoulli family as a normalized density family against counting measure:
`dens p ω = p^(#true) (1-p)^(#false)` as an extended-nonnegative density, indexed by the
closed unit interval (endpoints included). -/
noncomputable def bernoulliFamily (n : ℕ) :
    ProbabilityTheory.NormalizedDensityFamily (Fin n → Bool) (Set.Icc (0 : ℝ) 1)
      Measure.count where
  dens := fun p ω =>
    ENNReal.ofReal ((p.val ^ (Finset.univ.filter fun i => ω i = true).card) *
      ((1 - p.val) ^ (Finset.univ.filter fun i => ω i = false).card))
  measurable := by
    intro p
    exact Measurable.of_discrete.aemeasurable
  normalized := by
    intro p
    have h01 : 0 ≤ p.val ∧ p.val ≤ 1 := Set.mem_Icc.mp p.property
    have hp0 : 0 ≤ p.val := h01.1
    have h1p : 0 ≤ 1 - p.val := by linarith [h01.2]
    rw [MeasureTheory.lintegral_count, tsum_fintype]
    have hprod : ∀ ω : Fin n → Bool,
        (∏ i, (if ω i then ENNReal.ofReal p.val else ENNReal.ofReal (1 - p.val))) =
          ENNReal.ofReal ((p.val ^ (Finset.univ.filter fun i => ω i = true).card) *
            ((1 - p.val) ^ (Finset.univ.filter fun i => ω i = false).card)) := by
      intro ω
      rw [prod_ite_eq_pow_mul_pow n ω _ _,
        ← ENNReal.ofReal_pow hp0 _, ← ENNReal.ofReal_pow h1p _,
        ← ENNReal.ofReal_mul (pow_nonneg hp0 _)]
    have hsum : (∑ ω : Fin n → Bool, ENNReal.ofReal ((p.val ^
        (Finset.univ.filter fun i => ω i = true).card) *
        ((1 - p.val) ^ (Finset.univ.filter fun i => ω i = false).card))) =
        ∑ ω : Fin n → Bool, ∏ i,
          (if ω i then ENNReal.ofReal p.val else ENNReal.ofReal (1 - p.val)) := by
      apply Finset.sum_congr rfl
      intro ω _
      exact (hprod ω).symm
    rw [hsum]
    have hfact := Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset Bool))
      (fun _ b => if b then ENNReal.ofReal p.val else ENNReal.ofReal (1 - p.val))
    rw [Fintype.piFinset_univ] at hfact
    rw [← hfact]
    have hinner : ∀ i : Fin n,
        (∑ j ∈ (Finset.univ : Finset Bool),
          (if j then ENNReal.ofReal p.val else ENNReal.ofReal (1 - p.val))) = 1 := by
      intro i
      rw [Fintype.univ_bool, Finset.sum_insert (by decide), Finset.sum_singleton]
      simp only [↓reduceIte, Bool.false_eq_true]
      rw [← ENNReal.ofReal_add hp0 h1p]
      have hadd : p.val + (1 - p.val) = 1 := by ring
      rw [hadd, ENNReal.ofReal_one]
    have hprod1 : (∏ i : Fin n, ∑ j ∈ (Finset.univ : Finset Bool),
        (if j then ENNReal.ofReal p.val else ENNReal.ofReal (1 - p.val))) =
        ∏ i : Fin n, 1 := by
      apply Finset.prod_congr rfl
      intro i _
      exact hinner i
    rw [hprod1, Finset.prod_const_one]

/-- The count statistic: number of `true` tosses. -/
def bernoulliCount (n : ℕ) (ω : Fin n → Bool) : ℕ :=
  (Finset.univ.filter fun i => ω i = true).card

/-- **Bernoulli count factorization and sufficiency at density level.** For every `n`
(including `n = 0`, where the sample space is a singleton) the count statistic is
sufficient for the Bernoulli family over the closed unit interval (endpoints included),
via the density factorization with `g p k = p^k (1-p)^(n-k)` and `h ≡ 1`. -/
theorem bernoulliFamily_count_sufficient (n : ℕ) :
    IsSufficient (MeasurableSpace.comap (bernoulliCount n) inferInstance)
      (fun p : Set.Icc (0 : ℝ) 1 =>
        (((bernoulliFamily n).law p : Measure (Fin n → Bool)))) := by
  have hT : Measurable (bernoulliCount n) := Measurable.of_discrete
  have hfinP : ∀ p : Set.Icc (0 : ℝ) 1,
      IsFiniteMeasure (((bernoulliFamily n).law p : Measure (Fin n → Bool))) := by
    intro p
    have _hprob := ProbabilityTheory.NormalizedDensityFamily.isProbabilityMeasure_law
      (bernoulliFamily n) p
    infer_instance
  have hfinW : IsFiniteMeasure ((Measure.count : Measure (Fin n → Bool)).withDensity
      (fun _ : Fin n → Bool => (1 : ℝ≥0∞))) := by
    have heq : (fun _ : Fin n → Bool => (1 : ℝ≥0∞)) = 1 := rfl
    rw [heq, MeasureTheory.withDensity_one]
    infer_instance
  have _hfinW' : IsFiniteMeasure ((Measure.count : Measure (Fin n → Bool)).withDensity
      (fun _ : Fin n → Bool => (1 : ℝ≥0∞))) := hfinW
  have _hfinT : IsFiniteMeasure (((Measure.count : Measure (Fin n → Bool)).withDensity
      (fun _ : Fin n → Bool => (1 : ℝ≥0∞))).trim hT.comap_le) :=
    isFiniteMeasure_trim hT.comap_le
  refine isSufficient_comap_of_factorization_of_sigmaFinite_trim hT Measure.count
    (fun p k => ENNReal.ofReal ((p.val ^ k) * ((1 - p.val) ^ (n - k))))
    (fun p => Measurable.of_discrete) (fun _ => (1 : ℝ≥0∞)) measurable_const ?_
  intro p
  have hlaw : ((bernoulliFamily n).law p : Measure (Fin n → Bool)) =
      Measure.count.withDensity ((bernoulliFamily n).dens p) := rfl
  apply Measure.ext_of_singleton
  intro ω
  rw [hlaw, withDensity_count_singleton, withDensity_count_singleton]
  change ENNReal.ofReal ((p.val ^ (Finset.univ.filter fun i => ω i = true).card) *
      ((1 - p.val) ^ (Finset.univ.filter fun i => ω i = false).card)) =
    ENNReal.ofReal ((p.val ^ bernoulliCount n ω) *
      ((1 - p.val) ^ (n - bernoulliCount n ω))) * 1
  rw [mul_one]
  have hcount : bernoulliCount n ω =
      (Finset.univ.filter fun i => ω i = true).card := rfl
  have hcard : (Finset.univ.filter fun i : Fin n => ω i = false).card =
      n - (Finset.univ.filter fun i => ω i = true).card :=
    card_false_eq_sub n ω
  rw [hcount, hcard]

end MathlibExt.Probability.Statistics.Sufficiency
