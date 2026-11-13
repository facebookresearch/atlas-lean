/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MixedModel

import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Crossed random effects and single-cluster design effect

Crossed random-intercept model (participant × item) with induced covariance
entries and planned contrasts, plus a single-cluster model (one cluster of
`m` observations) with shared-effect variance, design-effect identity, and
preservation of the experimental unit.

The crossed part gives the repeated-measures covariance of the marginal law
and contrast variances. The cluster part (single cluster only, not multiple
clusters) gives row variance, mean variance, the design-effect form, the
gap between true and independent-row variance, and the lower bound showing
the shared effect is never averaged away.
-/

open MeasureTheory ProbabilityTheory Matrix MetaMathlibExt
open MathlibExt.Biology.StatisticalGenetics.MixedModel (phenCov)
open MathlibExt.Probability.Statistics.MixedModel

namespace MathlibExt.Probability.Statistics.CrossedRandomEffects

@[expose] public section

/-- Indicator design `Z = [S | W]` of the crossed random-intercept model:
observation `(i, j)` loads on participant `i` and on item `j`. This `Z`
determines the repeated-measures covariance of the marginal law. -/
def crossedDesign (I J : Type*) [DecidableEq I] [DecidableEq J] :
    Matrix (I × J) (I ⊕ J) ℝ :=
  Matrix.of fun k r =>
    Sum.elim (fun i => if k.1 = i then 1 else 0)
      (fun j => if k.2 = j then 1 else 0) r

/-- Diagonal random-effects covariance `G` of the crossed model: `σs2` on
participants, `σw2` on items. With `crossedDesign` and `σe2 • 1` it fixes
the marginal law of the crossed response. -/
def crossedCov (I J : Type*) [DecidableEq I] [DecidableEq J] (σs2 σw2 : ℝ) :
    Matrix (I ⊕ J) (I ⊕ J) ℝ :=
  Matrix.diagonal (Sum.elim (fun _ => σs2) (fun _ => σw2))

/-- The crossed random-effects covariance is positive semidefinite when both
variance components are nonnegative; a hypothesis for the marginal law. -/
theorem posSemidef_crossedCov (I J : Type*) [DecidableEq I] [DecidableEq J]
    (σs2 σw2 : ℝ) (hs : 0 ≤ σs2) (hw : 0 ≤ σw2) :
    (crossedCov I J σs2 σw2).PosSemidef := by
  unfold crossedCov
  apply Matrix.PosSemidef.diagonal
  intro r
  cases r with
  | inl i =>
      simpa using hs
  | inr j =>
      simpa using hw

/-- Specified repeated-measures covariance of the crossed model, algebraically:
`phenCov` entries count shared participants, shared items and diagonal noise.
This is the covariance matrix of the marginal law. -/
theorem phenCov_crossed_apply {I J : Type*} [DecidableEq I] [DecidableEq J]
    [Fintype I] [Fintype J] (σs2 σw2 σe2 : ℝ) (k l : I × J) :
    phenCov (crossedDesign I J) (crossedCov I J σs2 σw2) (σe2 • 1) k l =
      (if k.1 = l.1 then σs2 else 0) + (if k.2 = l.2 then σw2 else 0) +
        (if k = l then σe2 else 0) := by
  simp only [phenCov, crossedDesign, crossedCov, Matrix.add_apply,
    Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal_apply,
    Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply]
  rw [Fintype.sum_sum_type]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ]

/-- Induced covariance entries in the Gaussian crossed model: the marginal law
of the mixed-model response has the specified repeated-measures covariance. -/
theorem covariance_crossed_response {I J : Type*} [DecidableEq I]
    [DecidableEq J] [Fintype I] [Fintype J] {p : Type*} [Fintype p]
    [DecidableEq p] {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] (γ : Ω → EuclideanSpace ℝ (I ⊕ J))
    (ε : Ω → EuclideanSpace ℝ (I × J)) (hγ : Measurable γ)
    (hε : Measurable ε) (hind : IndepFun γ ε P)
    (X : Matrix (I × J) p ℝ) (β : EuclideanSpace ℝ p) (σs2 σw2 σe2 : ℝ)
    (hs : 0 ≤ σs2) (hw : 0 ≤ σw2) (he : 0 < σe2)
    (hγl : P.map γ = multivariateGaussian 0 (crossedCov I J σs2 σw2))
    (hεl : P.map ε = multivariateGaussian 0 (σe2 • 1)) (k l : I × J) :
    cov[fun ω => (toEuclideanLin X β +
        toEuclideanLin (crossedDesign I J) (γ ω) + ε ω).ofLp k,
      fun ω => (toEuclideanLin X β +
        toEuclideanLin (crossedDesign I J) (γ ω) + ε ω).ofLp l;
      P] =
      (if k.1 = l.1 then σs2 else 0) + (if k.2 = l.2 then σw2 else 0) +
        (if k = l then σe2 else 0) := by
  have hG : (crossedCov I J σs2 σw2).PosSemidef :=
    posSemidef_crossedCov I J σs2 σw2 hs hw
  have hR : (σe2 • (1 : Matrix (I × J) (I × J) ℝ)).PosDef :=
    Matrix.PosDef.one.smul he
  have hcov := covariance_mixedModel_response γ ε hγ hε hind X β
    (crossedDesign I J) (crossedCov I J σs2 σw2) (σe2 • 1) hG hR hγl hεl k l
  rw [phenCov_crossed_apply] at hcov
  exact hcov

/-- Planned-contrast variance in any mixed model: for fixed coefficients
`c`, the variance under the marginal law is the `phenCov` quadratic form. -/
theorem variance_contrast_mixedModel_response {n p q : Type*} [Fintype n]
    [DecidableEq n] [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (γ : Ω → EuclideanSpace ℝ q) (ε : Ω → EuclideanSpace ℝ n)
    (hγ : Measurable γ) (hε : Measurable ε) (hind : IndepFun γ ε P)
    (X : Matrix n p ℝ) (β : EuclideanSpace ℝ p) (Z : Matrix n q ℝ)
    (G : Matrix q q ℝ) (R : Matrix n n ℝ) (hG : G.PosSemidef)
    (hR : R.PosSemidef) (hγl : P.map γ = multivariateGaussian 0 G)
    (hεl : P.map ε = multivariateGaussian 0 R) (c : n → ℝ) :
    Var[fun ω => ∑ k, c k * (toEuclideanLin X β + toEuclideanLin Z (γ ω) +
      ε ω).ofLp k; P] =
      c ⬝ᵥ (phenCov Z G R *ᵥ c) := by
  have hmap := map_mixedModel_response γ ε hγ hε hind X β Z G R hG hR
    hγl hεl
  have hpsd : (phenCov Z G R).PosSemidef :=
    posSemidef_phenCov_of_posSemidef Z G R hG hR
  have hYmeas : AEStronglyMeasurable
      (fun ω => toEuclideanLin X β + toEuclideanLin Z (γ ω) + ε ω) P := by
    fun_prop
  have hXmeas : AEMeasurable
      (fun y : EuclideanSpace ℝ n => ∑ k, c k * y.ofLp k)
      (P.map (fun ω => toEuclideanLin X β + toEuclideanLin Z (γ ω) +
        ε ω)) := by
    apply Measurable.aemeasurable
    apply Finset.measurable_sum
    intro k _
    have hck : Measurable (fun y : EuclideanSpace ℝ n => y.ofLp k) := by
      rw [← EuclideanSpace.coe_proj]
      exact (EuclideanSpace.proj k).continuous.measurable
    exact hck.const_mul (c k)
  have hvar : Var[fun ω => ∑ k, c k * (toEuclideanLin X β +
      toEuclideanLin Z (γ ω) + ε ω).ofLp k; P] =
      Var[fun y : EuclideanSpace ℝ n => ∑ k, c k * y.ofLp k;
        P.map (fun ω => toEuclideanLin X β + toEuclideanLin Z (γ ω) +
          ε ω)] :=
    (variance_map hXmeas hYmeas.aemeasurable).symm
  have hmemid : MemLp (id : EuclideanSpace ℝ n → EuclideanSpace ℝ n) 2
      (multivariateGaussian (toEuclideanLin X β) (phenCov Z G R)) :=
    IsGaussian.memLp_two_id
  have hbase : ∀ k : n, MemLp (fun y : EuclideanSpace ℝ n => y.ofLp k) 2
      (multivariateGaussian (toEuclideanLin X β) (phenCov Z G R)) := by
    intro k
    have h := hmemid.continuousLinearMap_comp
      (EuclideanSpace.proj k : EuclideanSpace ℝ n →L[ℝ] ℝ)
    simpa [EuclideanSpace.coe_proj] using h
  have hmem : ∀ k : n, MemLp
      (fun y : EuclideanSpace ℝ n => c k * y.ofLp k) 2
      (multivariateGaussian (toEuclideanLin X β) (phenCov Z G R)) :=
    fun k => (hbase k).const_mul _
  rw [hvar, hmap, variance_fun_sum hmem]
  simp_rw [covariance_const_mul_left, covariance_const_mul_right,
    covariance_eval_multivariateGaussian hpsd]
  simp only [dotProduct, Matrix.mulVec]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Planned-contrast variance in the crossed model: expanding the quadratic
form of the marginal law gives the double sum over the specified entries. -/
theorem variance_contrast_crossed_response {I J : Type*} [DecidableEq I]
    [DecidableEq J] [Fintype I] [Fintype J] {p : Type*} [Fintype p]
    [DecidableEq p] {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] (γ : Ω → EuclideanSpace ℝ (I ⊕ J))
    (ε : Ω → EuclideanSpace ℝ (I × J)) (hγ : Measurable γ)
    (hε : Measurable ε) (hind : IndepFun γ ε P)
    (X : Matrix (I × J) p ℝ) (β : EuclideanSpace ℝ p) (σs2 σw2 σe2 : ℝ)
    (hs : 0 ≤ σs2) (hw : 0 ≤ σw2) (he : 0 < σe2)
    (hγl : P.map γ = multivariateGaussian 0 (crossedCov I J σs2 σw2))
    (hεl : P.map ε = multivariateGaussian 0 (σe2 • 1)) (c : I × J → ℝ) :
    Var[fun ω => ∑ k, c k * (toEuclideanLin X β +
      toEuclideanLin (crossedDesign I J) (γ ω) + ε ω).ofLp k; P] =
      ∑ k, ∑ l, c k * c l * ((if k.1 = l.1 then σs2 else 0) +
        (if k.2 = l.2 then σw2 else 0) + (if k = l then σe2 else 0)) := by
  have hG : (crossedCov I J σs2 σw2).PosSemidef :=
    posSemidef_crossedCov I J σs2 σw2 hs hw
  have hR : (σe2 • (1 : Matrix (I × J) (I × J) ℝ)).PosSemidef :=
    Matrix.PosSemidef.one.smul he.le
  have hvar := variance_contrast_mixedModel_response γ ε hγ hε hind X β
    (crossedDesign I J) (crossedCov I J σs2 σw2) (σe2 • 1) hG hR hγl hεl c
  rw [hvar]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [phenCov_crossed_apply]
  ring

/-- All-ones cluster design for one cluster of `m` observations: every row
loads on the single shared effect. With `σc2 • 1` and `σw2 • 1` it fixes
the marginal law of the cluster response. -/
def clusterDesign (m : ℕ) : Matrix (Fin m) (Fin 1) ℝ :=
  Matrix.of fun _ _ => 1

/-- Specified cluster covariance entries: `phenCov` of the marginal law is
`σc2` everywhere plus `σw2` on the diagonal. -/
theorem phenCov_cluster_apply (m : ℕ) (σc2 σw2 : ℝ) (k l : Fin m) :
    phenCov (clusterDesign m) (σc2 • 1) (σw2 • 1) k l =
      σc2 + (if k = l then σw2 else 0) := by
  simp [phenCov, clusterDesign, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply]

/-- Row variance in the cluster model: under the marginal law each row has
variance `σc2 + σw2`. -/
theorem variance_cluster_row (m : ℕ) {p : Type*} [Fintype p] [DecidableEq p]
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (γ : Ω → EuclideanSpace ℝ (Fin 1)) (ε : Ω → EuclideanSpace ℝ (Fin m))
    (hγ : Measurable γ) (hε : Measurable ε) (hind : IndepFun γ ε P)
    (X : Matrix (Fin m) p ℝ) (β : EuclideanSpace ℝ p) (σc2 σw2 : ℝ)
    (hc : 0 ≤ σc2) (hw : 0 < σw2)
    (hγl : P.map γ = multivariateGaussian 0 (σc2 • 1))
    (hεl : P.map ε = multivariateGaussian 0 (σw2 • 1)) (k : Fin m) :
    Var[fun ω => (toEuclideanLin X β + toEuclideanLin (clusterDesign m) (γ ω) +
      ε ω).ofLp k; P] = σc2 + σw2 := by
  have hG : (σc2 • (1 : Matrix (Fin 1) (Fin 1) ℝ)).PosSemidef :=
    Matrix.PosSemidef.one.smul hc
  have hR : (σw2 • (1 : Matrix (Fin m) (Fin m) ℝ)).PosDef :=
    Matrix.PosDef.one.smul hw
  have hcov := covariance_mixedModel_response γ ε hγ hε hind X β
    (clusterDesign m) (σc2 • 1) (σw2 • 1) hG hR hγl hεl k k
  have hYresp : Measurable (fun ω => toEuclideanLin X β +
      toEuclideanLin (clusterDesign m) (γ ω) + ε ω) := by
    fun_prop
  have hcoord : Measurable (fun y : EuclideanSpace ℝ (Fin m) => y.ofLp k) := by
    rw [← EuclideanSpace.coe_proj]
    exact (EuclideanSpace.proj k).continuous.measurable
  have hvar : Var[fun ω => (toEuclideanLin X β +
      toEuclideanLin (clusterDesign m) (γ ω) + ε ω).ofLp k; P] =
      cov[fun ω => (toEuclideanLin X β +
        toEuclideanLin (clusterDesign m) (γ ω) + ε ω).ofLp k,
        fun ω => (toEuclideanLin X β +
          toEuclideanLin (clusterDesign m) (γ ω) + ε ω).ofLp k; P] :=
    (covariance_self (hcoord.comp hYresp).aemeasurable).symm
  rw [hvar, hcov, phenCov_cluster_apply]
  simp

/-- Mean variance in the cluster model: under the marginal law the mean has
variance `σc2 + σw2 / m`, Kerry and Bland's formula. -/
theorem variance_cluster_mean (m : ℕ) {p : Type*} [Fintype p] [DecidableEq p]
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (γ : Ω → EuclideanSpace ℝ (Fin 1)) (ε : Ω → EuclideanSpace ℝ (Fin m))
    (hγ : Measurable γ) (hε : Measurable ε) (hind : IndepFun γ ε P)
    (X : Matrix (Fin m) p ℝ) (β : EuclideanSpace ℝ p) (σc2 σw2 : ℝ)
    (hc : 0 ≤ σc2) (hw : 0 < σw2)
    (hγl : P.map γ = multivariateGaussian 0 (σc2 • 1))
    (hεl : P.map ε = multivariateGaussian 0 (σw2 • 1)) (hm : 0 < m) :
    Var[fun ω => (∑ k, (toEuclideanLin X β +
      toEuclideanLin (clusterDesign m) (γ ω) + ε ω).ofLp k) / (m : ℝ);
      P] = σc2 + σw2 / (m : ℝ) := by
  have hG : (σc2 • (1 : Matrix (Fin 1) (Fin 1) ℝ)).PosSemidef :=
    Matrix.PosSemidef.one.smul hc
  have hR : (σw2 • (1 : Matrix (Fin m) (Fin m) ℝ)).PosDef :=
    Matrix.PosDef.one.smul hw
  have hm' : (m : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt hm
  have hmpos : (0 : ℝ) < m := by
    exact_mod_cast hm
  have hC := variance_contrast_mixedModel_response γ ε hγ hε hind X β
    (clusterDesign m) (σc2 • 1) (σw2 • 1) hG hR.posSemidef hγl hεl
    (fun _ => (1 : ℝ))
  have hsum : Var[fun ω => ∑ k, (toEuclideanLin X β +
      toEuclideanLin (clusterDesign m) (γ ω) + ε ω).ofLp k; P] =
      (m : ℝ) ^ 2 * σc2 + (m : ℝ) * σw2 := by
    have hC' : Var[fun ω => ∑ k, (toEuclideanLin X β +
        toEuclideanLin (clusterDesign m) (γ ω) + ε ω).ofLp k; P] =
        (fun _ => (1 : ℝ)) ⬝ᵥ (phenCov (clusterDesign m) (σc2 • 1)
          (σw2 • 1) *ᵥ (fun _ => 1)) := by
      simpa using hC
    rw [hC']
    simp only [dotProduct, Matrix.mulVec, phenCov_cluster_apply,
      one_mul, mul_one]
    simp [Finset.sum_add_distrib, Finset.sum_const, Fintype.card_fin,
      Finset.sum_ite_eq, Finset.mem_univ]
    ring
  have hdiv : Var[fun ω => (∑ k, (toEuclideanLin X β +
      toEuclideanLin (clusterDesign m) (γ ω) + ε ω).ofLp k) / (m : ℝ); P] =
      Var[fun ω => ∑ k, (toEuclideanLin X β +
        toEuclideanLin (clusterDesign m) (γ ω) + ε ω).ofLp k; P] /
        (m : ℝ) ^ 2 := by
    have heq : (fun ω => (∑ k, (toEuclideanLin X β +
        toEuclideanLin (clusterDesign m) (γ ω) + ε ω).ofLp k) / (m : ℝ)) =
        (fun ω => (m : ℝ)⁻¹ * (∑ k, (toEuclideanLin X β +
          toEuclideanLin (clusterDesign m) (γ ω) + ε ω).ofLp k)) := by
      funext ω
      rw [div_eq_inv_mul, mul_comm]
    rw [heq, variance_const_mul]
    field_simp
  rw [hdiv, hsum]
  field_simp

/-- Design-effect form: under the marginal law the mean variance equals the
design effect times the independent-row variance. -/
theorem variance_cluster_mean_eq_designEffect (m : ℕ) {p : Type*}
    [Fintype p] [DecidableEq p] {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (γ : Ω → EuclideanSpace ℝ (Fin 1)) (ε : Ω → EuclideanSpace ℝ (Fin m))
    (hγ : Measurable γ) (hε : Measurable ε) (hind : IndepFun γ ε P)
    (X : Matrix (Fin m) p ℝ) (β : EuclideanSpace ℝ p) (σc2 σw2 : ℝ)
    (hc : 0 ≤ σc2) (hw : 0 < σw2)
    (hγl : P.map γ = multivariateGaussian 0 (σc2 • 1))
    (hεl : P.map ε = multivariateGaussian 0 (σw2 • 1)) (hm : 0 < m)
    (k : Fin m) :
    Var[fun ω => (∑ j, (toEuclideanLin X β +
      toEuclideanLin (clusterDesign m) (γ ω) + ε ω).ofLp j) / (m : ℝ);
      P] = (1 + ((m : ℝ) - 1) * (σc2 / (σc2 + σw2))) *
      (Var[fun ω => (toEuclideanLin X β +
        toEuclideanLin (clusterDesign m) (γ ω) + ε ω).ofLp k; P] /
        (m : ℝ)) := by
  have hmean := variance_cluster_mean m X β σc2 σw2 hc hw hγl hεl hm
    (γ := γ) (ε := ε) (hγ := hγ) (hε := hε) (hind := hind)
  have hrow := variance_cluster_row m X β σc2 σw2 hc hw hγl hεl k
    (γ := γ) (ε := ε) (hγ := hγ) (hε := hε) (hind := hind)
  rw [hmean, hrow]
  have hm' : (m : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt hm
  have hpos : (0 : ℝ) < σc2 + σw2 := by
    linarith
  have hsum : σc2 + σw2 ≠ 0 := ne_of_gt hpos
  field_simp
  ring

/-- True versus independent-row variance: under the marginal law with at
least two observations and a positive shared effect, they differ. -/
theorem variance_cluster_row_div_lt_mean (m : ℕ) {p : Type*}
    [Fintype p] [DecidableEq p] {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (γ : Ω → EuclideanSpace ℝ (Fin 1)) (ε : Ω → EuclideanSpace ℝ (Fin m))
    (hγ : Measurable γ) (hε : Measurable ε) (hind : IndepFun γ ε P)
    (X : Matrix (Fin m) p ℝ) (β : EuclideanSpace ℝ p) (σc2 σw2 : ℝ)
    (hw : 0 < σw2)
    (hγl : P.map γ = multivariateGaussian 0 (σc2 • 1))
    (hεl : P.map ε = multivariateGaussian 0 (σw2 • 1)) (hm : 2 ≤ m)
    (hcpos : 0 < σc2) (k : Fin m) :
    Var[fun ω => (toEuclideanLin X β +
      toEuclideanLin (clusterDesign m) (γ ω) + ε ω).ofLp k; P] / (m : ℝ) <
      Var[fun ω => (∑ j, (toEuclideanLin X β +
        toEuclideanLin (clusterDesign m) (γ ω) + ε ω).ofLp j) / (m : ℝ);
        P] := by
  have hc : 0 ≤ σc2 := le_of_lt hcpos
  have hm0 : 0 < m := by linarith
  have hmean := variance_cluster_mean m X β σc2 σw2 hc hw hγl hεl hm0
    (γ := γ) (ε := ε) (hγ := hγ) (hε := hε) (hind := hind)
  have hrow := variance_cluster_row m X β σc2 σw2 hc hw hγl hεl k
    (γ := γ) (ε := ε) (hγ := hγ) (hε := hε) (hind := hind)
  rw [hrow, hmean]
  have hm' : (1 : ℝ) < m := by
    exact_mod_cast (by linarith : 1 < m)
  have hmpos : (0 : ℝ) < m := by
    exact_mod_cast hm0
  field_simp
  nlinarith [hcpos, hw, hm', hmpos]

/-- The shared effect is never averaged away: under the marginal law the
mean variance is at least `σc2`; the experimental unit is the cluster. -/
theorem le_variance_cluster_mean (m : ℕ) {p : Type*} [Fintype p]
    [DecidableEq p] {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] (γ : Ω → EuclideanSpace ℝ (Fin 1))
    (ε : Ω → EuclideanSpace ℝ (Fin m)) (hγ : Measurable γ)
    (hε : Measurable ε) (hind : IndepFun γ ε P)
    (X : Matrix (Fin m) p ℝ) (β : EuclideanSpace ℝ p) (σc2 σw2 : ℝ)
    (hc : 0 ≤ σc2) (hw : 0 < σw2)
    (hγl : P.map γ = multivariateGaussian 0 (σc2 • 1))
    (hεl : P.map ε = multivariateGaussian 0 (σw2 • 1)) (hm : 0 < m) :
    σc2 ≤ Var[fun ω => (∑ k, (toEuclideanLin X β +
      toEuclideanLin (clusterDesign m) (γ ω) + ε ω).ofLp k) / (m : ℝ);
      P] := by
  have hmean := variance_cluster_mean m X β σc2 σw2 hc hw hγl hεl hm
    (γ := γ) (ε := ε) (hγ := hγ) (hε := hε) (hind := hind)
  rw [hmean]
  have hmpos : (0 : ℝ) < m := by
    exact_mod_cast hm
  have hnonneg : (0 : ℝ) ≤ σw2 / (m : ℝ) := by
    positivity
  linarith

end

end MathlibExt.Probability.Statistics.CrossedRandomEffects
