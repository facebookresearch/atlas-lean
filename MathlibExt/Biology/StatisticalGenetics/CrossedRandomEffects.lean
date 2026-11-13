/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.MixedModel
public import MathlibExt.Biology.Omics.Pseudobulk

import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Crossed random effects and the single-cluster design effect

Two specializations of the linear mixed model `Y = X β + Z γ + ε` of
`MathlibExt.Biology.StatisticalGenetics.MixedModel`, whose Gaussian response laws give the
covariances below.

**Crossed random intercepts.** Observation `(i, j)` loads on a row effect `i` and a column effect
`j`: participant × item in repeated-measures experiments (Clark 1973; Baayen, Davidson and Bates
2008), or sire × dam in a factorial mating design with one record per cross (Comstock and
Robinson 1948), where any sire × dam interaction is absorbed into the residual. Two observations
covary by `σs2` if they share the row, plus `σw2` if they share the column, plus `σe2` on the
diagonal (`phenCov_crossed_apply`, `covariance_crossed_response`), and a planned contrast has the
matching quadratic-form variance (`variance_contrast_crossed_response`).

**One cluster.** With the all-ones design (one cluster of `m` observations) the Gaussian response
is a random-intercept model with one donor and `m` cells in the sense of
`MathlibExt.Biology.Omics.Pseudobulk` (`isRandomIntercept_cluster_response`). The row variance,
the mean variance `σc2 + σw2 / m`, the design-effect form and the gap between true and
independent-row variance are derived from that file's `variance_cell`, `variance_cellMean`,
`trueVar_eq_designEffect_mul_naiveVar` and `naiveVar_lt_trueVar`; `le_variance_cluster_mean` adds
that the shared effect is never averaged away. Several balanced clusters are the general case of
the Pseudobulk results.

## References

* H. H. Clark, *The language-as-fixed-effect fallacy: a critique of language statistics in
  psychological research*, J. Verbal Learn. Verbal Behav. 12 (1973), 335–359.
* R. H. Baayen, D. J. Davidson, D. M. Bates, *Mixed-effects modeling with crossed random effects
  for subjects and items*, J. Mem. Lang. 59 (2008), 390–412.
* R. E. Comstock, H. F. Robinson, *The components of genetic variance in populations of
  biparental progenies and their use in estimating the average degree of dominance*,
  Biometrics 4 (1948), 254–266.
-/

open MeasureTheory ProbabilityTheory Matrix MetaMathlibExt
open MathlibExt.Biology.StatisticalGenetics.MixedModel
open MathlibExt.Biology.Omics.Pseudobulk (IsRandomIntercept riCov cellMean trueVar naiveVar icc
  variance_cell variance_cellMean trueVar_eq_designEffect_mul_naiveVar naiveVar_lt_trueVar)

namespace MathlibExt.Biology.StatisticalGenetics.CrossedRandomEffects

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

/-- **The Gaussian cluster response is a random-intercept model.** Indexing the `m` rows by
`Fin 1 × Fin m` (one donor, `m` cells), the rows of `Y = X β + 𝟙 γ + ε` satisfy `IsRandomIntercept`
of `MathlibExt.Biology.Omics.Pseudobulk` with donor variance `σc2` and residual variance `σw2`, so
that file's second-moment results apply to this response. -/
theorem isRandomIntercept_cluster_response (m : ℕ) {p : Type*} [Fintype p] [DecidableEq p]
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (γ : Ω → EuclideanSpace ℝ (Fin 1)) (ε : Ω → EuclideanSpace ℝ (Fin m))
    (hγ : Measurable γ) (hε : Measurable ε) (hind : IndepFun γ ε P)
    (X : Matrix (Fin m) p ℝ) (β : EuclideanSpace ℝ p) (σc2 σw2 : ℝ)
    (hc : 0 ≤ σc2) (hw : 0 < σw2)
    (hγl : P.map γ = multivariateGaussian 0 (σc2 • 1))
    (hεl : P.map ε = multivariateGaussian 0 (σw2 • 1)) :
    IsRandomIntercept P (fun (i : Fin 1 × Fin m) ω => (toEuclideanLin X β +
      toEuclideanLin (clusterDesign m) (γ ω) + ε ω).ofLp i.2) σc2 σw2 := by
  have hG : (σc2 • (1 : Matrix (Fin 1) (Fin 1) ℝ)).PosSemidef :=
    Matrix.PosSemidef.one.smul hc
  have hR : (σw2 • (1 : Matrix (Fin m) (Fin m) ℝ)).PosDef :=
    Matrix.PosDef.one.smul hw
  refine ⟨hc, hw.le, fun i => ?_, fun i j => ?_⟩
  · have hmap := map_mixedModel_response γ ε hγ hε hind X β (clusterDesign m)
      (σc2 • 1) (σw2 • 1) hG hR.posSemidef hγl hεl
    have hY : AEMeasurable (fun ω => toEuclideanLin X β +
        toEuclideanLin (clusterDesign m) (γ ω) + ε ω) P := by
      fun_prop
    have hid : MemLp (id : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)) 2
        (multivariateGaussian (toEuclideanLin X β)
          (phenCov (clusterDesign m) (σc2 • 1) (σw2 • 1))) :=
      IsGaussian.memLp_two_id
    have hcoord : MemLp (fun y : EuclideanSpace ℝ (Fin m) => y.ofLp i.2) 2
        (multivariateGaussian (toEuclideanLin X β)
          (phenCov (clusterDesign m) (σc2 • 1) (σw2 • 1))) := by
      have h := hid.continuousLinearMap_comp
        (EuclideanSpace.proj i.2 : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ)
      simpa [EuclideanSpace.coe_proj] using h
    rw [← hmap] at hcoord
    exact hcoord.comp_of_map hY
  · refine (covariance_mixedModel_response γ ε hγ hε hind X β (clusterDesign m)
      (σc2 • 1) (σw2 • 1) hG hR hγl hεl i.2 j.2).trans ?_
    rw [phenCov_cluster_apply]
    simp [riCov, Prod.ext_iff, Subsingleton.elim i.1 j.1]

/-- With one donor, the cell-level mean of `Pseudobulk` is the plain mean of the `m` rows. -/
private theorem cellMean_cluster {Ω : Type*} {m : ℕ} (Z : Ω → EuclideanSpace ℝ (Fin m)) :
    cellMean (fun (i : Fin 1 × Fin m) ω => (Z ω).ofLp i.2) =
      fun ω => (∑ k, (Z ω).ofLp k) / (m : ℝ) := by
  funext ω
  simp [cellMean, Fintype.sum_prod_type]

/-- The cluster mean has variance `trueVar σc2 σw2 1 m`: `variance_cellMean` with one donor. -/
private theorem variance_cluster_mean_eq_trueVar (m : ℕ) {p : Type*} [Fintype p]
    [DecidableEq p] {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] (γ : Ω → EuclideanSpace ℝ (Fin 1))
    (ε : Ω → EuclideanSpace ℝ (Fin m)) (hγ : Measurable γ) (hε : Measurable ε)
    (hind : IndepFun γ ε P) (X : Matrix (Fin m) p ℝ) (β : EuclideanSpace ℝ p)
    (σc2 σw2 : ℝ) (hc : 0 ≤ σc2) (hw : 0 < σw2)
    (hγl : P.map γ = multivariateGaussian 0 (σc2 • 1))
    (hεl : P.map ε = multivariateGaussian 0 (σw2 • 1)) (hm : 0 < m) :
    Var[fun ω => (∑ k, (toEuclideanLin X β +
      toEuclideanLin (clusterDesign m) (γ ω) + ε ω).ofLp k) / (m : ℝ);
      P] = trueVar σc2 σw2 1 m := by
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have h := variance_cellMean
    (isRandomIntercept_cluster_response m γ ε hγ hε hind X β σc2 σw2 hc hw hγl hεl)
  rw [cellMean_cluster] at h
  simpa only [Fintype.card_fin] using h

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
  exact variance_cell
    (isRandomIntercept_cluster_response m γ ε hγ hε hind X β σc2 σw2 hc hw hγl hεl) (0, k)

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
  rw [variance_cluster_mean_eq_trueVar m γ ε hγ hε hind X β σc2 σw2 hc hw hγl hεl hm,
    trueVar]
  simp

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
  rw [variance_cluster_mean_eq_trueVar m γ ε hγ hε hind X β σc2 σw2 hc hw hγl hεl hm,
    variance_cluster_row m γ ε hγ hε hind X β σc2 σw2 hc hw hγl hεl k,
    trueVar_eq_designEffect_mul_naiveVar (add_pos_of_nonneg_of_pos hc hw).ne'
      one_ne_zero hm.ne']
  simp [naiveVar, icc]

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
  rw [variance_cluster_row m γ ε hγ hε hind X β σc2 σw2 hcpos.le hw hγl hεl k,
    variance_cluster_mean_eq_trueVar m γ ε hγ hε hind X β σc2 σw2 hcpos.le hw hγl hεl
      (by omega)]
  simpa [naiveVar] using naiveVar_lt_trueVar σw2 hcpos (one_ne_zero : (1 : ℕ) ≠ 0) hm

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

end MathlibExt.Biology.StatisticalGenetics.CrossedRandomEffects
