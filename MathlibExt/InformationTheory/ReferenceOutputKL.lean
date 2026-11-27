/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.ConditionalEntropy
public import MathlibExt.InformationTheory.MutualInformationDPI
public import Mathlib.InformationTheory.KullbackLeibler.ChainRule
public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
public import Mathlib.Probability.Kernel.Disintegration.StandardBorel
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Reference-output KL identity

For a joint probability law and a reference output law, the KL
divergence to the product of the input marginal with the reference
splits into a mutual-information term (in bits, hence the
`log 2` factor) plus the KL divergence from the true output
marginal to the reference. Independent and diagonal Gaussian
laws validate the two ends of the identity.

-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace MathlibExt.InformationTheory.ReferenceOutputKL

open _root_.InformationTheory

/-! ### Proof-facing identities -/

/-- KL divergence is invariant under the coordinate swap `X × Y ≃ Y × X`. -/
theorem klDiv_map_swap {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ ν : Measure (X × Y)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv (μ.map Prod.swap) (ν.map Prod.swap) = klDiv μ ν := by
  apply le_antisymm
  · exact klDiv_map_le _ _ measurable_swap
  · have h1 : (μ.map Prod.swap).map Prod.swap = μ := by
      rw [Measure.map_map measurable_swap measurable_swap]
      simp
    have h2 : (ν.map Prod.swap).map Prod.swap = ν := by
      rw [Measure.map_map measurable_swap measurable_swap]
      simp
    have h := klDiv_map_le (μ.map Prod.swap) (ν.map Prod.swap) measurable_swap
    rwa [h1, h2] at h

/-- Disintegration of the swapped joint law over the output coordinate: the law of `(Y, X)` is the
output marginal composed with the conditional kernel of `X` given `Y`. -/
theorem map_swap_eq_map_snd_compProd_condKernel {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] [StandardBorelSpace X] [Nonempty X] (μ : Measure (X × Y))
    [IsFiniteMeasure μ] :
    μ.map Prod.swap = (μ.map Prod.snd) ⊗ₘ (μ.map Prod.swap).condKernel := by
  have h := Measure.disintegrate (μ.map Prod.swap) ((μ.map Prod.swap).condKernel)
  simpa [Measure.fst_map_swap, Measure.snd] using h.symm

/-- The chain-rule identity behind the variational formula, with the true product of the
marginals as middle term:
`KL(μ ‖ μX ⊗ Q) = KL(μ ‖ μX ⊗ μY) + KL(μY ‖ Q)` in `ℝ≥0∞`. -/
theorem klDiv_prod_reference_eq_add {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [StandardBorelSpace X] [Nonempty X]
    (μ : ProbabilityMeasure (X × Y)) (Q : Measure Y) [IsProbabilityMeasure Q] :
    klDiv (μ : Measure (X × Y)) (((μ : Measure (X × Y)).map Prod.fst).prod Q) =
      klDiv (μ : Measure (X × Y))
          (((μ : Measure (X × Y)).map Prod.fst).prod ((μ : Measure (X × Y)).map Prod.snd)) +
        klDiv ((μ : Measure (X × Y)).map Prod.snd) Q := by
  set μX : Measure X := (μ : Measure (X × Y)).map Prod.fst with hμX
  set μY : Measure Y := (μ : Measure (X × Y)).map Prod.snd with hμY
  set μs : Measure (Y × X) := (μ : Measure (X × Y)).map Prod.swap with hμs
  set κ : Kernel Y X := μs.condKernel with hκ
  have hdis : μs = μY ⊗ₘ κ :=
    map_swap_eq_map_snd_compProd_condKernel (μ : Measure (X × Y))
  have hswap1 : (((μ : Measure (X × Y)).map Prod.fst).prod Q).map Prod.swap
      = Q.prod μX := Measure.prod_swap
  have hswap2 : (((μ : Measure (X × Y)).map Prod.fst).prod
      ((μ : Measure (X × Y)).map Prod.snd)).map Prod.swap
      = μY.prod μX := by
    have := Measure.prod_swap (μ := (μ : Measure (X × Y)).map Prod.fst)
      (ν := (μ : Measure (X × Y)).map Prod.snd)
    simpa [hμX, hμY] using this
  have hcompQ : Q.prod μX = Q ⊗ₘ (Kernel.const Y μX) := (Measure.compProd_const).symm
  have hcompY : μY.prod μX = μY ⊗ₘ (Kernel.const Y μX) := (Measure.compProd_const).symm
  have hKL1 : klDiv (μ : Measure (X × Y)) (((μ : Measure (X × Y)).map Prod.fst).prod Q)
      = klDiv μs (Q.prod μX) := by
    have h := klDiv_map_swap (μ : Measure (X × Y))
      (((μ : Measure (X × Y)).map Prod.fst).prod Q)
    calc klDiv (μ : Measure (X × Y)) (((μ : Measure (X × Y)).map Prod.fst).prod Q)
        = klDiv ((μ : Measure (X × Y)).map Prod.swap)
            ((((μ : Measure (X × Y)).map Prod.fst).prod Q).map Prod.swap) := h.symm
      _ = klDiv μs (Q.prod μX) := by rw [hμs, hswap1]
  have hKL2 : klDiv (μ : Measure (X × Y))
        (((μ : Measure (X × Y)).map Prod.fst).prod ((μ : Measure (X × Y)).map Prod.snd))
      = klDiv μs (μY.prod μX) := by
    have h := klDiv_map_swap (μ : Measure (X × Y))
      (((μ : Measure (X × Y)).map Prod.fst).prod ((μ : Measure (X × Y)).map Prod.snd))
    calc klDiv (μ : Measure (X × Y))
          (((μ : Measure (X × Y)).map Prod.fst).prod ((μ : Measure (X × Y)).map Prod.snd))
        = klDiv ((μ : Measure (X × Y)).map Prod.swap)
            ((((μ : Measure (X × Y)).map Prod.fst).prod
              ((μ : Measure (X × Y)).map Prod.snd)).map Prod.swap) := h.symm
      _ = klDiv μs (μY.prod μX) := by rw [hμs, hswap2]
  rw [hKL1, hKL2, hdis, hcompQ, hcompY]
  rw [klDiv_compProd_eq_add]
  rw [add_comm]

/-- Bits to nats: `ofReal (log 2) * I(μ) = KL(μ ‖ μX ⊗ μY)`, including the value `⊤`. -/
theorem ofReal_log_two_mul_measureMutualInformation {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] (μ : ProbabilityMeasure (X × Y)) :
    ENNReal.ofReal (Real.log 2) * measureMutualInformation μ =
      klDiv (μ : Measure (X × Y))
        (((μ : Measure (X × Y)).map Prod.fst).prod ((μ : Measure (X × Y)).map Prod.snd)) := by
  unfold measureMutualInformation
  have hpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc0 : ENNReal.ofReal (Real.log 2) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hpos).ne'
  have hctop : ENNReal.ofReal (Real.log 2) ≠ ∞ := ENNReal.ofReal_ne_top
  exact ENNReal.mul_div_cancel hc0 hctop

/-! ### Headline -/

/-- **Reference-output decomposition of mutual information.** For a joint probability law `μ` on `X × Y` (with `X`
standard Borel) and actual marginals `μX`, `μY`, and any output reference probability `Q`,
`KL(μ ‖ μX ⊗ Q) = ofReal (log 2) · I(μ) + KL(μY ‖ Q)` as an identity in `ℝ≥0∞`, including infinite
values (`I` in bits, `KL` in nats). -/
theorem klDiv_prod_reference_eq_measureMutualInformation_add {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] [StandardBorelSpace X] [Nonempty X]
    (μ : ProbabilityMeasure (X × Y)) (Q : Measure Y) [IsProbabilityMeasure Q] :
    klDiv (μ : Measure (X × Y)) (((μ : Measure (X × Y)).map Prod.fst).prod Q) =
      ENNReal.ofReal (Real.log 2) * measureMutualInformation μ +
        klDiv ((μ : Measure (X × Y)).map Prod.snd) Q := by
  rw [klDiv_prod_reference_eq_add, ← ofReal_log_two_mul_measureMutualInformation]

/-! ### Validation -/

/-- Validation, `Q = μY`: the reference divergence is the mutual information in nats. -/
theorem klDiv_prod_marginal_eq_mul_measureMutualInformation {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y]
    (μ : ProbabilityMeasure (X × Y)) :
    klDiv (μ : Measure (X × Y))
        (((μ : Measure (X × Y)).map Prod.fst).prod ((μ : Measure (X × Y)).map Prod.snd)) =
      ENNReal.ofReal (Real.log 2) * measureMutualInformation μ := by
  exact (ofReal_log_two_mul_measureMutualInformation μ).symm

/-- Validation, independent joint law: the product of two probability laws carries zero mutual
information. -/
theorem measureMutualInformation_prod_eq_zero {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] (P : Measure X) [IsProbabilityMeasure P] (R : Measure Y)
    [IsProbabilityMeasure R] :
    measureMutualInformation (⟨P.prod R, inferInstance⟩ : ProbabilityMeasure (X × Y)) = 0 := by
  unfold measureMutualInformation
  have hfst : ((P.prod R).map Prod.fst) = P := by simp
  have hsnd : ((P.prod R).map Prod.snd) = R := by simp
  simp [hfst, hsnd]

/-- Validation, independent joint law against an arbitrary output reference: the identity
collapses to `KL(P ⊗ R ‖ P ⊗ Q) = KL(R ‖ Q)`. -/
theorem klDiv_prod_prod_eq_klDiv {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure X) [IsProbabilityMeasure P] (R Q : Measure Y) [IsProbabilityMeasure R]
    [IsProbabilityMeasure Q] :
    klDiv (P.prod R) (P.prod Q) = klDiv R Q := by
  have hswap : klDiv (P.prod R) (P.prod Q)
      = klDiv ((P.prod R).map Prod.swap) ((P.prod Q).map Prod.swap) :=
    (klDiv_map_swap (P.prod R) (P.prod Q)).symm
  rw [hswap, Measure.prod_swap, Measure.prod_swap]
  have hR : R.prod P = R ⊗ₘ (Kernel.const Y P) := by
    rw [Measure.compProd_const]
  have hQ : Q.prod P = Q ⊗ₘ (Kernel.const Y P) := by
    rw [Measure.compProd_const]
  rw [hR, hQ]
  exact klDiv_compProd_left R Q (Kernel.const Y P)

/-- A singular joint law: the diagonal image `x ↦ (x, x)` of the standard Gaussian on `ℝ`. -/
noncomputable def diagonalGaussian : ProbabilityMeasure (ℝ × ℝ) :=
  ⟨(gaussianReal 0 1).map (fun x => (x, x)), inferInstance⟩

/-- Validation, singular joint law: the diagonal Gaussian has infinite mutual information. -/
theorem measureMutualInformation_diagonalGaussian_eq_top :
    measureMutualInformation diagonalGaussian = ∞ := by
  have hnull : NullSingletonClass (gaussianReal (0 : ℝ) (1 : NNReal)) :=
    nullSingletonClass_gaussianReal (by simp)
  have hdiag_meas : MeasurableSet (Set.diagonal ℝ) := measurableSet_diagonal
  have hmeas : Measurable (fun x : ℝ => (x, x)) := measurable_id.prodMk measurable_id
  have hfst : ((diagonalGaussian : Measure (ℝ × ℝ)).map Prod.fst) = gaussianReal 0 1 := by
    have h1 : (diagonalGaussian : Measure (ℝ × ℝ))
        = (gaussianReal 0 1).map (fun x => (x, x)) := rfl
    rw [h1, Measure.map_map measurable_fst hmeas]
    have hcomp : Prod.fst ∘ (fun x : ℝ => (x, x)) = id := rfl
    rw [hcomp, Measure.map_id]
  have hdiag_one : (diagonalGaussian : Measure (ℝ × ℝ)) (Set.diagonal ℝ) = 1 := by
    have h1 : (diagonalGaussian : Measure (ℝ × ℝ))
        = (gaussianReal 0 1).map (fun x => (x, x)) := rfl
    rw [h1, Measure.map_apply hmeas hdiag_meas]
    have hpre : (fun x : ℝ => (x, x)) ⁻¹' Set.diagonal ℝ = Set.univ := by
      ext x
      simp [Set.mem_preimage, Set.mem_diagonal_iff]
    rw [hpre, measure_univ]
  have hprod_zero : ((((diagonalGaussian : Measure (ℝ × ℝ)).map Prod.fst).prod
      ((diagonalGaussian : Measure (ℝ × ℝ)).map Prod.snd)))
      (Set.diagonal ℝ) = 0 := by
    rw [hfst, Measure.prod_apply_symm hdiag_meas]
    have hforall : ∀ y : ℝ, (gaussianReal 0 1) ((fun x => (x, y)) ⁻¹' Set.diagonal ℝ) = 0 := by
      intro y
      have hset : (fun x : ℝ => (x, y)) ⁻¹' Set.diagonal ℝ = {y} := by
        ext x
        simp [Set.mem_preimage, Set.mem_diagonal_iff]
      rw [hset]
      exact measure_singleton y
    simp [hforall]
  have hnotac : ¬ ((diagonalGaussian : Measure (ℝ × ℝ))
      ≪ (((diagonalGaussian : Measure (ℝ × ℝ)).map Prod.fst).prod
        ((diagonalGaussian : Measure (ℝ × ℝ)).map Prod.snd))) := by
    intro h
    have h1 := h hprod_zero
    rw [hdiag_one] at h1
    simp at h1
  have htop : klDiv (diagonalGaussian : Measure (ℝ × ℝ))
      (((diagonalGaussian : Measure (ℝ × ℝ)).map Prod.fst).prod
        ((diagonalGaussian : Measure (ℝ × ℝ)).map Prod.snd)) = ∞ :=
    klDiv_of_not_ac hnotac
  unfold measureMutualInformation
  rw [htop]
  exact ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top

/-- Validation, singular joint law: the reference divergence is `⊤` for every output reference
probability, so the identity holds as `⊤ = ⊤` rather than vanishing through `toReal`. -/
theorem klDiv_diagonalGaussian_prod_eq_top (Q : Measure ℝ) [IsProbabilityMeasure Q] :
    klDiv (diagonalGaussian : Measure (ℝ × ℝ))
        (((diagonalGaussian : Measure (ℝ × ℝ)).map Prod.fst).prod Q) = ∞ := by
  have hnull : NullSingletonClass (gaussianReal (0 : ℝ) (1 : NNReal)) :=
    nullSingletonClass_gaussianReal (by simp)
  have hdiag_meas : MeasurableSet (Set.diagonal ℝ) := measurableSet_diagonal
  have hmeas : Measurable (fun x : ℝ => (x, x)) := measurable_id.prodMk measurable_id
  have hfst : ((diagonalGaussian : Measure (ℝ × ℝ)).map Prod.fst) = gaussianReal 0 1 := by
    have h1 : (diagonalGaussian : Measure (ℝ × ℝ))
        = (gaussianReal 0 1).map (fun x => (x, x)) := rfl
    rw [h1, Measure.map_map measurable_fst hmeas]
    have hcomp : Prod.fst ∘ (fun x : ℝ => (x, x)) = id := rfl
    rw [hcomp, Measure.map_id]
  have hdiag_one : (diagonalGaussian : Measure (ℝ × ℝ)) (Set.diagonal ℝ) = 1 := by
    have h1 : (diagonalGaussian : Measure (ℝ × ℝ))
        = (gaussianReal 0 1).map (fun x => (x, x)) := rfl
    rw [h1, Measure.map_apply hmeas hdiag_meas]
    have hpre : (fun x : ℝ => (x, x)) ⁻¹' Set.diagonal ℝ = Set.univ := by
      ext x
      simp [Set.mem_preimage, Set.mem_diagonal_iff]
    rw [hpre, measure_univ]
  have hprod_zero : ((((diagonalGaussian : Measure (ℝ × ℝ)).map Prod.fst).prod Q))
      (Set.diagonal ℝ) = 0 := by
    rw [hfst, Measure.prod_apply_symm hdiag_meas]
    have hforall : ∀ y : ℝ, (gaussianReal 0 1) ((fun x => (x, y)) ⁻¹' Set.diagonal ℝ) = 0 := by
      intro y
      have hset : (fun x : ℝ => (x, y)) ⁻¹' Set.diagonal ℝ = {y} := by
        ext x
        simp [Set.mem_preimage, Set.mem_diagonal_iff]
      rw [hset]
      exact measure_singleton y
    simp [hforall]
  have hnotac : ¬ ((diagonalGaussian : Measure (ℝ × ℝ))
      ≪ (((diagonalGaussian : Measure (ℝ × ℝ)).map Prod.fst).prod Q)) := by
    intro h
    have h1 := h hprod_zero
    rw [hdiag_one] at h1
    simp at h1
  exact klDiv_of_not_ac hnotac

/-- Violated premise (`muY` must be the actual output marginal): for the point mass at
`(true, true)` and `Q = δ_true`, replacing the marginal `δ_true` by `δ_false` breaks the
decomposition (`0` on the left, `⊤` on the right). -/
theorem klDiv_prod_wrong_marginal_ne :
    klDiv (Measure.dirac (true, true) : Measure (Bool × Bool))
        ((Measure.dirac true).prod (Measure.dirac true)) ≠
      klDiv (Measure.dirac (true, true) : Measure (Bool × Bool))
          ((Measure.dirac true).prod (Measure.dirac false)) +
        klDiv (Measure.dirac false) (Measure.dirac true) := by
  have hprod1 : ((Measure.dirac true).prod (Measure.dirac true) : Measure (Bool × Bool))
      = Measure.dirac (true, true) := Measure.dirac_prod_dirac
  have hprod2 : ((Measure.dirac true).prod (Measure.dirac false) : Measure (Bool × Bool))
      = Measure.dirac (true, false) := Measure.dirac_prod_dirac
  rw [hprod1, hprod2]
  have hleft : klDiv (Measure.dirac (true, true) : Measure (Bool × Bool))
      (Measure.dirac (true, true)) = 0 := klDiv_self _
  have hnotac1 : ¬ ((Measure.dirac (true, true) : Measure (Bool × Bool))
      ≪ Measure.dirac (true, false)) := by
    intro h
    have h0 : (Measure.dirac (true, false) : Measure (Bool × Bool)) {(true, true)} = 0 := by
      simp
    have h1 := h h0
    simp at h1
  have htop1 : klDiv (Measure.dirac (true, true) : Measure (Bool × Bool))
      (Measure.dirac (true, false)) = ∞ := klDiv_of_not_ac hnotac1
  have hnotac2 : ¬ ((Measure.dirac false : Measure Bool) ≪ Measure.dirac true) := by
    intro h
    have h0 : (Measure.dirac true : Measure Bool) {false} = 0 := by simp
    have h1 := h h0
    simp at h1
  have htop2 : klDiv (Measure.dirac false : Measure Bool) (Measure.dirac true) = ∞ :=
    klDiv_of_not_ac hnotac2
  rw [hleft, htop1, htop2]
  simp

end MathlibExt.InformationTheory.ReferenceOutputKL
