/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.MachineLearning.Sequence.KalmanFilter

open Cslib.MachineLearning.Sequence.KalmanFilter MeasureTheory ProbabilityTheory Matrix WithLp

-- Scalar random walk `x' = x + w`, `w ~ N(0, 1)`, from `N(0, 1)`: the predicted variance is 2.
example : (predict (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 ⟨0, 1⟩).cov = 2 := by
  simp [predict]
  norm_num

-- Observing it directly with noise variance 2 gives the gain `2 / (2 + 2) = 1 / 2`.
example : gain (1 : Matrix (Fin 1) (Fin 1) ℝ) !![2] ⟨0, !![2]⟩ 0 0 = 1 / 2 := by
  simp [gain, mul_apply]
  norm_num

-- One exact filter step for a two-dimensional state observed through one coordinate.
example {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {x w : Ω → EuclideanSpace ℝ (Fin 2)} {v : Ω → EuclideanSpace ℝ (Fin 1)}
    (hx : Measurable x) (hw : Measurable w) (hv : Measurable v) (hxw : IndepFun x w P)
    (hxwv : IndepFun (fun ω => (x ω, w ω)) v P) {b : Belief (Fin 2)}
    {Q : Matrix (Fin 2) (Fin 2) ℝ} {R : Matrix (Fin 1) (Fin 1) ℝ} (hP : b.cov.PosSemidef)
    (hQ : Q.PosSemidef) (hR : R.PosSemidef) (hxl : P.map x = b.law)
    (hwl : P.map w = multivariateGaussian 0 Q) (hvl : P.map v = multivariateGaussian 0 R)
    (F : Matrix (Fin 2) (Fin 2) ℝ) (H : Matrix (Fin 1) (Fin 2) ℝ)
    (hinv : IsUnit (H * (predict F Q b).cov * Hᵀ + R).det) :
    ∀ᵐ y ∂P.map (fun ω => toEuclideanLin H (toEuclideanLin F (x ω) + w ω) + v ω),
      condDistrib (fun ω => toEuclideanLin F (x ω) + w ω)
          (fun ω => toEuclideanLin H (toEuclideanLin F (x ω) + w ω) + v ω) P y =
        (step F Q H R y b).law :=
  condDistrib_step hx hw hv hxw hxwv hP hQ hR hxl hwl hvl F H hinv

-- Filter steps keep the belief a valid Gaussian.
example (F Q : Matrix (Fin 2) (Fin 2) ℝ) (H : Matrix (Fin 1) (Fin 2) ℝ)
    {R : Matrix (Fin 1) (Fin 1) ℝ} (y : EuclideanSpace ℝ (Fin 1)) {b : Belief (Fin 2)}
    (hb : b.Valid) (hQ : Q.PosSemidef) (hR : R.PosDef) : (step F Q H R y b).Valid :=
  step_valid F Q H y hb hQ hR

/-! ### The filter over an observation history -/

/-- The scalar model with `F = G = Q = H = R = 1` from the prior `N(0, 1)`: after the first
observation the filtered variance is `1 - 1 / (1 + 1) = 1 / 2`. -/
example (ζ : Fin 1 → EuclideanSpace ℝ (Fin 1)) :
    (filteredBelief (n := Fin 1) (r := Fin 1) (fun _ => 1) (fun _ => 1) (fun _ => 1)
      (fun _ => 1) (fun _ => 1) ⟨0, 1⟩ 0 ζ).cov 0 0 = 1 / 2 := by
  simp [filteredBelief, predictedBelief, update, gain, Ring.inverse_eq_inv]
  norm_num

/-- In the same model, the next predicted variance is `1 / 2 + 1 = 3 / 2`, whatever the first
observation. -/
example (ζ : Fin 1 → EuclideanSpace ℝ (Fin 1)) :
    (predictedBelief (n := Fin 1) (r := Fin 1) (fun _ => 1) (fun _ => 1) (fun _ => 1)
      (fun _ => 1) (fun _ => 1) ⟨0, 1⟩ 1 ζ).cov 0 0 = 3 / 2 := by
  simp [predictedBelief, predict, update, gain, Ring.inverse_eq_inv]
  norm_num

/-- **Non-vacuity of `condDistrib_observationHistory`.** The canonical model with horizon `1`:
the initial state and the noises are the coordinates of the product of their Gaussian laws, and
the state and the observations are built from them by the signal model. All hypotheses hold, so
the theorem applies; here, the filtered mean after two observations is the conditional
expectation of the state `x₁`. -/
example (F G Q H R : ℕ → Matrix (Fin 1) (Fin 1) ℝ) (b₀ : Belief (Fin 1)) (hP₀ : b₀.Valid)
    (hQ : ∀ k < 1, (Q k).PosSemidef) (hR : ∀ k ≤ 1, (R k).PosDef) :
    let μ := b₀.law.prod ((Measure.pi fun i : Fin 1 => multivariateGaussian 0 (Q i)).prod
      (Measure.pi fun i : Fin 2 => multivariateGaussian 0 (R i)))
    let w : ℕ → EuclideanSpace ℝ (Fin 1) × (Fin 1 → EuclideanSpace ℝ (Fin 1)) ×
      (Fin 2 → EuclideanSpace ℝ (Fin 1)) → EuclideanSpace ℝ (Fin 1) := fun _ ω => ω.2.1 0
    let v : ℕ → EuclideanSpace ℝ (Fin 1) × (Fin 1 → EuclideanSpace ℝ (Fin 1)) ×
      (Fin 2 → EuclideanSpace ℝ (Fin 1)) → EuclideanSpace ℝ (Fin 1) :=
      fun k ω => if hk : k < 2 then ω.2.2 ⟨k, hk⟩ else 0
    let x : ℕ → EuclideanSpace ℝ (Fin 1) × (Fin 1 → EuclideanSpace ℝ (Fin 1)) ×
      (Fin 2 → EuclideanSpace ℝ (Fin 1)) → EuclideanSpace ℝ (Fin 1) := fun k ω =>
      if k = 0 then ω.1 else toEuclideanLin (F 0) ω.1 + toEuclideanLin (G 0) (w 0 ω)
    let z : ℕ → EuclideanSpace ℝ (Fin 1) × (Fin 1 → EuclideanSpace ℝ (Fin 1)) ×
      (Fin 2 → EuclideanSpace ℝ (Fin 1)) → EuclideanSpace ℝ (Fin 1) := fun k ω =>
      toEuclideanLin (H k)ᵀ (x k ω) + v k ω
    μ[x 1 | MeasurableSpace.comap (fun ω (i : Fin 2) => z i ω) inferInstance] =ᵐ[μ]
      fun ω => (filteredBelief F G Q H R b₀ 1 fun i => z i ω).mean := by
  intro μ w v x z
  have : IsProbabilityMeasure b₀.law := by rw [Belief.law]; infer_instance
  have hid : (fun ω : EuclideanSpace ℝ (Fin 1) × (Fin 1 → EuclideanSpace ℝ (Fin 1)) ×
      (Fin 2 → EuclideanSpace ℝ (Fin 1)) =>
        (x 0 ω, (fun i : Fin 1 => w i ω), fun i : Fin 2 => v i ω)) = id := by
    funext ω
    refine Prod.ext rfl (Prod.ext (funext fun i => ?_) (funext fun i => ?_))
    · simp [w, Subsingleton.elim i 0]
    · fin_cases i <;> rfl
  refine (condDistrib_observationHistory hP₀ hQ hR (x := x) (w := w) (v := v) (z := z)
    (by fun_prop) (fun _ _ => by fun_prop) (fun _ _ => by fun_prop)
    (fun k hk ω => by obtain rfl : k = 0 := (by omega); simp [x]) (fun _ _ _ => rfl)
    (by rw [hid, Measure.map_id]) le_rfl).2.2.2.1

#print axioms condDistrib_step
#print axioms condDistrib_observationHistory
