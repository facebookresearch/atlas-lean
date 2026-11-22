/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Sufficiency.Ancillary
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Constructions.Pi

@[expose] public section

namespace MathlibExtTest.Probability.Statistics.Sufficiency.AncillaryNormal

open MeasureTheory ProbabilityTheory

/-- Closed-form centering map for `n = 2`: subtract the explicit average. -/
private noncomputable def centered2 : (Fin 2 → ℝ) → (Fin 2 → ℝ) :=
  fun x i => x i - (x 0 + x 1) / 2

/-- Centering map for `n = 1`: identically zero. -/
private noncomputable def centered1 : (Fin 1 → ℝ) → (Fin 1 → ℝ) :=
  fun x i => x i - x 0

private theorem centered2_meas : Measurable centered2 := by
  unfold centered2
  fun_prop

private theorem centered1_meas : Measurable centered1 := by
  unfold centered1
  fun_prop

private theorem shift_meas (θ : ℝ) :
    Measurable (fun x : Fin 2 → ℝ => fun i => θ + x i) := by
  fun_prop

private theorem centered2_shift (θ : ℝ) (x : Fin 2 → ℝ) :
    centered2 (fun i => θ + x i) = centered2 x := by
  funext i
  show (θ + x i) - ((θ + x 0) + (θ + x 1)) / 2 = x i - (x 0 + x 1) / 2
  ring

private theorem pi_gaussian_shift (θ : ℝ) :
    (Measure.pi fun _ : Fin 2 => gaussianReal (0 : ℝ) 1).map (fun x i => θ + x i)
      = Measure.pi fun _ : Fin 2 => gaussianReal θ 1 := by
  rw [Measure.pi_map_pi (fun i => (measurable_const_add θ).aemeasurable)]
  congr 1
  funext i
  rw [gaussianReal_map_const_add, zero_add]

private theorem map_centered2_eq (θ : ℝ) :
    (Measure.pi fun _ : Fin 2 => gaussianReal θ 1).map centered2
      = (Measure.pi fun _ : Fin 2 => gaussianReal (0 : ℝ) 1).map centered2 := by
  conv_lhs => rw [← pi_gaussian_shift θ]
  rw [Measure.map_map centered2_meas (shift_meas θ)]
  have hcomp : centered2 ∘ (fun x : Fin 2 → ℝ => fun i => θ + x i) = centered2 :=
    funext (fun x => centered2_shift θ x)
  rw [hcomp]

/-- Use case (`n = 2`): the centered normal location vector is ancillary for the
`N(θ, 1)^2` family. Centering kills location, so every pushforward agrees. -/
example :
    MathlibExt.Probability.Statistics.Sufficiency.IsAncillary
      (fun θ : ℝ => ⟨Measure.pi fun _ : Fin 2 => gaussianReal θ 1, inferInstance⟩)
      centered2 := by
  refine ⟨centered2_meas, fun θ₁ θ₂ => ?_⟩
  exact (map_centered2_eq θ₁).trans (map_centered2_eq θ₂).symm

/-- Boundary (`n = 1`, degenerate): centering gives the zero vector, still ancillary
since every pushforward is the Dirac mass at `0`. -/
example :
    MathlibExt.Probability.Statistics.Sufficiency.IsAncillary
      (fun θ : ℝ => ⟨Measure.pi fun _ : Fin 1 => gaussianReal θ 1, inferInstance⟩)
      centered1 := by
  refine MathlibExt.Probability.Statistics.Sufficiency.isAncillary_of_ae_const
    (c := (0 : Fin 1 → ℝ)) ?_ centered1_meas
  intro θ
  apply Filter.Eventually.of_forall
  intro x
  show centered1 x = 0
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  show x i - x 0 = 0
  rw [hi, sub_self]

/-- Counter-case (varying scale): for the scale-indexed Dirac family
`Q s = dirac (s • u)` on the fixed non-centered direction
`u = fun i => if i = 0 then 1 else 0`, the centered pushforward at scale `0` is
`dirac 0` while at scale `1` it is `dirac` at the nonzero point `centered2 u`;
hence the pushforwards differ and `centered2` is not ancillary for `Q`. -/
example :
    ¬ MathlibExt.Probability.Statistics.Sufficiency.IsAncillary
      (fun s : ℝ => ⟨Measure.dirac
        (fun i : Fin 2 => s * (if i = 0 then (1 : ℝ) else 0)), inferInstance⟩)
      centered2 := by
  intro h
  obtain ⟨-, heq⟩ := h
  have h01 := heq (0 : ℝ) (1 : ℝ)
  have h01' : Measure.map centered2
        (Measure.dirac (fun i : Fin 2 => (0 : ℝ) * (if i = 0 then (1 : ℝ) else 0)))
      = Measure.map centered2
        (Measure.dirac (fun i : Fin 2 => (1 : ℝ) * (if i = 0 then (1 : ℝ) else 0))) := h01
  rw [Measure.map_dirac' centered2_meas, Measure.map_dirac' centered2_meas] at h01'
  have hz : centered2 (fun i : Fin 2 => (0 : ℝ) * (if i = 0 then (1 : ℝ) else 0))
      = 0 := by
    funext i
    show (0 : ℝ) * (if i = 0 then (1 : ℝ) else 0) -
      (((0 : ℝ) * (if (0 : Fin 2) = 0 then (1 : ℝ) else 0)) +
        ((0 : ℝ) * (if (1 : Fin 2) = 0 then (1 : ℝ) else 0))) / 2 = 0
    simp
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  have hhalf : centered2
        (fun i : Fin 2 => (1 : ℝ) * (if i = 0 then (1 : ℝ) else 0)) 0 = 1 / 2 := by
    show (1 : ℝ) * (if (0 : Fin 2) = 0 then (1 : ℝ) else 0) -
      (((1 : ℝ) * (if (0 : Fin 2) = 0 then (1 : ℝ) else 0)) +
        ((1 : ℝ) * (if (1 : Fin 2) = 0 then (1 : ℝ) else 0))) / 2 = 1 / 2
    rw [ite_eq_left rfl, ite_eq_right h10]
    norm_num
  have hne : centered2
      (fun i : Fin 2 => (1 : ℝ) * (if i = 0 then (1 : ℝ) else 0)) ≠ 0 := by
    intro hcon
    have h0 := congrFun hcon (0 : Fin 2)
    rw [hhalf, Pi.zero_apply] at h0
    norm_num at h0
  rw [hz] at h01'
  rw [dirac_eq_dirac_iff] at h01'
  exact hne h01'.symm

end MathlibExtTest.Probability.Statistics.Sufficiency.AncillaryNormal
