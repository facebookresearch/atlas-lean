/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.IsingTorusCharacterCoordinates
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

open MeasureTheory Set
open scoped BigOperators ComplexConjugate ENNReal Real RealInnerProductSpace

namespace StatMech.FrontierA

abbrev IsingMomentumSpace (d : Nat) := EuclideanSpace Real (Fin d)

def isingMomentumCube (d : Nat) : Set (IsingMomentumSpace d) :=
  {p | ∀ i, |p i| ≤ Real.pi}

noncomputable def isingContinuumDispersion {d : Nat}
    (p : IsingMomentumSpace d) : Real :=
  ∑ i : Fin d, (2 - 2 * Real.cos (p i))

noncomputable def isingContinuumInverseDispersion {d : Nat}
    (p : IsingMomentumSpace d) : Real :=
  if p = 0 then 0 else (isingContinuumDispersion p)⁻¹

noncomputable def isingContinuumGreenDensity (d : Nat) :
    IsingMomentumSpace d → Complex :=
  (isingMomentumCube d).indicator
    (fun p => (isingContinuumInverseDispersion p : Complex))

theorem measurableSet_isingMomentumCube (d : Nat) :
    MeasurableSet (isingMomentumCube d) := by
  unfold isingMomentumCube
  rw [show {p : IsingMomentumSpace d | ∀ i : Fin d, |p i| ≤ Real.pi} =
      ⋂ i : Fin d, {p : IsingMomentumSpace d | |p i| ≤ Real.pi} by
    ext p
    simp]
  apply MeasurableSet.iInter
  intro i
  apply measurableSet_le _ measurable_const
  exact (by fun_prop)

theorem isingMomentumCube_zero (d : Nat) :
    (0 : IsingMomentumSpace d) ∈ isingMomentumCube d := by
  intro i
  simp [Real.pi_pos.le]

theorem continuous_isingContinuumDispersion (d : Nat) :
    Continuous (isingContinuumDispersion : IsingMomentumSpace d → Real) := by
  unfold isingContinuumDispersion
  fun_prop

theorem isingContinuumDispersion_nonneg {d : Nat}
    (p : IsingMomentumSpace d) :
    0 ≤ isingContinuumDispersion p := by
  unfold isingContinuumDispersion
  apply Finset.sum_nonneg
  intro i _
  nlinarith [Real.neg_one_le_cos (p i), Real.cos_le_one (p i)]

theorem isingContinuumDispersion_quadratic_lower {d : Nat}
    {p : IsingMomentumSpace d} (hp : p ∈ isingMomentumCube d) :
    (4 / Real.pi ^ 2) * ‖p‖ ^ 2 ≤ isingContinuumDispersion p := by
  have hpi : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  have hi (i : Fin d) :
      (4 / Real.pi ^ 2) * (p i) ^ 2 ≤
        2 - 2 * Real.cos (p i) := by
    have hcos := Real.cos_le_one_sub_mul_cos_sq (hp i)
    calc
      (4 / Real.pi ^ 2) * (p i) ^ 2 =
          2 * ((2 / Real.pi ^ 2) * (p i) ^ 2) := by ring
      _ ≤ 2 * (1 - Real.cos (p i)) := by
        gcongr
        linarith
      _ = 2 - 2 * Real.cos (p i) := by ring
  unfold isingContinuumDispersion
  calc
    (4 / Real.pi ^ 2) * ‖p‖ ^ 2 =
        ∑ i : Fin d, (4 / Real.pi ^ 2) * (p i) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp [Real.norm_eq_abs, sq_abs]
    _ ≤ ∑ i : Fin d, (2 - 2 * Real.cos (p i)) :=
      Finset.sum_le_sum fun i _ => hi i

theorem isingContinuumDispersion_pos {d : Nat}
    {p : IsingMomentumSpace d} (hp : p ∈ isingMomentumCube d)
    (hp0 : p ≠ 0) :
    0 < isingContinuumDispersion p := by
  have hcoef : 0 < 4 / Real.pi ^ 2 := div_pos (by norm_num) (sq_pos_of_pos Real.pi_pos)
  have hnorm : 0 < ‖p‖ := norm_pos_iff.mpr hp0
  exact lt_of_lt_of_le (mul_pos hcoef (sq_pos_of_pos hnorm))
    (isingContinuumDispersion_quadratic_lower hp)

theorem measurable_isingContinuumInverseDispersion (d : Nat) :
    Measurable (isingContinuumInverseDispersion :
      IsingMomentumSpace d → Real) := by
  unfold isingContinuumInverseDispersion
  apply Measurable.ite (MeasurableSet.singleton 0) measurable_const
  exact (continuous_isingContinuumDispersion d).measurable.inv

theorem measurable_isingContinuumGreenDensity (d : Nat) :
    Measurable (isingContinuumGreenDensity d) := by
  unfold isingContinuumGreenDensity
  apply Measurable.indicator _ (measurableSet_isingMomentumCube d)
  exact Complex.measurable_ofReal.comp
    (measurable_isingContinuumInverseDispersion d)

theorem norm_isingContinuumGreenDensity_le {d : Nat}
    (p : IsingMomentumSpace d) :
    ‖isingContinuumGreenDensity d p‖ ≤
      (Real.pi ^ 2 / 4) * ‖p‖ ^ (-2 : Real) := by
  by_cases hpCube : p ∈ isingMomentumCube d
  · rw [isingContinuumGreenDensity, Set.indicator_of_mem hpCube]
    by_cases hp0 : p = 0
    · subst p
      simp [isingContinuumInverseDispersion]
      positivity
    · have hdisp := isingContinuumDispersion_pos hpCube hp0
      have hcoef : 0 < 4 / Real.pi ^ 2 :=
        div_pos (by norm_num) (sq_pos_of_pos Real.pi_pos)
      have hnorm : 0 < ‖p‖ := norm_pos_iff.mpr hp0
      have hlower : 0 < (4 / Real.pi ^ 2) * ‖p‖ ^ 2 :=
        mul_pos hcoef (sq_pos_of_pos hnorm)
      have hinv : (isingContinuumDispersion p)⁻¹ ≤
          ((4 / Real.pi ^ 2) * ‖p‖ ^ 2)⁻¹ := by
        exact (inv_le_inv₀ hdisp hlower).2
          (isingContinuumDispersion_quadratic_lower hpCube)
      rw [isingContinuumInverseDispersion, if_neg hp0,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hdisp)]
      calc
        (isingContinuumDispersion p)⁻¹ ≤
            ((4 / Real.pi ^ 2) * ‖p‖ ^ 2)⁻¹ := hinv
        _ = (Real.pi ^ 2 / 4) * ‖p‖ ^ (-2 : Real) := by
          rw [Real.rpow_neg (norm_nonneg p)]
          field_simp
          exact Real.rpow_natCast _ 2
  · rw [isingContinuumGreenDensity, Set.indicator_of_notMem hpCube, norm_zero]
    exact mul_nonneg (div_nonneg (sq_nonneg _) (by norm_num)) (Real.rpow_nonneg (norm_nonneg p) _)

theorem isBounded_isingMomentumCube (d : Nat) :
    Bornology.IsBounded (isingMomentumCube d) := by
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨Real.sqrt ((d : Real) * Real.pi ^ 2), ?_⟩
  intro p hp
  have hsq : ‖p‖ ^ 2 ≤ (d : Real) * Real.pi ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      ∑ i : Fin d, ‖p i‖ ^ 2 ≤ ∑ _i : Fin d, Real.pi ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        rw [Real.norm_eq_abs]
        nlinarith [hp i, abs_nonneg (p i), Real.pi_pos.le]
      _ = (d : Real) * Real.pi ^ 2 := by simp
  have hbase : 0 ≤ (d : Real) * Real.pi ^ 2 :=
    mul_nonneg (Nat.cast_nonneg d) (sq_nonneg Real.pi)
  rw [← sq_le_sq₀ (norm_nonneg p) (Real.sqrt_nonneg _), Real.sq_sqrt hbase]
  exact hsq

theorem integrable_isingContinuumGreenDensity
    {d : Nat} (hd : 2 < d) :
    Integrable (isingContinuumGreenDensity d) := by
  obtain ⟨R, hRpos, hR⟩ :=
    (isBounded_isingMomentumCube d).exists_pos_norm_lt
  have hdim : 1 ≤ Module.finrank Real (IsingMomentumSpace d) := by
    simp only [finrank_euclideanSpace, Fintype.card_fin]
    omega
  have halpha : (2 : Real) < Module.finrank Real (IsingMomentumSpace d) := by
    simp only [finrank_euclideanSpace, Fintype.card_fin]
    exact_mod_cast hd
  have hmeas : AEStronglyMeasurable (isingContinuumGreenDensity d) :=
    (measurable_isingContinuumGreenDensity d).aestronglyMeasurable
  have hdecay : ∀ᵐ p ∂(volume.restrict (Metric.ball
      (0 : IsingMomentumSpace d) R)),
      ‖isingContinuumGreenDensity d p‖ ≤
        (Real.pi ^ 2 / 4) * ‖p‖ ^ (-2 : Real) :=
    Filter.Eventually.of_forall norm_isingContinuumGreenDensity_le
  have hint : IntegrableOn (isingContinuumGreenDensity d)
      (Metric.ball (0 : IsingMomentumSpace d) R) :=
    integrableOn_ball_of_norm_le_rpow hdim halpha hdecay hmeas
  apply hint.integrable_of_forall_notMem_eq_zero
  intro p hpBall
  have hpCube : p ∉ isingMomentumCube d := by
    intro hp
    apply hpBall
    simpa only [Metric.mem_ball, dist_zero_right] using hR p hp
  simp [isingContinuumGreenDensity, hpCube]

noncomputable def isingContinuumGreen (d : Nat) :
    IsingMomentumSpace d → Complex :=
  fun x ↦ ∫ p, Real.fourierChar (-⟪p, x⟫) •
    isingContinuumGreenDensity d p

theorem isingContinuumGreen_tendsto_zero
    {d : Nat} (hd : 2 < d) :
    Filter.Tendsto (isingContinuumGreen d)
      (Filter.cocompact (IsingMomentumSpace d)) (nhds 0) := by
  have _hIntegrable := integrable_isingContinuumGreenDensity hd
  simpa only [isingContinuumGreen] using
    (tendsto_integral_exp_inner_smul_cocompact
      (isingContinuumGreenDensity d))

end StatMech.FrontierA
