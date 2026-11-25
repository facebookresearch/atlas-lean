/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Circuits.BoxTerminalFlux

@[expose] public section

open PhyslibExt.Circuits.BoxTerminalFlux MeasureTheory

namespace PhyslibExtTest.Circuits.BoxTerminalFlux

/-- Through-flow currents `(-3, 3, 0, 0, 0, 0)` sum to zero. -/
example : ∑ f : Fin 6, (![-3, 3, 0, 0, 0, 0] : Fin 6 → ℝ) f = 0 :=
  throughFlow_currents_sum_example

/-- Accumulating-charge currents sum to `-2`, keeping the nonzero
charge-rate term. -/
example : ∑ f : Fin 6, (![-2, 0, 0, 0, 0, 0] : Fin 6 → ℝ) f = -2 :=
  accumulatingCharge_currents_sum_example

/-- Omitting the entering face leaves a nonzero sum. -/
example : ∑ f : Fin 6, (![0, 3, 0, 0, 0, 0] : Fin 6 → ℝ) f ≠ 0 :=
  omittedFace_currents_sum_example

/-- The ohmic density at a point is conductivity times the normal
field component: `2 * 3 = 6`. -/
example : ohmicDensity 2 (fun _ _ => 3) 0 (0, 0) = 6 := by
  norm_num [ohmicDensity, PhyslibExt.Circuits.UniformOhmicBar.ohmCurrentDensity]

/-- With zero charge rate, the end-face currents of the through-flow
example cancel. -/
example : (![-3, 3, 0, 0, 0, 0] : Fin 6 → ℝ) 0 +
    (![-3, 3, 0, 0, 0, 0] : Fin 6 → ℝ) 1 = 0 := by
  have hsum : ∑ f : Fin 6, (![-3, 3, 0, 0, 0, 0] : Fin 6 → ℝ) f = -(0 : ℝ) := by
    rw [neg_zero]
    exact throughFlow_currents_sum_example
  have h := endFaceCurrents_add_eq_neg_chargeRate_of_sideFaces_zero
    (![-3, 3, 0, 0, 0, 0] : Fin 6 → ℝ) 0 hsum (by
      intro f hf0 hf1
      fin_cases f <;> simp_all)
  rw [neg_zero] at h
  exact h

/-! ### Interface on finite rectangles -/

/-- The rectangle `[0, 2] × [0, 3]` has area `6`. -/
lemma volume_rect : volume (Set.Icc ((0 : ℝ), (0 : ℝ)) (2, 3)) = 6 := by
  rw [← Set.Icc_prod_Icc, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc,
    Real.volume_Icc, ← ENNReal.ofReal_mul (by norm_num)]
  norm_num

/-- A constant density `5` over the rectangle `[0, 2] × [0, 3]` has
finite area `6`, is integrable, and has flux `30`. -/
example : faceFlux (fun _ => Set.Icc ((0 : ℝ), (0 : ℝ)) (2, 3)) (fun _ _ => 5) 0 = 30 := by
  obtain ⟨-, -, h⟩ := faceFlux_of_const_of_measure_ne_top
    (fun _ => Set.Icc ((0 : ℝ), (0 : ℝ)) (2, 3)) (fun _ _ => 5) 0 5 measurableSet_Icc
    (by rw [volume_rect]; exact ENNReal.ofNat_ne_top) (fun _ _ => rfl)
  rw [h, Measure.real, volume_rect]
  norm_num

/-- Ohmic scaling on the rectangle: conductivity `2` and a normal field
`3` give flux `2 * 18 = 36`. -/
example : faceFlux (fun _ => Set.Icc ((0 : ℝ), (0 : ℝ)) (2, 3))
    (ohmicDensity 2 (fun _ _ => 3)) 0 = 36 := by
  rw [faceFlux_ohmicDensity 2 _ _ 0,
    faceFlux_of_const _ _ 0 3 measurableSet_Icc (fun _ _ => rfl), Measure.real, volume_rect]
  norm_num

/-- Six disjoint unit squares `[2f, 2f + 1] × [0, 1]` as face domains. -/
def squares (f : Fin 6) : Set (ℝ × ℝ) :=
  Set.Icc ((2 * (f : ℕ) : ℝ), 0) (2 * (f : ℕ) + 1, 1)

lemma volume_squares (f : Fin 6) : volume (squares f) = 1 := by
  rw [squares, ← Set.Icc_prod_Icc, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc,
    Real.volume_Icc]
  norm_num

/-- Through-flow densities `-3` and `3` on the end squares, `0` on the
sides. -/
def throughDensity (f : Fin 6) (_ : ℝ × ℝ) : ℝ := (![-3, 3, 0, 0, 0, 0] : Fin 6 → ℝ) f

lemma faceFlux_squares (f : Fin 6) :
    faceFlux squares throughDensity f = (![-3, 3, 0, 0, 0, 0] : Fin 6 → ℝ) f := by
  rw [faceFlux_of_const squares throughDensity f ((![-3, 3, 0, 0, 0, 0] : Fin 6 → ℝ) f)
    measurableSet_Icc (fun _ _ => rfl), Measure.real, volume_squares]
  simp

/-- The interface transfer applied to computed through-flow fluxes on
six unit squares: continuity with rate zero holds, and the terminal
currents sum to zero. -/
example : ∑ f : Fin 6, faceFlux squares throughDensity f = 0 := by
  have hcont : chargeContinuity (faceFlux squares throughDensity) 0 := by
    simp [chargeContinuity, faceFlux_squares, Fin.sum_univ_six]
  have h := sum_terminalCurrent_eq_neg_chargeRate squares throughDensity _ 0 (fun _ => rfl) hcont
  rwa [neg_zero] at h

/-- Uniform through-flow on the two finite end squares of area `1`, with
densities `-3` and `3`: the end-face currents are opposite. -/
example : faceFlux squares throughDensity 1 = -faceFlux squares throughDensity 0 :=
  uniformThroughFlow_endFlux_opposite squares throughDensity 3 measurableSet_Icc
    measurableSet_Icc (by rw [volume_squares]; exact ENNReal.one_ne_top)
    (by rw [volume_squares]; exact ENNReal.one_ne_top)
    (by rw [Measure.real, Measure.real, volume_squares, volume_squares])
    (fun _ _ => rfl) (fun _ _ => rfl)

/-! ### The unit cube in space -/

/-- Each face of the unit cube has area `1`. -/
lemma volume_unitCube_face (f : Fin 6) : volume (boxFaceDomain 0 1 f) = 1 := by
  simp [boxFaceDomain, Real.volume_Icc_pi]

/-- Uniform flow `c` along axis `0`. -/
def uniformFlow (c : ℝ) (_ : Fin 3 → ℝ) : Fin 3 → ℝ := Pi.single 0 c

lemma boxOutwardFlux_uniformFlow (c : ℝ) (f : Fin 6) :
    boxOutwardFlux 0 1 (uniformFlow c) f = (![-c, c, 0, 0, 0, 0] : Fin 6 → ℝ) f := by
  have hconst : ∀ x, boxNormalDensity 0 1 (uniformFlow c) f x =
      faceSign f * (Pi.single 0 c : Fin 3 → ℝ) (faceAxis f) := fun _ => rfl
  simp only [boxOutwardFlux, hconst, setIntegral_const, smul_eq_mul, Measure.real,
    volume_unitCube_face, ENNReal.toReal_one, one_mul]
  fin_cases f <;> simp [faceSign, faceIsUpper, faceAxis]

/-- Uniform through-flow on the unit cube: the end faces carry opposite
outward currents `-c` and `c`. -/
example (c : ℝ) : boxOutwardFlux 0 1 (uniformFlow c) 1 =
    -boxOutwardFlux 0 1 (uniformFlow c) 0 := by
  simp [boxOutwardFlux_uniformFlow]

/-- Constant enclosed charge (static density `1`) and divergence-free
uniform flow: the derived balance gives zero total outward flux. -/
example (c : ℝ) : ∑ f : Fin 6, boxOutwardFlux 0 1 (uniformFlow c) f = 0 :=
  sum_boxOutwardFlux_eq_zero_of_enclosedCharge_const 0 1 zero_le_one (fun _ _ => 1)
    (fun _ _ => 0) continuous_const continuous_const (fun _ _ => hasDerivAt_const _ _) 0
    (fun _ => rfl) (uniformFlow c) (fun _ => 0) continuous_const.continuousOn
    (fun _ _ => hasFDerivAt_const _ _) (fun x _ => by simp [fderivDivergence])

/-- The same uniform flow through the headline: terminal currents read
from the six faces sum to zero because the enclosed charge is constant,
and the computed end-face currents are `-c` and `c`. -/
example (c : ℝ) : ∑ f : Fin 6, (![-c, c, 0, 0, 0, 0] : Fin 6 → ℝ) f = 0 :=
  boxTerminalCurrents_sum_eq_zero_of_constantCharge 0 1 zero_le_one (fun _ _ => 1)
    (fun _ _ => 0) continuous_const continuous_const (fun _ _ => hasDerivAt_const _ _) 0
    (fun _ => rfl) (uniformFlow c) (fun _ => 0) continuous_const.continuousOn
    (fun _ _ => hasFDerivAt_const _ _) (fun x _ => by simp [fderivDivergence]) _
    (fun f => (boxOutwardFlux_uniformFlow c f).symm)

/-- The linear field `J x = x` has divergence `3`. With charge-density
rate `-3` (the cube is losing charge), the derived balance gives total
outward current `3`, keeping the nonzero rate term. -/
example : ∑ f : Fin 6, boxOutwardFlux 0 1 (fun x => x) f = 3 := by
  have h := boxTerminalCurrents_sum_eq_neg_chargeRate 0 1 zero_le_one (fun x => x)
    (fun _ => ContinuousLinearMap.id ℝ _) continuous_id.continuousOn
    (fun x _ => hasFDerivAt_id x) (fun _ => -3) (integrableOn_const isCompact_Icc.measure_lt_top.ne)
    (fun x _ => by simp [fderivDivergence]) _ (fun _ => rfl)
  rw [h, setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Icc_pi]
  simp

/-- A charge density growing at unit rate gives an enclosed charge
growing at the cube volume `1`. -/
example : HasDerivAt (enclosedCharge 0 1 fun s _ => s) 1 0 := by
  have h := hasDerivAt_enclosedCharge 0 1 (fun s _ => s) (fun _ _ => 1)
    continuous_fst continuous_const (fun s _ => hasDerivAt_id s) 0
  simpa [setIntegral_const, Measure.real, Real.volume_Icc_pi] using h

/-- The inward field `J x = -(1/3) x` has divergence `-1`, so it feeds the
density growing at unit rate. The enclosed charge then changes at minus
the total outward flux, and since it grows at rate `1`, the six outward
fluxes sum to `-1`: charge flows in, the nonzero rate term is kept. -/
example : ∑ f : Fin 6, boxOutwardFlux 0 1 (fun x => -(1 / 3 : ℝ) • x) f = -1 := by
  have hJ : ∀ x, HasFDerivAt (fun x : Fin 3 → ℝ => -(1 / 3 : ℝ) • x)
      (-(1 / 3 : ℝ) • ContinuousLinearMap.id ℝ (Fin 3 → ℝ)) x := fun x =>
    (hasFDerivAt_id x).const_smul (-(1 / 3 : ℝ))
  have hbal := hasDerivAt_enclosedCharge_eq_neg_sum_boxOutwardFlux 0 1 zero_le_one
    (fun s _ => s) (fun _ _ => 1) continuous_fst continuous_const
    (fun s _ => hasDerivAt_id s) 0 (fun x => -(1 / 3 : ℝ) • x)
    (fun _ => -(1 / 3 : ℝ) • ContinuousLinearMap.id ℝ (Fin 3 → ℝ))
    (by fun_prop : Continuous fun x : Fin 3 → ℝ => -(1 / 3 : ℝ) • x).continuousOn
    (fun x _ => hJ x) (fun x _ => by simp [fderivDivergence])
  have hrate := hasDerivAt_enclosedCharge 0 1 (fun s _ => s) (fun _ _ => 1)
    continuous_fst continuous_const (fun s _ => hasDerivAt_id s) 0
  have h1 : (∫ _ in Set.Icc (0 : Fin 3 → ℝ) 1, (1 : ℝ)) = 1 := by
    simp [setIntegral_const, Measure.real, Real.volume_Icc_pi]
  rw [h1] at hrate
  have := hbal.unique hrate
  linarith

end PhyslibExtTest.Circuits.BoxTerminalFlux
