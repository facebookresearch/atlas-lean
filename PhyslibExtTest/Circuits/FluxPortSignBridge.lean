/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Circuits.FluxPortSignBridge
import Mathlib.Tactic.Linarith

@[expose] public section

open MeasureTheory Matrix
open PhyslibExt.Circuits.ArcPortSigns
open PhyslibExt.Circuits.BoxTerminalFlux
open PhyslibExt.Circuits.FluxPortSignBridge

namespace PhyslibExtTest.Circuits.FluxPortSignBridge

/-- Constant outward densities `(-c, c, 0, 0, 0, 0)` on the six face domains of area `1/2`
give the face fluxes `(-c/2, c/2, 0, 0, 0, 0)`. -/
example (c : ℝ) (f : Fin 6) :
    faceFlux (fun g : Fin 6 => Set.Icc (g.val : ℝ) (g.val + 1 / 2) ×ˢ Set.Icc (0 : ℝ) 1)
      (fun g _ => equalOppositeFlux c g) f = 1 / 2 * equalOppositeFlux c f := by
  rw [faceFlux_of_const (fun g : Fin 6 => Set.Icc (g.val : ℝ) (g.val + 1 / 2) ×ˢ Set.Icc (0 : ℝ) 1)
    (fun g _ => equalOppositeFlux c g) f (equalOppositeFlux c f)
    (measurableSet_Icc.prod measurableSet_Icc) (fun _ _ => rfl)]
  simp only [Measure.real, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc]
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num),
    ENNReal.toReal_ofReal (by norm_num)]
  ring

/-- Headline on the six-face field data: with steady charge, the sign-converted port currents
of the two-terminal network give zero outflow at the box node, equal to the flux sum, and every
compatible injection vanishes there. -/
example (c : ℝ) :
    let D : Fin 6 → Set (ℝ × ℝ) := fun g =>
      Set.Icc (g.val : ℝ) (g.val + 1 / 2) ×ˢ Set.Icc (0 : ℝ) 1
    let I := faceFlux D (fun g _ => equalOppositeFlux c g)
    let i : Fin 6 → ℝ := fun e => portSign twoTerminalTail 0 e * I e
    (electricalIncidence twoTerminalTail twoTerminalHead *ᵥ i) 0 = ∑ f : Fin 6, I f ∧
      (electricalIncidence twoTerminalTail twoTerminalHead *ᵥ i) 0 = 0 ∧
      ∀ j : Fin 3 → ℝ, electricalIncidence twoTerminalTail twoTerminalHead *ᵥ i = j →
        j 0 = 0 := by
  intro D I i
  have hflux : ∀ f, I f = 1 / 2 * equalOppositeFlux c f := by
    intro f
    simp only [I, D]
    rw [faceFlux_of_const
      (fun g : Fin 6 => Set.Icc (g.val : ℝ) (g.val + 1 / 2) ×ˢ Set.Icc (0 : ℝ) 1)
      (fun g _ => equalOppositeFlux c g) f (equalOppositeFlux c f)
      (measurableSet_Icc.prod measurableSet_Icc) (fun _ _ => rfl)]
    simp only [Measure.real, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc]
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num),
      ENNReal.toReal_ofReal (by norm_num)]
    ring
  have hsteady : chargeContinuity (faceFlux D (fun g _ => equalOppositeFlux c g)) 0 := by
    change ∑ f : Fin 6, I f = -0
    simp only [hflux, Fin.sum_univ_six, equalOppositeFlux]
    simp
  exact fluxPortSignBridge_correct D _ I (fun _ => rfl) hsteady
    twoTerminalTail twoTerminalHead 0 id i (twoTerminal_equalOppositeFlux c).1 (fun _ => rfl)

/-- On the six-face field data the sign-converted branch currents are those of the
two-terminal network at flux `c/2`, and current balance gives the injection
`(0, c/2, -(c/2))`. -/
example (c : ℝ) :
    let I := faceFlux (fun g : Fin 6 => Set.Icc (g.val : ℝ) (g.val + 1 / 2) ×ˢ Set.Icc (0 : ℝ) 1)
      (fun g _ => equalOppositeFlux c g)
    electricalIncidence twoTerminalTail twoTerminalHead *ᵥ
        (fun e => portSign twoTerminalTail 0 e * I e) = ![0, c / 2, -(c / 2)] := by
  intro I
  have hflux : ∀ f, I f = equalOppositeFlux (c / 2) f := by
    intro f
    simp only [I]
    rw [faceFlux_of_const
      (fun g : Fin 6 => Set.Icc (g.val : ℝ) (g.val + 1 / 2) ×ˢ Set.Icc (0 : ℝ) 1)
      (fun g _ => equalOppositeFlux c g) f (equalOppositeFlux c f)
      (measurableSet_Icc.prod measurableSet_Icc) (fun _ _ => rfl)]
    simp only [Measure.real, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc]
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num),
      ENNReal.toReal_ofReal (by norm_num)]
    fin_cases f <;> simp [equalOppositeFlux] <;> ring
  have hi : (fun e => portSign twoTerminalTail 0 e * I e) = equalOppositeBranchCurrent (c / 2) := by
    funext e
    rw [hflux e]
    exact ((twoTerminal_equalOppositeFlux (c / 2)).2.1 e).symm
  rw [hi]
  exact (twoTerminal_equalOppositeFlux (c / 2)).2.2.1

/-- Accumulating charge on the six-face field data: an extra constant density `k` on face `2`
gives the face fluxes `(-c/2, c/2, k/2, 0, 0, 0)`, continuity holds at rate `-k/2`, and every
compatible injection equals `k/2` at the box node. -/
example (c k : ℝ) (j : Fin 3 → ℝ)
    (hKCL : electricalIncidence twoTerminalTail twoTerminalHead *ᵥ
      (fun e => portSign twoTerminalTail 0 e *
        faceFlux (fun g : Fin 6 => Set.Icc (g.val : ℝ) (g.val + 1 / 2) ×ˢ Set.Icc (0 : ℝ) 1)
          (fun g _ => (![-c, c, k, 0, 0, 0] : Fin 6 → ℝ) g) e) = j) :
    j 0 = k / 2 := by
  have hflux : ∀ f, faceFlux
      (fun g : Fin 6 => Set.Icc (g.val : ℝ) (g.val + 1 / 2) ×ˢ Set.Icc (0 : ℝ) 1)
      (fun g _ => (![-c, c, k, 0, 0, 0] : Fin 6 → ℝ) g) f =
        1 / 2 * (![-c, c, k, 0, 0, 0] : Fin 6 → ℝ) f := by
    intro f
    rw [faceFlux_of_const
      (fun g : Fin 6 => Set.Icc (g.val : ℝ) (g.val + 1 / 2) ×ˢ Set.Icc (0 : ℝ) 1)
      (fun g _ => (![-c, c, k, 0, 0, 0] : Fin 6 → ℝ) g) f ((![-c, c, k, 0, 0, 0] : Fin 6 → ℝ) f)
      (measurableSet_Icc.prod measurableSet_Icc) (fun _ _ => rfl)]
    simp only [Measure.real, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc]
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num),
      ENNReal.toReal_ofReal (by norm_num)]
    ring
  have hcont : chargeContinuity
      (faceFlux (fun g : Fin 6 => Set.Icc (g.val : ℝ) (g.val + 1 / 2) ×ˢ Set.Icc (0 : ℝ) 1)
        (fun g _ => (![-c, c, k, 0, 0, 0] : Fin 6 → ℝ) g)) (-(k / 2)) := by
    simp only [chargeContinuity, hflux, Fin.sum_univ_six]
    simp
    ring
  have h := injection_box_eq_neg_chargeRate _ _ _ _ (fun _ => rfl) hcont
    twoTerminalTail twoTerminalHead 0 id _ j (twoTerminal_equalOppositeFlux c).1
    (fun _ => rfl) hKCL
  rw [h, neg_neg]

/-- Reversing face `0`'s port sign on the six-face field data at `c = 3` makes the box
outflow `-2 * (-3/2) = 3`, not zero. -/
example :
    let I := faceFlux (fun g : Fin 6 => Set.Icc (g.val : ℝ) (g.val + 1 / 2) ×ˢ Set.Icc (0 : ℝ) 1)
      (fun g _ => equalOppositeFlux 3 g)
    let i : Fin 6 → ℝ := fun e => portSign twoTerminalTail 0 e * I e
    (electricalIncidence twoTerminalTail twoTerminalHead *ᵥ Function.update i 0 (-i 0)) 0 = 3 ∧
      (electricalIncidence twoTerminalTail twoTerminalHead *ᵥ Function.update i 0 (-i 0)) 0 ≠
        0 := by
  intro I i
  have hflux : ∀ f, I f = 1 / 2 * equalOppositeFlux 3 f := by
    intro f
    simp only [I]
    rw [faceFlux_of_const
      (fun g : Fin 6 => Set.Icc (g.val : ℝ) (g.val + 1 / 2) ×ˢ Set.Icc (0 : ℝ) 1)
      (fun g _ => equalOppositeFlux 3 g) f (equalOppositeFlux 3 f)
      (measurableSet_Icc.prod measurableSet_Icc) (fun _ _ => rfl)]
    simp only [Measure.real, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc]
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num),
      ENNReal.toReal_ofReal (by norm_num)]
    ring
  have hsum : ∑ f : Fin 6, I f = 0 := by
    simp only [hflux, Fin.sum_univ_six, equalOppositeFlux]
    simp
  have hI0 : I 0 ≠ 0 := by
    rw [hflux]
    simp [equalOppositeFlux]
  obtain ⟨h1, h2⟩ := reversedPortSign_breaks_injection twoTerminalTail twoTerminalHead 0 id I i
    (twoTerminal_equalOppositeFlux 3).1 (fun _ => rfl) hsum 0 hI0
  have h3 : -2 * I 0 = 3 := by
    rw [hflux]
    norm_num [equalOppositeFlux]
  exact ⟨h1.trans h3, h2⟩

/-- Two terminals with equal opposite flux `3`: current balance gives the injection
`(0, 3, -3)`, and the unconverted current gives `-6` at the box. -/
example :
    electricalIncidence twoTerminalTail twoTerminalHead *ᵥ equalOppositeBranchCurrent 3 =
        ![0, 3, -3] ∧
      (electricalIncidence twoTerminalTail twoTerminalHead *ᵥ equalOppositeFlux 3) 0 = -6 := by
  obtain ⟨-, -, h1, h2⟩ := twoTerminal_equalOppositeFlux 3
  exact ⟨h1, by rw [h2]; norm_num⟩

end PhyslibExtTest.Circuits.FluxPortSignBridge
