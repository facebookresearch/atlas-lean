/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Elasticity.PrismaticMembers
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Tests for `PhyslibExt.Elasticity.PrismaticMembers`

* a nonzero uniform axial load with exact endpoint values;
* the uniform-load displacement as a fixed-fixed solution at concrete data;
* a fixed-free displacement at concrete data, which is not a fixed-fixed solution;
* the fixed-traction bar `EA = 2`, `L = 3`, `P = 6`, `q = 4`: the constructed solution, its end
  displacement, the internal axial force at the fixed end from the load path, the support
  reaction there, which balances the loads, and the same data read as a shaft;
* two free ends: an incompatible net load and a rigid translation;
* the thin closed rectangular cell: a nonzero torque and its reversal at SI data, an open wall
  whose resultants are not a couple, and a zero thickness, whose torsion constant vanishes, so that
  no twist rate carries the cell torque;
* the simply supported beam `EI = 2`, `L = 4`, `q = 3`: equal support reactions `6`, the slopes
  `± 4` at the pins, the midspan deflection `5` of every solution, the fixed-end polynomial with
  midspan deflection `1`, which is not a simply supported solution, and no solution on a span of
  length `0`.
-/

@[expose] public section

namespace PhyslibExtTest.Elasticity.PrismaticMembers

open _root_.Elasticity.PrismaticMembers

/-! ## A. Uniform axial load -/

-- Nonzero uniform axial load `q = 4`, `EA = 2`, `L = 2`: the displacement is `x * (2 - x)`,
-- exactly `0` at both ends and `1` at midspan.
example :
    axialDisplacement 2 2 4 0 = 0 ∧ axialDisplacement 2 2 4 2 = 0 ∧
      axialDisplacement 2 2 4 1 = 1 := by
  unfold axialDisplacement
  norm_num

-- The same data give a solution of the fixed-fixed bar problem.
example : IsFixedFixedSolution 2 2 (fun _ => 4) (axialDisplacement 2 2 4) :=
  isFixedFixedSolution_axialDisplacement (by norm_num) (by norm_num) 4

/-! ## B. Traction-free end -/

-- With the right end traction-free instead of fixed, the displacement `4 * x * (4 - x) / 4`
-- is not a fixed-fixed solution.
example : ¬ IsFixedFixedSolution 2 2 (fun _ => 4) (fixedFreeDisplacement 2 2 4) :=
  (fixedFreeDisplacement_not_isFixedFixedSolution (by norm_num) (by norm_num)
    (by norm_num)).2.2.2

/-! ## C. Clamped-free cantilever -/

-- Tip-force fixture `EI = 2`, `L = 3`, `q = 0`, `P = 4`: tip deflection
-- `P * L ^ 3 / (3 * EI) = 18`.
example : cantileverDeflection 2 3 0 4 3 = 18 := by
  unfold cantileverDeflection
  norm_num

-- Nonzero-load fixture `EI = 2`, `L = 3`, `q = 4`, `P = 5`: all four boundary conditions and
-- the equation hold, and the tip deflection is `q * L ^ 4 / (8 * EI) + P * L ^ 3 / (3 * EI)`
-- `= 81 / 4 + 45 / 2 = 171 / 4`.
example :
    cantileverDeflection 2 3 4 5 0 = 0 ∧ deriv (cantileverDeflection 2 3 4 5) 0 = 0 ∧
      2 * iteratedDeriv 2 (cantileverDeflection 2 3 4 5) 3 = 0 ∧
      -(2 * iteratedDeriv 3 (cantileverDeflection 2 3 4 5) 3) = 5 ∧
      (∀ x : ℝ, 2 * iteratedDeriv 4 (cantileverDeflection 2 3 4 5) x = 4) ∧
      cantileverDeflection 2 3 4 5 3 = 171 / 4 := by
  refine ⟨cantileverDeflection_zero 2 3 4 5, deriv_cantileverDeflection_zero 2 3 4 5,
    cantileverDeflection_moment_right 2 3 4 5,
    cantileverDeflection_shear_right (by norm_num) 3 4 5,
    fun x => cantileverDeflection_iteratedDeriv_four (by norm_num) 3 4 5 x, ?_⟩
  unfold cantileverDeflection
  norm_num

/-! ## D. Positive cantilever span -/

-- At the positive span `L = 3` the polynomial solves the cantilever problem.
example : IsCantileverSolution 2 3 4 5 (cantileverDeflection 2 3 4 5) :=
  isCantileverSolution_cantileverDeflection (by norm_num) (by norm_num) 4 5

-- A nonpositive span admits no cantilever solution: the model requires `0 < L`.
example (w : ℝ → ℝ) : ¬ IsCantileverSolution 2 (-3) 4 5 w := fun h => by
  have h' := h.span_pos
  norm_num at h'

example (w : ℝ → ℝ) : ¬ IsCantileverSolution 2 0 4 5 w := fun h => lt_irrefl _ h.span_pos

/-! ## E. Fixed-traction bar and shaft -/

-- Nonzero fixture `EA = 2`, `L = 3`, `P = 6`, `q = 4`: the constructed displacement solves the
-- problem, the end displacement is `P * L / EA + q * L ^ 2 / (2 * EA) = 9 + 9 = 18`, and the
-- internal axial force at the fixed end is `EA * u' 0 = P + q * L = 18` (tension).
example :
    IsFixedTractionSolution 2 3 6 (fun _ => 4) (fixedTractionDisplacement 2 3 6 fun _ => 4) ∧
      fixedTractionDisplacement 2 3 6 (fun _ => 4) 3 = 18 ∧
      2 * derivWithin (fixedTractionDisplacement 2 3 6 fun _ => 4) (Set.Icc 0 3) 0 = 18 := by
  have hL : (0 : ℝ) < 3 := by norm_num
  have hk : (2 : ℝ) ≠ 0 := by norm_num
  have hf : ContinuousOn (fun _ : ℝ => (4 : ℝ)) (Set.Icc 0 3) := continuousOn_const
  have hsol : IsFixedTractionSolution 2 3 6 (fun _ => (4 : ℝ))
      (fixedTractionDisplacement 2 3 6 fun _ => 4) :=
    isFixedTractionSolution_fixedTractionDisplacement hL hk hf
  refine ⟨hsol, ?_, ?_⟩
  · have hconst := fixedTractionDisplacement_const 2 3 6 4 3
    rw [hconst]
    show (6 : ℝ) * 3 / 2 + 4 * 3 * (2 * 3 - 3) / (2 * 2) = 18
    norm_num
  · have hDu : derivWithin (fixedTractionDisplacement 2 3 6 fun _ => (4 : ℝ)) (Set.Icc 0 3)
        0 =
        fixedTractionStrain 2 3 6 (fun _ => (4 : ℝ)) 0 :=
      derivWithin_fixedTractionDisplacement hL hf 0 ⟨le_rfl, by norm_num⟩
    rw [hDu]
    show (2 : ℝ) * ((6 + ∫ y in (0 : ℝ)..3, (fun _ => (4 : ℝ)) y) / 2) = 18
    rw [intervalIntegral.integral_const, smul_eq_mul]
    norm_num

-- In every solution of the fixed-traction bar `EA = 2`, `L = 3`, `P = 6`, `q = 4` the internal
-- axial force at the fixed end is `EA * u' 0 = P + q * L = 18` (tension), by the load path.
example (u : ℝ → ℝ) (hu : IsFixedTractionSolution 2 3 6 (fun _ => 4) u) :
    2 * derivWithin u (Set.Icc 0 3) 0 = 18 := by
  rw [hu.axialForce_eq 0 ⟨le_rfl, by norm_num⟩, intervalIntegral.integral_const, smul_eq_mul]
  norm_num

-- The support reaction at the fixed end: the outward normal there is `-x` (the end-force
-- convention of `IsFreeFreeSolution`), so the force the support exerts on the bar along `+x` is
-- `-(EA * u' 0) = -18`, and it balances the end force `P = 6` and the distributed load
-- `q * L = 12`.
example (u : ℝ → ℝ) (hu : IsFixedTractionSolution 2 3 6 (fun _ => 4) u) :
    -(2 * derivWithin u (Set.Icc 0 3) 0) = -18 ∧
      -(2 * derivWithin u (Set.Icc 0 3) 0) + 6 + 4 * 3 = 0 := by
  have h := hu.axialForce_eq 0 ⟨le_rfl, by norm_num⟩
  rw [intervalIntegral.integral_const, smul_eq_mul] at h
  constructor <;> linarith

-- A circular shaft with `GJ = 2`, `L = 3`, end torque `T = 6` and uniform distributed torque
-- `t = 4`: every twist solution has the end twist `T * L / GJ + t * L ^ 2 / (2 * GJ) = 18`.
example (φ : ℝ → ℝ) (hφ : IsFixedTractionSolution 2 3 6 (fun _ => 4) φ) : φ 3 = 18 := by
  rw [(hφ.twist (by norm_num)).1 ⟨by norm_num, le_rfl⟩, fixedTractionDisplacement_const]
  unfold fixedFreeDisplacement
  norm_num

-- Two free ends: a free-free solution shifted by a constant is again a free-free solution.
example (u : ℝ → ℝ) (hu : IsFreeFreeSolution 2 3 1 (-1) (fun _ => 0) u) (c : ℝ) :
    IsFreeFreeSolution 2 3 1 (-1) (fun _ => 0) (fun x => u x + c) :=
  hu.add_const c

/-! ## F. Two free ends -/

-- Incompatible net load: a unit bar with unit distributed load and unloaded ends has no
-- free-free solution, while the unloaded free-free bar admits the nonzero translation `u = 1`,
-- which violates the fixed-end condition `u 0 = 0`.
example (k : ℝ) :
    (∀ u : ℝ → ℝ, ¬ IsFreeFreeSolution k 1 0 0 (fun _ => 1) u) ∧
      IsFreeFreeSolution k 1 0 0 (fun _ => 0) (fun _ => 1) := by
  constructor
  · intro u hu
    have hL : (0 : ℝ) < 1 := by norm_num
    have hnet := hu.net_load hL
    have hint : (∫ x in (0 : ℝ)..(1 : ℝ), (fun _ => (1 : ℝ)) x) = 1 := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      norm_num
    rw [hint] at hnet
    norm_num at hnet
  · refine ⟨contDiffOn_const, ?_, ?_, ?_⟩
    · intro x hx
      have hiter : iteratedDerivWithin 2 (fun _ : ℝ => (1 : ℝ)) (Set.Icc 0 1) x = 0 := by
        rw [iteratedDerivWithin_const]
        simp
      rw [hiter]
      simp
    · have hd0 : derivWithin (fun _ : ℝ => (1 : ℝ)) (Set.Icc 0 1) 0 = 0 :=
        congrFun (derivWithin_fun_const (Set.Icc 0 1) 1) 0
      rw [hd0]
      simp
    · have hdL : derivWithin (fun _ : ℝ => (1 : ℝ)) (Set.Icc 0 1) 1 = 0 :=
        congrFun (derivWithin_fun_const (Set.Icc 0 1) 1) 1
      rw [hdL]
      simp

/-! ## G. Thin closed rectangular cell -/

section ClosedCell

open Mechanics.EngineeringStatics (momentAbout)
open PhyslibExt.Mechanics.HarmonicMechanics (resultantForce)

/-- Nonzero torque and its reversal, in SI units: a cell of median sides `a = 0.2 m`, `b = 0.1 m`,
thickness `t = 0.005 m` and `G = 80 GPa` with the shear flow `q = 25 kN/m` carries
`T = 1000 N m`; reversing the flow reverses the torque. The wall shear stress is `τ = 5 MPa`, and
the twist rate `θ' = 15 / 16000 rad/m` satisfies the compatibility law. -/
lemma fixture_cell_torque_reversal :
    momentAbout (cellWallMidpoint (1 / 5) (1 / 10)) (cellWallForce (1 / 5) (1 / 10) 25000)
        (fun _ => 0) 0 = ![0, 0, 1000] ∧
      momentAbout (cellWallMidpoint (1 / 5) (1 / 10)) (cellWallForce (1 / 5) (1 / 10) (-25000))
        (fun _ => 0) 0 = ![0, 0, -1000] ∧
      wallShearStress 25000 (1 / 200) = 5000000 ∧
      IsClosedCellCompatible (1 / 5) (1 / 10) (1 / 200) 80000000000 25000 (15 / 16000) := by
  rw [momentAbout_cellWall, momentAbout_cellWall]
  norm_num
  unfold wallShearStress IsClosedCellCompatible cellWallLength
  rw [Fin.sum_univ_four]
  norm_num

/-- The shear-stress lemma at the same cell: with the wall thickness `t = 0.005 m > 0` and the
torque `T = 1000 N m` of the wall resultants, `τ = T / (2 a b t) = 1000 / 0.0002 = 5 MPa`, the value
`q / t` above. -/
example : wallShearStress 25000 (1 / 200) = 1000 / (2 * (1 / 5) * (1 / 10) * (1 / 200)) ∧
    (1000 : ℝ) / (2 * (1 / 5) * (1 / 10) * (1 / 200)) = 5000000 := by
  refine ⟨wallShearStress_eq (a := 1 / 5) (b := 1 / 10) (O := 0) (by norm_num) (by norm_num)
    (by norm_num) ?_, by norm_num⟩
  rw [momentAbout_cellWall]
  norm_num

/-- **An open wall breaks the closed cell.** With the left wall cut, the three remaining wall
resultants of a nonzero shear flow have the nonzero sum `(0, q b, 0)`, so they are not a couple:
their moment depends on the reference point, and no single torque `2 a b q` is carried. -/
lemma openCell_not_couple {a b q : ℝ} (hb : b ≠ 0) (hq : q ≠ 0) :
    resultantForce (fun i : Fin 3 => cellWallForce a b q i.castSucc) ≠ 0 ∧
      ∃ O O' : Fin 3 → ℝ,
        momentAbout (fun i : Fin 3 => cellWallMidpoint a b i.castSucc)
            (fun i : Fin 3 => cellWallForce a b q i.castSucc) (fun _ => 0) O ≠
          momentAbout (fun i : Fin 3 => cellWallMidpoint a b i.castSucc)
            (fun i : Fin 3 => cellWallForce a b q i.castSucc) (fun _ => 0) O' := by
  constructor
  · unfold resultantForce cellWallForce
    rw [Fin.sum_univ_three]
    simp [hq, hb]
  · refine ⟨0, ![1, 0, 0], ?_⟩
    intro h
    have h2 := congrFun h 2
    unfold momentAbout cellWallMidpoint cellWallForce at h2
    rw [Fin.sum_univ_three, Fin.sum_univ_three] at h2
    simp only [add_zero, Pi.sub_apply, cross_apply, Pi.zero_apply] at h2
    simp [hq, hb, eq_sub_iff_add_eq] at h2

/-- **A zero thickness is rejected.** A wall of zero thickness gives the torsion constant `J = 0`,
so for `a, b > 0` and `q ≠ 0` no twist rate reproduces the cell torque `2 a b q` through the
rigidity `G J`. -/
lemma zeroThickness_rejected {a b G q : ℝ} (ha : 0 < a) (hb : 0 < b) (hq : q ≠ 0) :
    closedCellTorsionConstant a b 0 = 0 ∧
      ∀ θ' : ℝ, 2 * a * b * q ≠ G * closedCellTorsionConstant a b 0 * θ' := by
  constructor
  · unfold closedCellTorsionConstant
    simp
  · intro θ'
    unfold closedCellTorsionConstant
    simp [ne_of_gt ha, ne_of_gt hb, hq]

end ClosedCell

/-! ## H. Simply supported beam -/

open _root_.Mechanics.EulerBernoulli

-- Nonzero-load fixture `EI = 2`, `L = 4`, `q = 3`: equal support reactions `q * L / 2 = 6`,
-- which together carry the total load `q * L = 12`, and the midspan deflection
-- `5 * q * L ^ 4 / (384 * EI) = 5`.
example :
    -(2 * iteratedDeriv 3 (uniformLoadDeflection 3 2 4) 0) = 6 ∧
      2 * iteratedDeriv 3 (uniformLoadDeflection 3 2 4) 4 = 6 ∧
      uniformLoadDeflection 3 2 4 2 = 5 := by
  obtain ⟨h0, hL⟩ := (isSimplySupportedSolution_uniformLoadDeflection (EI := 2) (L := 4)
    (by norm_num) (by norm_num) 3).reactions (by norm_num)
  refine ⟨by rw [h0]; norm_num, by rw [hL]; norm_num, ?_⟩
  unfold uniformLoadDeflection
  norm_num

-- The same data: the pins leave the slopes free, `4` at the left pin and `-4` at the right.
example :
    deriv (uniformLoadDeflection 3 2 4) 0 = 4 ∧ deriv (uniformLoadDeflection 3 2 4) 4 = -4 := by
  obtain ⟨h0, hL⟩ := (isSimplySupportedSolution_uniformLoadDeflection (EI := 2) (L := 4)
    (by norm_num) (by norm_num) 3).slopes (by norm_num)
  exact ⟨by rw [h0]; norm_num, by rw [hL]; norm_num⟩

-- Uniqueness: every solution with these data has the midspan deflection `5`.
example (w : ℝ → ℝ) (hw : IsSimplySupportedSolution 2 4 3 w) : w 2 = 5 := by
  rw [hw.eqOn (by norm_num) ⟨by norm_num, by norm_num⟩]
  unfold uniformLoadDeflection
  norm_num

-- Clamped slopes instead of the moment conditions: the fixed-end polynomial is not a simply
-- supported solution, and its midspan deflection is `1`, not `5`.
example :
    ¬ IsSimplySupportedSolution 2 4 3 (clampedClampedDeflection 2 4 3) ∧
      clampedClampedDeflection 2 4 3 2 = 1 := by
  refine ⟨(clampedSlopes_change_solution (EI := 2) (L := 4) (q := 3) (by norm_num) (by norm_num)
    (by norm_num)).2.2.2.2.2.1, ?_⟩
  unfold clampedClampedDeflection
  norm_num

-- A span of length `0` admits no simply supported solution.
example (w : ℝ → ℝ) : ¬ IsSimplySupportedSolution 2 0 3 w := fun h => lt_irrefl _ h.span_pos

end PhyslibExtTest.Elasticity.PrismaticMembers

end
