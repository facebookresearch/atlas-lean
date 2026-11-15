/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Chemistry.Thermodynamics.FundamentalRelation

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!

# Tests for equilibrium postulates and the fundamental relation

The generic API exercised on the ideal-gas fundamental relation `idealGas`, mostly at
`(U, V, N) = (3/2, 1, 1)` with `kB = 1` and `s0 = 0`, where `T = 1`: the derived chain
rule against a direct derivative, the first law, the Euler relation, Gibbs-Duhem,
two-subsystem equilibrium and heat flow, and the boundary countermodel at `N = 0`.

-/

@[expose] public section

open Chemistry.Thermodynamics

open scoped Topology

namespace PhyslibExtTest.Chemistry.Thermodynamics

/-!

## A. Equilibrium states and the fundamental relation

-/

/-- The entropy of `idealGas` is the ideal-gas model `SidealGen`. -/
example (kB s0 : ℝ) (hkB : 0 < kB) : (idealGas kB s0 hkB).S = SidealGen kB s0 := rfl

/-- `temp_pos` on `idealGas`: the temperature at `(3/2, 1, 1)` is positive. -/
example : 0 < temp (idealGas 1 0 one_pos).S ((3 / 2, 1, fun _ => 1) : ThermoState 1) :=
  temp_pos _ _ ⟨by norm_num, one_pos, fun _ => one_pos⟩

/-- The ideal-gas entropy is strictly increasing in `U` at `V = N = 1`. -/
example : StrictMonoOn (fun u => (idealGas 1 0 one_pos).S (u, 1, fun _ => 1))
    (Set.Ioi 0) :=
  (idealGas 1 0 one_pos).strictMonoOn_energy one_pos fun _ => one_pos

/-- The derived chain rule on `idealGas` along the diagonal curve `t ↦ (t, t, 1)` at
`t = 1`: `∂S/∂U + ∂S/∂V = 3/2 + 1 = 5/2`. -/
example : HasDerivAt (fun t => (idealGas 1 0 one_pos).S (t, t, fun _ => 1)) (5 / 2) 1 := by
  have hx : ((1, 1, fun _ => 1) : ThermoState 1) ∈ thermoDomain 1 :=
    ⟨one_pos, one_pos, fun _ => one_pos⟩
  have h := hasDerivAt_comp_curve (γN := fun _ _ => 1) (hasDerivAt_id' (1 : ℝ))
    (hasDerivAt_id' (1 : ℝ)) (fun _ => hasDerivAt_const (1 : ℝ) (1 : ℝ))
    ((idealGas 1 0 one_pos).differentiableAt hx)
  have hU : dSdU (idealGas 1 0 one_pos).S ((1, 1, fun _ => 1) : ThermoState 1) = 3 / 2 := by
    rw [show (idealGas 1 0 one_pos).S = SidealGen 1 0 from rfl,
      sideal_dSdU 1 0 _ one_pos one_pos]
    norm_num
  have hV : dSdV (idealGas 1 0 one_pos).S ((1, 1, fun _ => 1) : ThermoState 1) = 1 := by
    rw [show (idealGas 1 0 one_pos).S = SidealGen 1 0 from rfl,
      sideal_dSdV 1 0 _ one_pos one_pos]
    norm_num
  rw [hU, hV] at h
  convert h using 1
  norm_num

/-- The same derivative by direct computation: along the diagonal the entropy is
`(5/2) * log t`, with derivative `5/2` at `t = 1`. -/
example : HasDerivAt (fun t => SidealGen 1 0 (t, t, fun _ => 1)) (5 / 2) 1 := by
  have h : HasDerivAt (fun t : ℝ => 5 / 2 * Real.log t) (5 / 2 * 1⁻¹) 1 :=
    (Real.hasDerivAt_log one_ne_zero).const_mul (5 / 2)
  have heq : (fun t => SidealGen 1 0 (t, t, fun _ => 1)) =
      fun t : ℝ => 5 / 2 * Real.log t := by
    funext t
    simp only [SidealGen, Sideal, div_one]
    ring
  rw [heq]
  simpa using h

/-!

## B. The first law and the Euler relation

-/

/-- The generic temperature of `idealGas` at `(3/2, 1, 1)` is `1`. -/
example : temp (idealGas 1 0 one_pos).S ((3 / 2, 1, fun _ => 1) : ThermoState 1) = 1 := by
  rw [show (idealGas 1 0 one_pos).S = SidealGen 1 0 from rfl,
    sideal_temp 1 0 _ (by norm_num) one_pos one_pos]
  norm_num

/-- The generic pressure of `idealGas` at `(3/2, 1, 1)` is `1`. -/
example : press (idealGas 1 0 one_pos).S ((3 / 2, 1, fun _ => 1) : ThermoState 1) = 1 := by
  rw [show (idealGas 1 0 one_pos).S = SidealGen 1 0 from rfl,
    sideal_press 1 0 _ (by norm_num) one_pos one_pos one_pos]
  norm_num

/-- First law for isochoric heating of `idealGas` at `(3/2, 1, 1)`: with `V` and `N`
fixed, `dU = T dS` and `T = 1` give `dS/dU = 1`. -/
example : deriv (fun t => (idealGas 1 0 one_pos).S (t, 1, fun _ => 1)) (3 / 2) = 1 := by
  have hT : temp (idealGas 1 0 one_pos).S ((3 / 2, 1, fun _ => 1) : ThermoState 1) = 1 := by
    rw [show (idealGas 1 0 one_pos).S = SidealGen 1 0 from rfl,
      sideal_temp 1 0 _ (by norm_num) one_pos one_pos]
    norm_num
  have h := firstLaw (idealGas 1 0 one_pos) (fun t => t) (fun _ => 1) (fun _ _ => 1)
    1 0 (fun _ => 0) (3 / 2) (hasDerivAt_id' _) (hasDerivAt_const _ _)
    (fun _ => hasDerivAt_const _ _) ⟨by norm_num, one_pos, fun _ => one_pos⟩
  simp only [mul_zero, Finset.sum_const_zero, sub_zero, add_zero] at h
  rw [hT, one_mul] at h
  exact h.symm

/-- The generic Euler relation for `idealGas`, with the closed forms of `T`, `p` and
`S` at `(3/2, 1, 1)`, determines the chemical potential `μ = 5/2 - (3/2) log (3/2)`. -/
example : chemPot (idealGas 1 0 one_pos).S ((3 / 2, 1, fun _ => 1) : ThermoState 1) 0 =
    5 / 2 - 3 / 2 * Real.log (3 / 2) := by
  have hx : ((3 / 2, 1, fun _ => 1) : ThermoState 1) ∈ thermoDomain 1 :=
    ⟨by norm_num, one_pos, fun _ => one_pos⟩
  have he := euler_relation (idealGas 1 0 one_pos) _ hx
  have hT : temp (idealGas 1 0 one_pos).S ((3 / 2, 1, fun _ => 1) : ThermoState 1) = 1 := by
    rw [show (idealGas 1 0 one_pos).S = SidealGen 1 0 from rfl,
      sideal_temp 1 0 _ (by norm_num) one_pos one_pos]
    norm_num
  have hp : press (idealGas 1 0 one_pos).S ((3 / 2, 1, fun _ => 1) : ThermoState 1) = 1 := by
    rw [show (idealGas 1 0 one_pos).S = SidealGen 1 0 from rfl,
      sideal_press 1 0 _ (by norm_num) one_pos one_pos one_pos]
    norm_num
  have hS : (idealGas 1 0 one_pos).S ((3 / 2, 1, fun _ => 1) : ThermoState 1) =
      3 / 2 * Real.log (3 / 2) := by
    change Sideal 1 0 (3 / 2) 1 1 = _
    simp only [Sideal, div_one, Real.log_one]
    ring
  rw [Fin.sum_univ_one, hT, hp, hS] at he
  change (3 / 2 : ℝ) = 1 * (3 / 2 * Real.log (3 / 2)) - 1 * 1 +
    chemPot (idealGas 1 0 one_pos).S ((3 / 2, 1, fun _ => 1) : ThermoState 1) 0 * 1 at he
  linarith

/-- The closed form `sideal_mu` gives the same chemical potential. -/
example : chemPot (SidealGen 1 0) ((3 / 2, 1, fun _ => 1) : ThermoState 1) 0 =
    5 / 2 - 3 / 2 * Real.log (3 / 2) := by
  rw [sideal_mu 1 0 _ 0 (by norm_num) one_pos one_pos one_pos]
  change -(2 * (3 / 2) / (3 * 1)) *
      (Real.log (1 / 1) + 3 / 2 * Real.log (3 / 2 / 1) + 0 - 5 / 2) = _
  simp only [div_one, Real.log_one]
  ring

/-!

## C. Gibbs-Duhem

Isochoric heating `t ↦ (t, 1, 1)` at `t = 3/2`, where `T = p = 2t/3` and
`μ = -(2t/3) ((3/2) log t - 5/2)`.

-/

/-- The generic `gibbsDuhem` on `idealGas`: with the derivatives `T' = p' = 2/3` and
`μ' = 2/3 - log (3/2)` of the closed forms, `S T' - V p' + N μ' = 0`. -/
example : SidealGen 1 0 ((3 / 2, 1, fun _ => 1) : ThermoState 1) * (2 / 3) - 1 * (2 / 3) +
    ∑ _i : Fin 1, (1 : ℝ) * (2 / 3 - Real.log (3 / 2)) = 0 := by
  have hx : ((3 / 2, 1, fun _ => 1) : ThermoState 1) ∈ thermoDomain 1 :=
    ⟨by norm_num, one_pos, fun _ => one_pos⟩
  have hev : ∀ᶠ t in 𝓝 (3 / 2 : ℝ), ((t, 1, fun _ => 1) : ThermoState 1) ∈ thermoDomain 1 :=
    (eventually_gt_nhds (by norm_num : (0 : ℝ) < 3 / 2)).mono fun t ht =>
      ⟨ht, one_pos, fun _ => one_pos⟩
  have hT : HasDerivAt (fun t => temp (idealGas 1 0 one_pos).S (t, 1, fun _ => 1))
      (2 / 3) (3 / 2) := by
    have h : HasDerivAt (fun t : ℝ => 2 * t / (3 * 1 * 1)) (2 * 1 / (3 * 1 * 1)) (3 / 2) :=
      ((hasDerivAt_id' _).const_mul 2).div_const _
    refine (h.congr_of_eventuallyEq ?_).congr_deriv (by norm_num)
    exact hev.mono fun t ht => sideal_temp 1 0 _ ht.1 (ht.2.2 0) one_pos
  have hp : HasDerivAt (fun t => press (idealGas 1 0 one_pos).S (t, 1, fun _ => 1))
      (2 / 3) (3 / 2) := by
    have h : HasDerivAt (fun t : ℝ => 2 * t / (3 * 1)) (2 * 1 / (3 * 1)) (3 / 2) :=
      ((hasDerivAt_id' _).const_mul 2).div_const _
    refine (h.congr_of_eventuallyEq ?_).congr_deriv (by norm_num)
    exact hev.mono fun t ht => sideal_press 1 0 _ ht.1 ht.2.1 (ht.2.2 0) one_pos
  have hmu : ∀ i, HasDerivAt
      (fun t => chemPot (idealGas 1 0 one_pos).S (t, 1, fun _ => 1) i)
      (2 / 3 - Real.log (3 / 2)) (3 / 2) := by
    intro i
    have hf : HasDerivAt (fun t : ℝ => -(2 * t / (3 * 1))) (-(2 * 1 / (3 * 1))) (3 / 2) :=
      (((hasDerivAt_id' _).const_mul 2).div_const _).neg
    have hl : HasDerivAt (fun t : ℝ => Real.log (t / 1)) ((1 / 1) / (3 / 2 / 1)) (3 / 2) :=
      ((hasDerivAt_id' _).div_const 1).log (by norm_num)
    have hg : HasDerivAt
        (fun t : ℝ => Real.log (1 / 1) + 3 / 2 * Real.log (t / 1) + 0 - 5 / 2)
        (0 + 3 / 2 * ((1 / 1) / (3 / 2 / 1)) + 0 - 0) (3 / 2) :=
      (((hasDerivAt_const _ _).add (hl.const_mul (3 / 2))).add
        (hasDerivAt_const _ _)).sub (hasDerivAt_const _ _)
    refine ((hf.mul hg).congr_of_eventuallyEq ?_).congr_deriv ?_
    · exact hev.mono fun t ht => sideal_mu 1 0 _ i ht.1 ht.2.1 (ht.2.2 0) one_pos
    · simp only [div_one, Real.log_one]
      ring
  exact gibbsDuhem (idealGas 1 0 one_pos) (fun t => t) (fun _ => 1) (fun _ _ => 1)
    1 0 (2 / 3) (2 / 3) (fun _ => 0) (fun _ => 2 / 3 - Real.log (3 / 2)) (3 / 2)
    (hasDerivAt_id' _) (hasDerivAt_const _ _) (fun _ => hasDerivAt_const _ _) hx hev
    hT hp hmu

/-- `sideal_gibbsDuhem` along the same curve, with no derivative hypotheses on
`T`, `p` or `μ`. -/
example : SidealGen 1 0 ((3 / 2, 1, fun _ => 1) : ThermoState 1) *
      deriv (fun t => temp (SidealGen 1 0) (t, 1, fun _ => 1)) (3 / 2) -
    1 * deriv (fun t => press (SidealGen 1 0) (t, 1, fun _ => 1)) (3 / 2) +
    ∑ i : Fin 1, 1 *
      deriv (fun t => chemPot (SidealGen 1 0) (t, 1, fun _ => 1) i) (3 / 2) = 0 :=
  sideal_gibbsDuhem 1 0 (fun t => t) (fun _ => 1) (fun _ _ => 1) 1 0 (fun _ => 0)
    (3 / 2) one_pos (hasDerivAt_id' _) (hasDerivAt_const _ _)
    (fun _ => hasDerivAt_const _ _) (by norm_num) one_pos one_pos
    (eventually_gt_nhds (by norm_num)) (Filter.Eventually.of_forall fun _ => one_pos)
    (Filter.Eventually.of_forall fun _ => one_pos)

/-!

## D. Entropy maximum and heat flow

Two ideal-gas subsystems with `V₁ = V₂ = 1`, `N₁ = N₂ = 1`, `kB = 1` and total energy
`Utot = 3`.

-/

/-- With `s0 = 0` for both, the total-entropy rate vanishes at `U₁ = 3 / 2`. -/
example : deriv
    (fun U1 => Sideal 1 0 U1 1 1 + Sideal 1 0 (3 - U1) 1 1) (3 / 2) = 0 := by
  have h := sideal_stot_hasDerivAt 1 0 1 1 1 1 3 (3 / 2) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  rw [h.deriv]
  norm_num

/-- Both subsystem temperatures equal `1` at `U₁ = 3 / 2`. -/
example : temp (SidealGen 1 0) ((3 / 2, 1, fun _ => 1) : ThermoState 1) =
    temp (SidealGen 1 0) ((3 - 3 / 2, 1, fun _ => 1) : ThermoState 1) := by
  rw [sideal_temp 1 0 _ (by norm_num) one_pos one_pos,
    sideal_temp 1 0 _ (by norm_num) one_pos one_pos]
  norm_num

/-- `entropyFlow_sign` on two ideal-gas subsystems at `U₁ = 2`, `U₂ = 1`:
`T₁ = 4/3 > T₂ = 2/3`, so moving energy from 1 to 2 raises the total entropy. -/
example : deriv (fun U1 => (idealGas 1 0 one_pos).S (U1, 1, fun _ => 1) +
    (idealGas 1 0 one_pos).S (3 - U1, 1, fun _ => 1)) 2 < 0 := by
  have hx1 : ((2, 1, fun _ => 1) : ThermoState 1) ∈ thermoDomain 1 :=
    ⟨by norm_num, one_pos, fun _ => one_pos⟩
  have hx2 : ((3 - 2, 1, fun _ => 1) : ThermoState 1) ∈ thermoDomain 1 :=
    ⟨by norm_num, one_pos, fun _ => one_pos⟩
  refine entropyFlow_sign (idealGas 1 0 one_pos) 1 1 3 2
    (fun _ => 1) (fun _ => 1) hx1 hx2 ?_
  rw [show (idealGas 1 0 one_pos).S = SidealGen 1 0 from rfl,
    sideal_temp 1 0 _ (by norm_num) one_pos one_pos,
    sideal_temp 1 0 _ (by norm_num) one_pos one_pos]
  norm_num

/-- General maximum principle for a two-species fundamental relation: at an interior
local maximizer of total entropy the two subsystem temperatures agree. -/
example (F : FundamentalRelation 2)
    (V1 V2 Utot Ustar : ℝ) (N1 N2 : Fin 2 → ℝ)
    (hx1 : (Ustar, V1, N1) ∈ thermoDomain 2)
    (hx2 : (Utot - Ustar, V2, N2) ∈ thermoDomain 2)
    (hmax : IsLocalMax
      (fun U1 => F.S (U1, V1, N1) + F.S (Utot - U1, V2, N2)) Ustar) :
    temp F.S (Ustar, V1, N1) = temp F.S (Utot - Ustar, V2, N2) :=
  entropyMax_temperature_eq F V1 V2 Utot Ustar N1 N2 hx1 hx2 hmax

/-!

## E. The ideal gas

-/

/-- On the physical domain the ideal-gas entropy agrees with Physlib's `entropy` at
`c = 3/2`: here at `U = V = N = 1`, `kB = 2`, `s0 = 5`, both are `10`. -/
example : Sideal 2 5 1 1 1 = _root_.entropy (3 / 2) 2 (2 * 5) 1 1 1 1 1 1 ∧
    Sideal 2 5 1 1 1 = 10 := by
  refine ⟨sideal_eq_entropy 2 5 1 1 1 one_pos one_pos one_pos, ?_⟩
  norm_num [Sideal]

/-- At `(U, V, N) = (3/2, 1, 1)` with `kB = 1`, `T = 1`. -/
example : temp (SidealGen 1 0) ((3 / 2, 1, fun _ => 1) : ThermoState 1) = 1 := by
  have hU : (0 : ℝ) < ((3 / 2, 1, fun _ => 1) : ThermoState 1).1 := by
    change (0 : ℝ) < 3 / 2
    norm_num
  have hN : (0 : ℝ) < ((3 / 2, 1, fun _ => 1) : ThermoState 1).2.2 0 := by
    change (0 : ℝ) < 1
    norm_num
  rw [sideal_temp 1 0 _ hU hN (by norm_num)]
  change 2 * (3 / 2) / (3 * 1 * 1) = 1
  norm_num

/-- `p * V = N * kB * T` at the numeric point: both sides equal `1`. -/
example : press (SidealGen 1 0) ((3 / 2, 1, fun _ => 1) : ThermoState 1) * 1 =
    1 * 1 * temp (SidealGen 1 0) ((3 / 2, 1, fun _ => 1) : ThermoState 1) := by
  have hU : (0 : ℝ) < ((3 / 2, 1, fun _ => 1) : ThermoState 1).1 := by
    change (0 : ℝ) < 3 / 2
    norm_num
  have hV : (0 : ℝ) < ((3 / 2, 1, fun _ => 1) : ThermoState 1).2.1 := by
    change (0 : ℝ) < 1
    norm_num
  have hN : (0 : ℝ) < ((3 / 2, 1, fun _ => 1) : ThermoState 1).2.2 0 := by
    change (0 : ℝ) < 1
    norm_num
  exact sideal_pV 1 0 _ hU hV hN (by norm_num)

/-- `U = (3/2) * N * kB * T` at the numeric point. -/
example : (3 / 2 : ℝ) =
    3 / 2 * 1 * 1 * temp (SidealGen 1 0) ((3 / 2, 1, fun _ => 1) : ThermoState 1) := by
  have hU : (0 : ℝ) < ((3 / 2, 1, fun _ => 1) : ThermoState 1).1 := by
    change (0 : ℝ) < 3 / 2
    norm_num
  have hN : (0 : ℝ) < ((3 / 2, 1, fun _ => 1) : ThermoState 1).2.2 0 := by
    change (0 : ℝ) < 1
    norm_num
  exact sideal_U 1 0 _ hU hN (by norm_num)

/-- The entropy value at the numeric point is `(3/2) * log (3/2)`. -/
example : Sideal 1 0 (3 / 2) 1 1 = 3 / 2 * Real.log (3 / 2) := by
  simp only [Sideal, div_one, Real.log_one]
  ring

/-- The ideal-gas entropy is concave on its domain (for `kB = 1 ≥ 0`). -/
example : ConcaveOn ℝ sidealDomain
    (fun x : ℝ × ℝ × ℝ => Sideal 1 0 x.1 x.2.1 x.2.2) :=
  sideal_concave 1 0 (by norm_num)

/-- At `N = 0` the `∂S/∂U` postulate fails: the slice derivative is `0`. -/
example : dSdU (SidealGen 1 0) ((1, 1, fun _ => 0) : ThermoState 1) = 0 :=
  sideal_dSdU_at_N_zero 1 0 1 1

/-- At `(U, V, N) = (1, 1, 0)` the caloric equation of state fails, so `sideal_U`
needs `0 < N`. -/
example : ¬ (1 : ℝ) =
    3 / 2 * (0 : ℝ) * 1 * temp (SidealGen 1 0) ((1, 1, fun _ => 0) : ThermoState 1) :=
  sideal_EOS_fails_at_N_zero 0

end PhyslibExtTest.Chemistry.Thermodynamics
