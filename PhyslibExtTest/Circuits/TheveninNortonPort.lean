/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Circuits.TheveninNortonPort
public import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

@[expose] public section

open Matrix PhyslibExt.Circuits.TheveninNortonPort

namespace PhyslibExtTest.Circuits.TheveninNortonPort

/-! ### Thevenin and Norton relations on `K = 2`, `jEff = 4` -/

/-- The Thevenin parameters are `Vth = 2` and `Rth = 1/2`. -/
example : theveninVoltage 2 4 = 2 ∧ theveninResistance 2 = 1 / 2 := by
  norm_num [theveninVoltage, theveninResistance]

/-- The operating point `V = 1`, `I = 2` satisfies the law, hence the
Thevenin form `1 = Vth - Rth * 2`. -/
example : (1 : ℝ) = theveninVoltage 2 4 - theveninResistance 2 * 2 :=
  (onePort_iff_thevenin 2 4 1 2 (by norm_num)).mp (by norm_num)

/-- The Thevenin form at `V = 1` forces the load current `I = 2`. -/
example (I : ℝ) (h : (1 : ℝ) = theveninVoltage 2 4 - theveninResistance 2 * I) :
    I = 2 := by
  have hlaw := (onePort_iff_thevenin 2 4 1 I (by norm_num)).mpr h
  linarith

/-- The Norton form at `V = 1` gives the load current `4 - 2 = 2`. -/
example (I : ℝ) (h : 2 * (1 : ℝ) = 4 - I) : I = 2 := by
  rw [(onePort_iff_norton 2 4 1 I).mp h]
  norm_num

/-- Open circuit gives the Thevenin voltage `2`. -/
example (V : ℝ) (h : 2 * V = 4 - 0) : V = 2 := by
  rw [onePort_openCircuit 2 4 V (by norm_num) h]
  norm_num [theveninVoltage]

/-! ### Short circuit -/

/-- Short circuit: zero port voltage and the Norton current `4`. -/
example (V I : ℝ) (hlaw : 2 * V = 4 - I) (hload : V = 0 * I) : V = 0 ∧ I = 4 :=
  onePort_shortCircuit 2 4 V I (by norm_num) hlaw hload

/-- The short is the `RL = 0` case of the divider: the load current is
`Vth / Rth = jEff`. -/
example (V I : ℝ) (hlaw : 2 * V = 4 - I) (hload : V = 0 * I) :
    I = theveninVoltage 2 4 / theveninResistance 2 := by
  have h := (onePort_resistiveLoad 2 4 0 V I (by norm_num) le_rfl hlaw hload).2
  rw [h, add_zero]

/-! ### Resistive load and the headline -/

/-- A load `RL = 3/2` gives the divider voltage `3/2` and current `1`. -/
example (V I : ℝ) (hlaw : 2 * V = 4 - I) (hload : V = 3 / 2 * I) :
    V = 3 / 2 ∧ I = 1 := by
  obtain ⟨hV, hI⟩ := onePort_resistiveLoad 2 4 (3 / 2) V I (by norm_num) (by norm_num)
    hlaw hload
  rw [hV, hI]
  norm_num [theveninVoltage, theveninResistance]

/-- The load operating point is unique. -/
example : ∃! VI : ℝ × ℝ, 2 * VI.1 = 4 - VI.2 ∧ VI.1 = 3 / 2 * VI.2 :=
  onePort_resistiveLoad_existsUnique 2 4 (3 / 2) (by norm_num) (by norm_num)

/-- The worked finite-load example. -/
example : theveninVoltage 2 4 = 2 ∧ theveninResistance 2 = 1 / 2 ∧
    (3 / 2 : ℝ) = 3 / 2 ∧ (1 : ℝ) = 1 :=
  resistiveLoad_example (3 / 2) 1 (by norm_num) (by norm_num)

/-- The headline divider clause at `K = 2`, `jEff = 4`, `RL = 3/2`. -/
example : (3 / 2 : ℝ) = theveninVoltage 2 4 * (3 / 2) / (theveninResistance 2 + 3 / 2) :=
  (thevenin_onePort_correct 2 4 (by norm_num)).2.2.2.2.2 (3 / 2) (3 / 2) 1
    (by norm_num) (by norm_num) (by norm_num)

/-- The reversed load-current sign breaks the divider. -/
example : ∃ V I : ℝ, 1 * V = 1 + I ∧ V = 2 * I ∧
    V ≠ theveninVoltage 1 1 * 2 / (theveninResistance 1 + 2) :=
  reversedLoadSign_counterexample

/-! ### A concrete two-node network

Conductance matrix `[[2, -1], [-1, 2]]` with node 1 the port and
node 2 interior. Port source `jS = 2`, interior injection `2`, load
current `I = 1` out of the port. The full solution is `V = 4/3` at
the port and `5/3` at the interior node; the reduced port has
`K = 3/2`, `jEff = 3`, `Vth = 2`, `Rth = 2/3`, and the load is
`RL = V / I = 4/3`. -/

/-- The two-node conductance matrix is positive definite: its
quadratic form is `2a^2 - 2ab + 2b^2 = a^2 + (a - b)^2 + b^2`. -/
lemma twoNode_posDef :
    (fromBlocks (Matrix.of fun _ _ => (2 : ℝ) : Matrix Unit Unit ℝ)
      (Matrix.of fun _ _ => (-1 : ℝ) : Matrix Unit (Fin 1) ℝ)
      (Matrix.of fun _ _ => (-1 : ℝ) : Matrix Unit (Fin 1) ℝ)ᵀ
      (!![2] : Matrix (Fin 1) (Fin 1) ℝ)).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  have hform : ∀ z : Unit ⊕ Fin 1 → ℝ,
      z ⬝ᵥ (fromBlocks (Matrix.of fun _ _ => (2 : ℝ) : Matrix Unit Unit ℝ)
        (Matrix.of fun _ _ => (-1 : ℝ) : Matrix Unit (Fin 1) ℝ)
        (Matrix.of fun _ _ => (-1 : ℝ) : Matrix Unit (Fin 1) ℝ)ᵀ
        (!![2] : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ z) =
        2 * (z (Sum.inl ())) ^ 2 - 2 * (z (Sum.inl ())) * (z (Sum.inr 0)) +
          2 * (z (Sum.inr 0)) ^ 2 := by
    intro z
    simp only [dotProduct, Matrix.mulVec, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Fintype.sum_sum_type,
      Fintype.sum_unique, Matrix.of_apply, Matrix.transpose_apply, Matrix.cons_val_fin_one]
    simp
    ring
  refine ⟨by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      fin_cases i <;> fin_cases j <;> simp [Matrix.fromBlocks], fun x hx => ?_⟩
  simp only [star_trivial]
  rw [hform]
  have hne : x (Sum.inl ()) ≠ 0 ∨ x (Sum.inr 0) ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext fun i => by rcases i with i | i <;> fin_cases i <;> simp [h.1, h.2])
  rcases hne with h0 | h1
  · nlinarith [sq_nonneg (x (Sum.inl ()) - x (Sum.inr 0)), sq_nonneg (x (Sum.inr 0)),
      sq_pos_of_ne_zero h0]
  · nlinarith [sq_nonneg (x (Sum.inl ()) - x (Sum.inr 0)), sq_nonneg (x (Sum.inl ())),
      sq_pos_of_ne_zero h1]

/-- Kron reduction of the full solution gives the reduced law and the
Thevenin form with positive port conductance. -/
lemma twoNode_reduced :
    0 < kronPortConductance (Matrix.of fun _ _ => (2 : ℝ))
        (Matrix.of fun _ _ => (-1 : ℝ)) (!![2] : Matrix (Fin 1) (Fin 1) ℝ) ∧
      kronPortConductance (Matrix.of fun _ _ => (2 : ℝ))
          (Matrix.of fun _ _ => (-1 : ℝ)) (!![2] : Matrix (Fin 1) (Fin 1) ℝ) * (4 / 3) =
        kronPortInjection (Matrix.of fun _ _ => (-1 : ℝ))
          (!![2] : Matrix (Fin 1) (Fin 1) ℝ) 2 ![2] - 1 ∧
      (4 / 3 : ℝ) = theveninVoltage
          (kronPortConductance (Matrix.of fun _ _ => (2 : ℝ))
            (Matrix.of fun _ _ => (-1 : ℝ)) (!![2] : Matrix (Fin 1) (Fin 1) ℝ))
          (kronPortInjection (Matrix.of fun _ _ => (-1 : ℝ))
            (!![2] : Matrix (Fin 1) (Fin 1) ℝ) 2 ![2])
        - theveninResistance
          (kronPortConductance (Matrix.of fun _ _ => (2 : ℝ))
            (Matrix.of fun _ _ => (-1 : ℝ)) (!![2] : Matrix (Fin 1) (Fin 1) ℝ)) * 1 :=
  kronOnePort_thevenin _ _ _ twoNode_posDef (4 / 3) 2 1 ![5 / 3] ![2]
    (by ext u; simp [Matrix.mulVec, dotProduct]; norm_num)
    (by ext i; fin_cases i; simp [Matrix.mulVec, dotProduct]; norm_num)

/-- The reduced port of the two-node network has `K = 3/2`,
`jEff = 3`, `Vth = 2` and `Rth = 2/3`. -/
example :
    theveninVoltage
        (kronPortConductance (Matrix.of fun _ _ => (2 : ℝ))
          (Matrix.of fun _ _ => (-1 : ℝ)) (!![2] : Matrix (Fin 1) (Fin 1) ℝ))
        (kronPortInjection (Matrix.of fun _ _ => (-1 : ℝ))
          (!![2] : Matrix (Fin 1) (Fin 1) ℝ) 2 ![2]) = 2 ∧
      theveninResistance
        (kronPortConductance (Matrix.of fun _ _ => (2 : ℝ))
          (Matrix.of fun _ _ => (-1 : ℝ)) (!![2] : Matrix (Fin 1) (Fin 1) ℝ)) = 2 / 3 := by
  obtain ⟨hK, hj⟩ := kronOnePort_interiorSource_example 2
  rw [hK, hj]
  norm_num [theveninVoltage, theveninResistance]

/-- The load `RL = 4/3` on the reduced two-node port reproduces the
full-network port voltage `4/3` as the Thevenin divider. -/
example :
    (4 / 3 : ℝ) = theveninVoltage
        (kronPortConductance (Matrix.of fun _ _ => (2 : ℝ))
          (Matrix.of fun _ _ => (-1 : ℝ)) (!![2] : Matrix (Fin 1) (Fin 1) ℝ))
        (kronPortInjection (Matrix.of fun _ _ => (-1 : ℝ))
          (!![2] : Matrix (Fin 1) (Fin 1) ℝ) 2 ![2]) * (4 / 3) /
      (theveninResistance
        (kronPortConductance (Matrix.of fun _ _ => (2 : ℝ))
          (Matrix.of fun _ _ => (-1 : ℝ)) (!![2] : Matrix (Fin 1) (Fin 1) ℝ)) + 4 / 3) := by
  obtain ⟨hpos, hlaw, _⟩ := twoNode_reduced
  exact (onePort_resistiveLoad _ _ (4 / 3) (4 / 3) 1 hpos (by norm_num) hlaw
    (by norm_num)).1

end PhyslibExtTest.Circuits.TheveninNortonPort
