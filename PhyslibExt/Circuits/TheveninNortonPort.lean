/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.SchurStrictPositivity
public import PhyslibExt.Circuits.KronPortReduction
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Thevenin and Norton equivalents of a reduced one-port

## i. Overview

A linear resistive one-port seen from its terminals obeys the reduced
law `K * V = jEff - I`, with real DC port voltage `V`, port
conductance `K > 0`, effective injected current `jEff`, and load
current `I` flowing out of the port. This law is equivalent to the
Thevenin form `V = Vth - Rth * I` with open-circuit voltage
`Vth = jEff / K` and Thevenin resistance `Rth = 1 / K`, and to the
Norton form `I = jEff - K * V` with Norton current `jEff`. Open
circuit (`I = 0`) gives `V = Vth`. A resistive load is specified
multiplicatively by `V = RL * I` with `RL ≥ 0`, so that the short
`RL = 0` is included without dividing by `RL`; it gives the voltage
divider `V = Vth * RL / (Rth + RL)` and the load current
`I = Vth / (Rth + RL)`, and at the short `V = 0` and `I = jEff`.

For a positive-definite conductance matrix with one retained port,
Kron reduction supplies exactly this law: the port conductance is the
single entry of the Schur complement, which is positive, and the
effective injection is the port source corrected by the interior
injections. No nonlinear device, time-varying element, or zero port
conductance is treated.

The Schur complement is the canonical one from
`MathlibExt.LinearAlgebra.Matrix.SchurStrictPositivity`, and the
reduced port equation with its positivity comes from the canonical
Kron reduction theorem
`PhyslibExt.Circuits.KronPortReduction.kron_reduction_correct`.

## ii. Key results

- `onePort_iff_thevenin`: the one-port law is equivalent to the
  Thevenin form for `K > 0`.
- `onePort_iff_norton`: the one-port law is the Norton form.
- `onePort_resistiveLoad`: a resistive load `RL ≥ 0` gives the
  voltage divider and the load current.
- `thevenin_onePort_correct`: the headline conjunction of the
  Thevenin parameters, the Thevenin form, open circuit, and the
  resistive-load divider.
- `kronOnePort_thevenin`: Kron reduction of a positive-definite
  network to one retained port yields the one-port law with positive
  conductance, hence the Thevenin form.

## iii. Table of contents

- A. Thevenin and Norton parameters
- B. Thevenin and Norton forms of the one-port law
- C. Kron reduction to one retained port
- D. Worked examples

## iv. References

- L. Thévenin, "Extension de la loi d'Ohm aux circuits
  électromoteurs complexes", *Annales Télégraphiques* (3e série) 10,
  1883, pp. 222-224: the equivalent source and series resistance of a
  linear network seen from two terminals.
- E. L. Norton, "Design of finite networks for uniform frequency
  characteristic", Bell Laboratories Technical Report TM26-0-1860,
  1926: the equivalent current source with parallel conductance.
- F. Dörfler and F. Bullo, "Kron reduction of graphs with
  applications to electrical networks", *IEEE Transactions on
  Circuits and Systems I: Regular Papers* 60(1), 2013, pp. 150-163:
  Kron reduction as the Schur complement of the conductance matrix,
  and the reduced port equations with corrected injections.

## A. Thevenin and Norton parameters

The Thevenin voltage and resistance of the one-port law, and the
port conductance and effective injection of a one-port Kron
reduction.
-/

@[expose] public section

open Matrix

namespace PhyslibExt.Circuits.TheveninNortonPort

open MathlibExt.LinearAlgebra.Matrix.SchurStrictPositivity

/-- Thevenin (open-circuit) voltage `jEff / K` of the one-port law
`K * V = jEff - I`. -/
noncomputable def theveninVoltage (K jEff : ℝ) : ℝ :=
  jEff / K

/-- Thevenin resistance `1 / K` of the one-port law. -/
noncomputable def theveninResistance (K : ℝ) : ℝ :=
  1 / K

/-- Port conductance of a one-port Kron reduction: the single entry of
the Schur complement. -/
noncomputable def kronPortConductance {p : Type*} [Fintype p] [DecidableEq p]
    (A : Matrix Unit Unit ℝ) (B : Matrix Unit p ℝ) (D : Matrix p p ℝ) : ℝ :=
  schurComplement A B D () ()

/-- Effective injected current of a one-port Kron reduction: the port
source `jS` corrected by the interior injection, `jS - (B D⁻¹ jI)`. -/
noncomputable def kronPortInjection {p : Type*} [Fintype p] [DecidableEq p]
    (B : Matrix Unit p ℝ) (D : Matrix p p ℝ) (jS : ℝ) (jI : p → ℝ) : ℝ :=
  jS - (B *ᵥ (D⁻¹ *ᵥ jI)) ()

/-- The Thevenin resistance of a positive conductance is positive. -/
lemma theveninResistance_pos (K : ℝ) (hK : 0 < K) :
    0 < theveninResistance K := by
  unfold theveninResistance
  exact one_div_pos.mpr hK

/-! ## B. Thevenin and Norton forms of the one-port law

The equivalence of the one-port law with the Thevenin and Norton
forms, open and short circuit, and the resistive-load operating
point. -/

/-- One-port law and Thevenin form are equivalent for `K > 0`, with
the load current taken out of the port. -/
theorem onePort_iff_thevenin (K jEff V I : ℝ) (hK : 0 < K) :
    K * V = jEff - I ↔ V = theveninVoltage K jEff - theveninResistance K * I := by
  have hK0 : K ≠ 0 := ne_of_gt hK
  unfold theveninVoltage theveninResistance
  constructor
  · intro h
    field_simp
    linarith
  · intro h
    field_simp at h
    linarith

/-- Norton form: the load current is the Norton current `jEff` minus
`K * V`. -/
theorem onePort_iff_norton (K jEff V I : ℝ) :
    K * V = jEff - I ↔ I = jEff - K * V := by
  constructor <;> intro h <;> linarith

/-- Open circuit: with zero load current the port voltage is the
Thevenin voltage. -/
lemma onePort_openCircuit (K jEff V : ℝ) (hK : 0 < K)
    (h : K * V = jEff - 0) :
    V = theveninVoltage K jEff := by
  have hK0 : K ≠ 0 := ne_of_gt hK
  unfold theveninVoltage
  field_simp
  linarith

/-- Resistive load `V = RL * I` with `RL ≥ 0`: the port voltage is the
divider `Vth * RL / (Rth + RL)` and the load current is
`Vth / (Rth + RL)`. -/
theorem onePort_resistiveLoad (K jEff RL V I : ℝ) (hK : 0 < K) (hRL : 0 ≤ RL)
    (hlaw : K * V = jEff - I) (hload : V = RL * I) :
    V = theveninVoltage K jEff * RL / (theveninResistance K + RL) ∧
      I = theveninVoltage K jEff / (theveninResistance K + RL) := by
  have hK0 : K ≠ 0 := ne_of_gt hK
  have hRth : 0 < theveninResistance K := theveninResistance_pos K hK
  have hden : 0 < theveninResistance K + RL := by linarith
  have hden0 : theveninResistance K + RL ≠ 0 := ne_of_gt hden
  unfold theveninVoltage theveninResistance at *
  field_simp
  constructor
  · have hRLhlaw : RL * (K * V) = RL * (jEff - I) := by rw [hlaw]
    have hring : V * (1 + K * RL) = V + RL * (K * V) := by ring
    rw [hring, hRLhlaw, hload]
    ring
  · have hring2 : (1 + K * RL) * I = I + K * (RL * I) := by ring
    rw [hring2, ← hload, hlaw]
    ring

/-- Short circuit, the `RL = 0` case: zero port voltage and load
current equal to the Norton current `jEff`. -/
lemma onePort_shortCircuit (K jEff V I : ℝ) (hK : 0 < K)
    (hlaw : K * V = jEff - I) (hload : V = 0 * I) :
    V = 0 ∧ I = jEff := by
  have _ : 0 < K := hK
  have hV : V = 0 := by linarith
  refine ⟨hV, ?_⟩
  rw [hV, mul_zero] at hlaw
  linarith

/-- The resistive-load operating point exists and is unique for
`K > 0` and `RL ≥ 0`. -/
lemma onePort_resistiveLoad_existsUnique (K jEff RL : ℝ) (hK : 0 < K)
    (hRL : 0 ≤ RL) :
    ∃! VI : ℝ × ℝ, K * VI.1 = jEff - VI.2 ∧ VI.1 = RL * VI.2 := by
  have hK0 : K ≠ 0 := ne_of_gt hK
  have hRth : 0 < theveninResistance K := theveninResistance_pos K hK
  have hden : 0 < theveninResistance K + RL := by linarith
  have hden0 : theveninResistance K + RL ≠ 0 := ne_of_gt hden
  refine ⟨(theveninVoltage K jEff * RL / (theveninResistance K + RL),
    theveninVoltage K jEff / (theveninResistance K + RL)), ?_, ?_⟩
  · constructor
    · change K * (theveninVoltage K jEff * RL / (theveninResistance K + RL)) =
        jEff - theveninVoltage K jEff / (theveninResistance K + RL)
      unfold theveninVoltage theveninResistance at *
      field_simp
      ring
    · change theveninVoltage K jEff * RL / (theveninResistance K + RL) =
        RL * (theveninVoltage K jEff / (theveninResistance K + RL))
      unfold theveninVoltage theveninResistance at *
      field_simp
  · intro VI hVI
    obtain ⟨hlaw, hload⟩ := hVI
    have hpair := onePort_resistiveLoad K jEff RL VI.1 VI.2 hK hRL hlaw hload
    obtain ⟨hV, hI⟩ := hpair
    obtain ⟨V, I⟩ := VI
    simp_all

/-- Headline correctness: for `K > 0`, the one-port law is the
Thevenin form with `Vth = jEff / K` and `Rth = 1 / K`, open circuit
gives `Vth`, and any resistive load `RL ≥ 0`, the short included,
gives the divider voltage. -/
theorem thevenin_onePort_correct (K jEff : ℝ) (hK : 0 < K) :
    theveninVoltage K jEff = jEff / K ∧
      theveninResistance K = 1 / K ∧
      0 < theveninResistance K ∧
      (∀ V I : ℝ, K * V = jEff - I ↔
        V = theveninVoltage K jEff - theveninResistance K * I) ∧
      (∀ V : ℝ, K * V = jEff - 0 → V = theveninVoltage K jEff) ∧
      (∀ RL V I : ℝ, 0 ≤ RL → K * V = jEff - I → V = RL * I →
        V = theveninVoltage K jEff * RL / (theveninResistance K + RL)) := by
  refine ⟨rfl, rfl, theveninResistance_pos K hK, ?_, ?_, ?_⟩
  · intro V I
    exact onePort_iff_thevenin K jEff V I hK
  · intro V h
    exact onePort_openCircuit K jEff V hK h
  · intro RL V I hRL hlaw hload
    exact (onePort_resistiveLoad K jEff RL V I hK hRL hlaw hload).1

/-! ## C. Kron reduction to one retained port

The one-port law, with positive conductance, for a positive-definite
network reduced to a single retained port. -/

/-- Kron reduction to one retained port: for a positive-definite
conductance matrix, a full solution with port injection `jS - I`
(port source `jS`, load current `I` out of the port) satisfies the
one-port law with positive conductance `kronPortConductance` and
effective injection `kronPortInjection`, hence the Thevenin form. -/
theorem kronOnePort_thevenin {p : Type*} [Fintype p] [DecidableEq p]
    (A : Matrix Unit Unit ℝ) (B : Matrix Unit p ℝ) (D : Matrix p p ℝ)
    (hG : (fromBlocks A B Bᵀ D).PosDef) (V jS I : ℝ) (φI : p → ℝ) (jI : p → ℝ)
    (hP : A *ᵥ (fun _ => V) + B *ᵥ φI = fun _ => jS - I)
    (hI : Bᵀ *ᵥ (fun _ => V) + D *ᵥ φI = jI) :
    0 < kronPortConductance A B D ∧
      kronPortConductance A B D * V = kronPortInjection B D jS jI - I ∧
      V = theveninVoltage (kronPortConductance A B D) (kronPortInjection B D jS jI)
        - theveninResistance (kronPortConductance A B D) * I := by
  obtain ⟨hPos, hRed, _, _⟩ :=
    PhyslibExt.Circuits.KronPortReduction.kron_reduction_correct A B D hG
      (fun _ => V) φI (fun _ => jS - I) jI hP hI
  have hNe : (fun _ => (1 : ℝ) : Unit → ℝ) ≠ 0 := by
    intro h
    have h0 := congrFun h ()
    simp_all
  have hpos := hPos.dotProduct_mulVec_pos hNe
  have hcalc : (star (fun _ => (1 : ℝ)) ⬝ᵥ
      (schurComplement A B D *ᵥ (fun _ => (1 : ℝ)))) =
      schurComplement A B D () () := by
    simp [mulVec, dotProduct, Finset.univ_unique]
  have hKpos : 0 < kronPortConductance A B D := by
    unfold kronPortConductance
    rw [← hcalc]
    exact hpos
  have hLHS : (schurComplement A B D *ᵥ (fun _ => V)) () =
      schurComplement A B D () () * V := by
    simp [mulVec, dotProduct, Finset.univ_unique]
  have hRed0 := congrFun hRed ()
  rw [hLHS] at hRed0
  simp only [Pi.sub_apply] at hRed0
  have hLaw : kronPortConductance A B D * V =
      kronPortInjection B D jS jI - I := by
    unfold kronPortConductance kronPortInjection
    linarith
  have hThev := (onePort_iff_thevenin _ _ V I hKpos).mp hLaw
  exact ⟨hKpos, hLaw, hThev⟩

/-! ## D. Worked examples

A finite positive load, a Kron reduction with a nonzero interior
source, and the failure of the reversed load-current sign. -/

/-- Finite positive load: `K = 2`, `jEff = 4`, `RL = 3/2` give
`Vth = 2`, `Rth = 1/2`, port voltage `3/2` and load current `1`. -/
lemma resistiveLoad_example (V I : ℝ) (hlaw : 2 * V = 4 - I)
    (hload : V = 3 / 2 * I) :
    theveninVoltage 2 4 = 2 ∧ theveninResistance 2 = 1 / 2 ∧ V = 3 / 2 ∧ I = 1 := by
  have hI : I = 1 := by linarith
  have hV : V = 3 / 2 := by linarith
  refine ⟨?_, rfl, hV, hI⟩
  unfold theveninVoltage
  norm_num

/-- Nonzero interior-source contribution: for the conductance matrix
`[[2, -1], [-1, 2]]` with one port and one interior node carrying
injection `2`, the port conductance is `3/2` and the effective
injection is the port source plus `1`. -/
lemma kronOnePort_interiorSource_example (jS : ℝ) :
    kronPortConductance (Matrix.of fun _ _ => (2 : ℝ)) (Matrix.of fun _ _ => (-1 : ℝ))
        (!![2] : Matrix (Fin 1) (Fin 1) ℝ) = 3 / 2 ∧
      kronPortInjection (Matrix.of fun _ _ => (-1 : ℝ)) (!![2] : Matrix (Fin 1) (Fin 1) ℝ)
        jS ![2] = jS + 1 := by
  have hdet : ((!![2] : Matrix (Fin 1) (Fin 1) ℝ).det) = 2 := det_fin_one_of 2
  have hunit : IsUnit ((!![2] : Matrix (Fin 1) (Fin 1) ℝ).det) := by
    rw [hdet]
    exact isUnit_iff_ne_zero.mpr (by norm_num)
  have hmul : (!![2] : Matrix (Fin 1) (Fin 1) ℝ) * (!![2] : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ = 1 :=
    mul_nonsing_inv _ hunit
  have h00 : ((!![2] : Matrix (Fin 1) (Fin 1) ℝ) * (!![2] : Matrix (Fin 1) (Fin 1) ℝ)⁻¹) 0 0 =
      (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 0 := by rw [hmul]
  have hLHS : ((!![2] : Matrix (Fin 1) (Fin 1) ℝ) * (!![2] : Matrix (Fin 1) (Fin 1) ℝ)⁻¹) 0 0 =
      2 * (((!![2] : Matrix (Fin 1) (Fin 1) ℝ)⁻¹) 0 0) := by
    simp [mul_apply, Finset.univ_unique]
  rw [hLHS] at h00
  have hRHS : (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 0 = 1 := by simp
  rw [hRHS] at h00
  have hDinv : ((!![2] : Matrix (Fin 1) (Fin 1) ℝ)⁻¹) 0 0 = 1 / 2 := by linarith
  constructor
  · unfold kronPortConductance schurComplement
    simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_one, Matrix.of_apply,
      transpose_apply]
    rw [hDinv]
    norm_num
  · unfold kronPortInjection
    simp only [mulVec, dotProduct, Fin.sum_univ_one, Matrix.of_apply,
      Matrix.cons_val_zero]
    rw [hDinv]
    ring

/-- Reversed load-current sign fails: under the wrong convention
`K * V = jEff + I` with `K = 1`, `jEff = 1`, the load `RL = 2` admits
the operating point `V = 2`, `I = 1`, which differs from the divider
value `Vth * RL / (Rth + RL) = 2/3`. -/
lemma reversedLoadSign_counterexample :
    ∃ V I : ℝ, 1 * V = 1 + I ∧ V = 2 * I ∧
      V ≠ theveninVoltage 1 1 * 2 / (theveninResistance 1 + 2) := by
  refine ⟨2, 1, by norm_num, by norm_num, ?_⟩
  unfold theveninVoltage theveninResistance
  norm_num

end PhyslibExt.Circuits.TheveninNortonPort
