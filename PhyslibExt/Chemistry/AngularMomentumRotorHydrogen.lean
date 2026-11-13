/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.PNat.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Physlib.QuantumMechanics.Hydrogen.Rydberg
public import Physlib.Relativity.PauliMatrices.Basic

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Angular momentum, rigid rotor and hydrogen-like atom

Explicit `l = 0, 1/2, 1` angular-momentum representations, the rigid rotor, hydrogen-like
radial functions and levels, the Rydberg formula, and the Aufbau and Hund counting rules.

## i. Overview

The angular-momentum part works with explicit complex matrices and keeps `hbar` symbolic. For
`l = 0, 1/2, 1` the components `Jx, Jy, Jz` are `(2 * l + 1) × (2 * l + 1)` matrices: the zero
matrix `lZeroL` in each component for `l = 0`, `spinHalfJx`, `spinHalfJy`, `spinHalfJz` built from
Physlib's Pauli matrices `PauliMatrix.pauliMatrix` for `l = 1/2`, and `lOneLx`, `lOneLy`,
`lOneLz` for `l = 1`. For each of them this file proves the commutation relations
`[Jx, Jy] = i hbar Jz` (and cyclic), the Casimir value `J^2 = l (l + 1) hbar^2`, and
irreducibility: for `hbar ≠ 0` every subspace of the carrier `Fin (2 * l + 1) → ℂ` invariant
under `Jx` and `Jz` is `⊥` or `⊤`. The classification of all finite-dimensional irreducible
representations is not proved. `commutator A B = A * B - B * A` is Mathlib's ring commutator
`⁅A, B⁆` (`commutator_eq_lie`). Physlib's operator-level angular momentum on Schwartz functions
(`QuantumMechanics.angularMomentumDimThreeOperator`, with the commutation relations
`QuantumMechanics.angularMomentumDimThree_commutation`) satisfies the same relations; no bridge
between those operators and the matrices here is built.

The rigid rotor has the levels `E_J = hbar^2 J (J + 1) / (2 I)` for a moment of inertia
`I ≠ 0`, with `2 * J + 1` magnetic sublevels. For the spherical harmonics only the `Lz`
eigenvalues of the `l = 1` matrices and the pole ratio `Y_10 / Y_00 = sqrt 3` are stated; the
Laplacian eigen-equation and completeness on the sphere are not formalized.

The hydrogen-like atom is the nonrelativistic one-electron atom, without fine structure. The
radial functions `R_10`, `R_20`, `R_21` are in atomic units with `Z = 1`: their derivatives are
proved with `HasDerivAt`, and substituted into the radial equation they give the energies
`-1/2` and `-1/8` (`radialResidual_1s`, `radialResidual_2s`, `radialResidual_2p`, an algebraic
identity at each `r ≠ 0`). The levels `E_n = -Z^2 R / n^2` and the Rydberg wavenumbers are
indexed by the principal quantum number `n : ℕ+`, and they agree with Physlib's Bohr levels and
Rydberg formula for a three-dimensional `QuantumMechanics.HydrogenAtom`
(`energyLevel_eq_hydrogenEnergy`, `wavelength_inv_eq_rydbergWavenumber`).

The Aufbau shell capacity and Hund's unpaired-electron count are counting forms of empirical
filling heuristics, not theorems about real atoms.

## ii. Key results

- `spinHalf_commutators`, `lOne_commutators`, `lZero_commutator`: commutation relations.
- `spinHalf_casimir`, `lOne_casimir`, `lZero_casimir`: `J^2 = l (l + 1) hbar^2`.
- `lZero_irreducible`, `spinHalf_irreducible`, `lOne_irreducible`: irreducibility.
- `angularMomentum_rep_dimensions`: the carriers have dimensions `1, 2, 3`.
- `rigidRotorEnergy_spacing`, `rigidRotorMagnetic_count`: rotor spacing and degeneracy.
- `l1_Lz_eigenvalues`: `Lz` has eigenvalues `hbar, 0, -hbar` in the `l = 1` matrices.
- `hydrogenEnergy_scaling`, `hydrogen_degeneracy`, `hydrogen_degeneracy_spin`: levels and
  degeneracies `n^2` and `2 n^2`.
- `radialResidual_1s`, `radialResidual_2s`, `radialResidual_2p` with
  `hydrogenRadial_deriv_1s`, `hydrogenRadial_deriv_2s`, `hydrogenRadial_deriv_2p`: the
  `1s`, `2s`, `2p` radial eigen-equations.
- `rydbergWavenumber_pos`: emission lines have positive wavenumber.
- `energyLevel_eq_hydrogenEnergy`, `wavelength_inv_eq_rydbergWavenumber`: bridges to Physlib.
- `aufbau_shellCapacity`, `hundUnpaired_le_g`: filling counts.

## iii. Table of contents

- A. Angular-momentum matrices
- B. Irreducibility
- C. Rigid rotor and spherical harmonics
- D. Hydrogen-like atom
- E. Filling heuristics

## iv. References

- J. J. Sakurai and J. Napolitano, *Modern Quantum Mechanics*, Chapter 3 (theory of angular
  momentum): commutation relations, the spin-1/2 and `l = 1` matrices, Casimir values and
  irreducible representations.
- D. J. Griffiths and D. F. Schroeter, *Introduction to Quantum Mechanics*, 3rd ed., Cambridge
  University Press, 2018, Chapter 4 (quantum mechanics in three dimensions): angular momentum,
  spin, the hydrogen atom, its radial functions and spectrum, and the Rydberg formula.
- P. Atkins and J. de Paula, *Atkins' Physical Chemistry*, Oxford University Press: the rigid
  rotor, the hydrogen atom, the building-up (Aufbau) principle and Hund's rules.
-/

@[expose] public section

namespace PhyslibExt.Chemistry.AngularMomentumRotorHydrogen

open scoped BigOperators
open scoped Matrix

/-! ## A. Angular-momentum matrices -/

/-- Commutator `[A, B] = A * B - B * A`, Mathlib's ring commutator `⁅A, B⁆`
(`commutator_eq_lie`). -/
noncomputable def commutator {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  A * B - B * A

/-- `commutator` is Mathlib's ring commutator `⁅A, B⁆` (`Ring.lie_def`). -/
lemma commutator_eq_lie {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    commutator A B = ⁅A, B⁆ :=
  (Ring.lie_def A B).symm

/-- Each component `Lx = Ly = Lz` of the `l = 0` angular momentum (the trivial
representation) is the zero operator on the one-dimensional carrier `Fin 1 → ℂ`. -/
noncomputable def lZeroL : Matrix (Fin 1) (Fin 1) ℂ := 0

/-- Spin-1/2 angular momentum `Jx = (hbar / 2) * σ₁`, with Physlib's Pauli matrix
`σ₁ = PauliMatrix.pauliMatrix (Sum.inr 0)`. -/
noncomputable def spinHalfJx (hbar : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((hbar : ℂ) / 2) • PauliMatrix.pauliMatrix (Sum.inr 0)

/-- Spin-1/2 angular momentum `Jy = (hbar / 2) * σ₂`, with Physlib's Pauli matrix
`σ₂ = PauliMatrix.pauliMatrix (Sum.inr 1)`. -/
noncomputable def spinHalfJy (hbar : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((hbar : ℂ) / 2) • PauliMatrix.pauliMatrix (Sum.inr 1)

/-- Spin-1/2 angular momentum `Jz = (hbar / 2) * σ₃`, with Physlib's Pauli matrix
`σ₃ = PauliMatrix.pauliMatrix (Sum.inr 2)`. -/
noncomputable def spinHalfJz (hbar : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((hbar : ℂ) / 2) • PauliMatrix.pauliMatrix (Sum.inr 2)

/-- l = 1 angular momentum `Lx`. -/
noncomputable def lOneLx (hbar : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  ((hbar : ℂ) / ((Real.sqrt 2 : ℝ) : ℂ)) • !![0, 1, 0; 1, 0, 1; 0, 1, 0]

/-- l = 1 angular momentum `Ly`. -/
noncomputable def lOneLy (hbar : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  ((hbar : ℂ) / ((Real.sqrt 2 : ℝ) : ℂ)) •
    !![0, -Complex.I, 0; Complex.I, 0, -Complex.I; 0, Complex.I, 0]

/-- l = 1 angular momentum `Lz = hbar * diag(1, 0, -1)`. -/
noncomputable def lOneLz (hbar : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  (hbar : ℂ) • !![1, 0, 0; 0, 0, 0; 0, 0, -1]

/-- `l = 0` commutation relations: the commutator of the zero components is `i hbar` times
the zero component. -/
lemma lZero_commutator (hbar : ℝ) :
    commutator lZeroL lZeroL = (Complex.I * (hbar : ℂ)) • lZeroL := by
  simp [commutator, lZeroL]

/-- `l = 0` Casimir: `L^2 = 0`, since `l (l + 1) = 0`. -/
lemma lZero_casimir : lZeroL ^ 2 + lZeroL ^ 2 + lZeroL ^ 2 = 0 := by
  simp [lZeroL]

/-- Spin-1/2 angular-momentum commutators `[Jx, Jy] = i * hbar * Jz` (and cyclic), from
Physlib's Pauli commutators `PauliMatrix.σ1_σ2_commutator`, `PauliMatrix.σ2_σ3_commutator`
and `PauliMatrix.σ3_σ1_commutator`. -/
theorem spinHalf_commutators (hbar : ℝ) :
    commutator (spinHalfJx hbar) (spinHalfJy hbar) =
      (Complex.I * (hbar : ℂ)) • spinHalfJz hbar ∧
    commutator (spinHalfJy hbar) (spinHalfJz hbar) =
      (Complex.I * (hbar : ℂ)) • spinHalfJx hbar ∧
    commutator (spinHalfJz hbar) (spinHalfJx hbar) =
      (Complex.I * (hbar : ℂ)) • spinHalfJy hbar := by
  have key : ∀ a b c : Matrix (Fin 2) (Fin 2) ℂ, a * b - b * a = (2 * Complex.I) • c →
      commutator (((hbar : ℂ) / 2) • a) (((hbar : ℂ) / 2) • b) =
        (Complex.I * (hbar : ℂ)) • (((hbar : ℂ) / 2) • c) := by
    intro a b c h
    rw [commutator, smul_mul_smul_comm, smul_mul_smul_comm, ← smul_sub, h, smul_smul,
      smul_smul]
    congr 1
    ring
  exact ⟨key _ _ _ PauliMatrix.σ1_σ2_commutator, key _ _ _ PauliMatrix.σ2_σ3_commutator,
    key _ _ _ PauliMatrix.σ3_σ1_commutator⟩

/-- Spin-1/2 Casimir: `J^2 = (3/4) * hbar^2 * 1`, from `σᵢ * σᵢ = 1`
(`PauliMatrix.pauliMatrix_mul_self`). -/
theorem spinHalf_casimir (hbar : ℝ) :
    spinHalfJx hbar ^ 2 + spinHalfJy hbar ^ 2 + spinHalfJz hbar ^ 2 =
      ((3 / 4 : ℂ) * (hbar : ℂ) ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  simp only [spinHalfJx, spinHalfJy, spinHalfJz, pow_two, smul_mul_smul_comm,
    PauliMatrix.pauliMatrix_mul_self, ← add_smul]
  congr 1
  ring

/-- l = 1 angular-momentum commutators `[Lx, Ly] = i * hbar * Lz` (and cyclic). -/
theorem lOne_commutators (hbar : ℝ) :
    commutator (lOneLx hbar) (lOneLy hbar) =
      (Complex.I * (hbar : ℂ)) • lOneLz hbar ∧
    commutator (lOneLy hbar) (lOneLz hbar) =
      (Complex.I * (hbar : ℂ)) • lOneLx hbar ∧
    commutator (lOneLz hbar) (lOneLx hbar) =
      (Complex.I * (hbar : ℂ)) • lOneLy hbar := by
  have hsq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hs0 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    exact_mod_cast ne_of_gt h2
  have hsq_mul : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← pow_two]
    exact hsq
  have hI : (Complex.I : ℂ) ^ 2 = -1 := by
    rw [pow_two]
    exact Complex.I_mul_I
  refine ⟨?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j
  all_goals simp [commutator, lOneLx, lOneLy, lOneLz, Matrix.mul_apply,
    Matrix.sub_apply, Matrix.smul_apply, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  all_goals (try field_simp [hs0])
  all_goals ring_nf
  all_goals (try simp only [hsq, hsq_mul, hI, Complex.I_mul_I])
  all_goals ring

/-- l = 1 Casimir: `L^2 = 2 * hbar^2 * 1` (l(l+1) = 2). -/
theorem lOne_casimir (hbar : ℝ) :
    lOneLx hbar ^ 2 + lOneLy hbar ^ 2 + lOneLz hbar ^ 2 =
      (2 * (hbar : ℂ) ^ 2) • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  have hsq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hs0 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    exact_mod_cast ne_of_gt h2
  have hsq_mul : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← pow_two]
    exact hsq
  have hI : (Complex.I : ℂ) ^ 2 = -1 := by
    rw [pow_two]
    exact Complex.I_mul_I
  have h10 : (1 : Fin 3) ≠ 0 := by decide
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [lOneLx, lOneLy, lOneLz, Matrix.add_apply, Matrix.mul_apply,
    Matrix.smul_apply, Matrix.one_apply, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, pow_two, h10, h20, h21, h01,
    h02, h12]
  all_goals (try field_simp [hs0])
  all_goals ring_nf
  all_goals (try simp only [hsq, hsq_mul, hI, Complex.I_mul_I])
  all_goals ring

/-! ## B. Irreducibility -/

/-- A subspace of `Fin n → ℂ` that contains every standard basis vector is everything. -/
private lemma eq_top_of_forall_single_mem {n : ℕ} (W : Submodule ℂ (Fin n → ℂ))
    (h : ∀ i, Pi.single i (1 : ℂ) ∈ W) : W = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun ℂ (Fin n)).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  simpa using h i

/-- A nonzero vector has a nonzero coordinate. -/
private lemma exists_apply_ne_zero {n : ℕ} {v : Fin n → ℂ} (hv : v ≠ 0) : ∃ i, v i ≠ 0 :=
  Function.ne_iff.mp hv

/-- The `l = 0` representation is irreducible: every subspace of the one-dimensional carrier
`Fin 1 → ℂ`, in particular every subspace invariant under the zero components `lZeroL`, is `⊥`
or `⊤`. -/
lemma lZero_irreducible (W : Submodule ℂ (Fin 1 → ℂ)) : W = ⊥ ∨ W = ⊤ := by
  rcases eq_or_ne W ⊥ with hW | hW
  · exact Or.inl hW
  right
  obtain ⟨v, hvW, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  obtain ⟨i, hi⟩ := exists_apply_ne_zero hv0
  apply eq_top_of_forall_single_mem
  intro j
  have hij : i = j := Subsingleton.elim i j
  subst hij
  have hv : v i • Pi.single i (1 : ℂ) = v := by
    ext k
    have hk : k = i := Subsingleton.elim k i
    subst hk
    simp
  have hmem : v i • Pi.single i (1 : ℂ) ∈ W := by
    rw [hv]
    exact hvW
  exact (W.smul_mem_iff hi).mp hmem

/-- The spin-1/2 representation is irreducible: for `hbar ≠ 0`, a subspace of `Fin 2 → ℂ`
invariant under `Jx` and `Jz` (in particular one invariant under all three components) is `⊥`
or `⊤`. -/
theorem spinHalf_irreducible {hbar : ℝ} (hbar0 : hbar ≠ 0) (W : Submodule ℂ (Fin 2 → ℂ))
    (hx : ∀ v ∈ W, spinHalfJx hbar *ᵥ v ∈ W) (hz : ∀ v ∈ W, spinHalfJz hbar *ᵥ v ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  rcases eq_or_ne W ⊥ with hW | hW
  · exact Or.inl hW
  right
  have hh : (hbar : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hbar0
  have hh2 : (hbar : ℂ) / 2 ≠ 0 := div_ne_zero hh two_ne_zero
  -- `Jz` separates the two coordinates of every vector of `W`.
  have hproj : ∀ w ∈ W, ∀ i : Fin 2, w i • Pi.single i (1 : ℂ) ∈ W := by
    intro w hw i
    have hzw := hz w hw
    fin_cases i
    · change w 0 • Pi.single (0 : Fin 2) (1 : ℂ) ∈ W
      have e : w 0 • Pi.single (0 : Fin 2) (1 : ℂ) =
          (1 / 2 : ℂ) • w + (1 / (hbar : ℂ)) • (spinHalfJz hbar *ᵥ w) := by
        ext j
        fin_cases j <;>
          simp [spinHalfJz, PauliMatrix.pauliMatrix, dotProduct, Fin.sum_univ_two] <;>
          field_simp <;> ring
      rw [e]
      exact W.add_mem (W.smul_mem _ hw) (W.smul_mem _ hzw)
    · change w 1 • Pi.single (1 : Fin 2) (1 : ℂ) ∈ W
      have e : w 1 • Pi.single (1 : Fin 2) (1 : ℂ) =
          (1 / 2 : ℂ) • w - (1 / (hbar : ℂ)) • (spinHalfJz hbar *ᵥ w) := by
        ext j
        fin_cases j <;>
          simp [spinHalfJz, PauliMatrix.pauliMatrix, dotProduct, Fin.sum_univ_two] <;>
          field_simp <;> ring
      rw [e]
      exact W.sub_mem (W.smul_mem _ hw) (W.smul_mem _ hzw)
  -- `Jx` exchanges the two basis vectors.
  have hx0 : spinHalfJx hbar *ᵥ Pi.single 0 1 = ((hbar : ℂ) / 2) • Pi.single 1 1 := by
    ext j
    fin_cases j <;>
      simp [spinHalfJx, PauliMatrix.pauliMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hx1 : spinHalfJx hbar *ᵥ Pi.single 1 1 = ((hbar : ℂ) / 2) • Pi.single 0 1 := by
    ext j
    fin_cases j <;>
      simp [spinHalfJx, PauliMatrix.pauliMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  obtain ⟨v, hvW, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  obtain ⟨i, hi⟩ := exists_apply_ne_zero hv0
  have hei : Pi.single i (1 : ℂ) ∈ W := (W.smul_mem_iff hi).mp (hproj v hvW i)
  have he : Pi.single (0 : Fin 2) (1 : ℂ) ∈ W ∧ Pi.single (1 : Fin 2) (1 : ℂ) ∈ W := by
    fin_cases i
    · refine ⟨hei, (W.smul_mem_iff hh2).mp ?_⟩
      rw [← hx0]
      exact hx _ hei
    · refine ⟨(W.smul_mem_iff hh2).mp ?_, hei⟩
      rw [← hx1]
      exact hx _ hei
  apply eq_top_of_forall_single_mem
  intro j
  fin_cases j
  · exact he.1
  · exact he.2

/-- The `l = 1` representation is irreducible: for `hbar ≠ 0`, a subspace of `Fin 3 → ℂ`
invariant under `Lx` and `Lz` (in particular one invariant under all three components) is `⊥`
or `⊤`. -/
theorem lOne_irreducible {hbar : ℝ} (hbar0 : hbar ≠ 0) (W : Submodule ℂ (Fin 3 → ℂ))
    (hx : ∀ v ∈ W, lOneLx hbar *ᵥ v ∈ W) (hz : ∀ v ∈ W, lOneLz hbar *ᵥ v ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  rcases eq_or_ne W ⊥ with hW | hW
  · exact Or.inl hW
  right
  have hh : (hbar : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hbar0
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    exact_mod_cast ne_of_gt h2
  have hc : (hbar : ℂ) / ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := div_ne_zero hh hs
  have h10 : (1 : Fin 3) ≠ 0 := by decide
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  -- `Lz` and `Lz ^ 2` separate the three coordinates of every vector of `W`.
  have hproj : ∀ w ∈ W, ∀ i : Fin 3, w i • Pi.single i (1 : ℂ) ∈ W := by
    intro w hw i
    have h1 := hz w hw
    have h2 := hz _ h1
    fin_cases i
    · change w 0 • Pi.single (0 : Fin 3) (1 : ℂ) ∈ W
      have e : w 0 • Pi.single (0 : Fin 3) (1 : ℂ) =
          (1 / (2 * (hbar : ℂ) ^ 2)) • (lOneLz hbar *ᵥ (lOneLz hbar *ᵥ w)) +
            (1 / (2 * (hbar : ℂ))) • (lOneLz hbar *ᵥ w) := by
        ext j
        fin_cases j <;>
          simp [lOneLz, dotProduct, Fin.sum_univ_three, h10, h20] <;>
          field_simp <;> ring
      rw [e]
      exact W.add_mem (W.smul_mem _ h2) (W.smul_mem _ h1)
    · change w 1 • Pi.single (1 : Fin 3) (1 : ℂ) ∈ W
      have e : w 1 • Pi.single (1 : Fin 3) (1 : ℂ) =
          w - (1 / (hbar : ℂ) ^ 2) • (lOneLz hbar *ᵥ (lOneLz hbar *ᵥ w)) := by
        ext j
        fin_cases j <;>
          simp [lOneLz, dotProduct, Fin.sum_univ_three, h21, h01] <;>
          field_simp <;> ring
      rw [e]
      exact W.sub_mem hw (W.smul_mem _ h2)
    · change w 2 • Pi.single (2 : Fin 3) (1 : ℂ) ∈ W
      have e : w 2 • Pi.single (2 : Fin 3) (1 : ℂ) =
          (1 / (2 * (hbar : ℂ) ^ 2)) • (lOneLz hbar *ᵥ (lOneLz hbar *ᵥ w)) -
            (1 / (2 * (hbar : ℂ))) • (lOneLz hbar *ᵥ w) := by
        ext j
        fin_cases j <;>
          simp [lOneLz, dotProduct, Fin.sum_univ_three, h02, h12] <;>
          field_simp <;> ring
      rw [e]
      exact W.sub_mem (W.smul_mem _ h2) (W.smul_mem _ h1)
  -- `Lx` moves between neighbouring basis vectors.
  have hx0 : lOneLx hbar *ᵥ Pi.single 0 1 =
      ((hbar : ℂ) / ((Real.sqrt 2 : ℝ) : ℂ)) • Pi.single 1 1 := by
    ext j
    fin_cases j <;>
      simp [lOneLx, Matrix.mulVec, dotProduct, Fin.sum_univ_three, h10, h20, h21, h01]
  have hx2 : lOneLx hbar *ᵥ Pi.single 2 1 =
      ((hbar : ℂ) / ((Real.sqrt 2 : ℝ) : ℂ)) • Pi.single 1 1 := by
    ext j
    fin_cases j <;>
      simp [lOneLx, Matrix.mulVec, dotProduct, Fin.sum_univ_three, h21, h01, h02, h12]
  have hx1 : lOneLx hbar *ᵥ Pi.single 1 1 =
      ((hbar : ℂ) / ((Real.sqrt 2 : ℝ) : ℂ)) • (Pi.single 0 1 + Pi.single 2 1) := by
    ext j
    fin_cases j <;>
      simp [lOneLx, Matrix.mulVec, dotProduct, Fin.sum_univ_three, h10, h20, h21, h01, h02, h12]
  obtain ⟨v, hvW, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  obtain ⟨i, hi⟩ := exists_apply_ne_zero hv0
  have hei : Pi.single i (1 : ℂ) ∈ W := (W.smul_mem_iff hi).mp (hproj v hvW i)
  have he1 : Pi.single (1 : Fin 3) (1 : ℂ) ∈ W := by
    fin_cases i
    · refine (W.smul_mem_iff hc).mp ?_
      rw [← hx0]
      exact hx _ hei
    · exact hei
    · refine (W.smul_mem_iff hc).mp ?_
      rw [← hx2]
      exact hx _ hei
  have hw : ((hbar : ℂ) / ((Real.sqrt 2 : ℝ) : ℂ)) • (Pi.single 0 1 + Pi.single 2 1) ∈ W := by
    rw [← hx1]
    exact hx _ he1
  have hw0 := hproj _ hw 0
  have hw2 := hproj _ hw 2
  simp only [Pi.smul_apply, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne h02,
    Pi.single_eq_of_ne h20, add_zero, zero_add, smul_eq_mul, mul_one] at hw0 hw2
  apply eq_top_of_forall_single_mem
  intro j
  fin_cases j
  · exact (W.smul_mem_iff hc).mp hw0
  · exact he1
  · exact (W.smul_mem_iff hc).mp hw2

/-- Carrier dimensions `2 * l + 1`: the `l = 0, 1/2, 1` representations act irreducibly
(`lZero_irreducible`, `spinHalf_irreducible`, `lOne_irreducible`) on `Fin 1 → ℂ`,
`Fin 2 → ℂ` and `Fin 3 → ℂ`, of dimensions `1, 2, 3` (`Module.finrank_fin_fun`). -/
lemma angularMomentum_rep_dimensions :
    Module.finrank ℂ (Fin 1 → ℂ) = 1 ∧ Module.finrank ℂ (Fin 2 → ℂ) = 2 ∧
      Module.finrank ℂ (Fin 3 → ℂ) = 3 :=
  ⟨Module.finrank_fin_fun ℂ, Module.finrank_fin_fun ℂ, Module.finrank_fin_fun ℂ⟩

/-! ## C. Rigid rotor and spherical harmonics -/

/-- Rigid-rotor energy `E_J = hbar ^ 2 * J * (J + 1) / (2 * I)` for a moment of inertia
`I ≠ 0`; at `I = 0` the division returns the junk value `0`. -/
noncomputable def rigidRotorEnergy (hbar I : ℝ) (J : ℕ) : ℝ :=
  hbar ^ 2 * ((J * (J + 1) : ℕ) : ℝ) / (2 * I)

/-- Spherical harmonic `Y_00 = 1 / sqrt (4 * pi)` (constant). -/
noncomputable def sphericalHarmonic00 (_θ _φ : ℝ) : ℂ := 1 / Real.sqrt (4 * Real.pi)

/-- Spherical harmonic `Y_10 = sqrt (3 / (4 * pi)) * cos θ`. -/
noncomputable def sphericalHarmonic10 (θ _φ : ℝ) : ℂ :=
  Real.sqrt (3 / (4 * Real.pi)) * Real.cos θ

/-- Rigid-rotor level spacing: `E_{J+1} - E_J = hbar^2 * (J+1) / I`. -/
theorem rigidRotorEnergy_spacing {hbar I : ℝ} (hI : I ≠ 0) (J : ℕ) :
    rigidRotorEnergy hbar I (J + 1) - rigidRotorEnergy hbar I J =
      hbar ^ 2 * ((J + 1 : ℕ) : ℝ) / I := by
  have h2I : (2 : ℝ) * I ≠ 0 := mul_ne_zero (by norm_num) hI
  unfold rigidRotorEnergy <;> push_cast <;> field_simp [hI, h2I] <;> ring

/-- Rigid-rotor degeneracy: the magnetic quantum numbers `m ∈ {-J, ..., J}` number
`2 * J + 1`; a case of Mathlib's `Int.card_Icc`. -/
lemma rigidRotorMagnetic_count (J : ℕ) :
    (Finset.Icc (-(J : ℤ)) (J : ℤ)).card = 2 * J + 1 := by
  rw [Int.card_Icc]
  omega

/-- In the l = 1 representation, `Lz` has eigenvalues `+hbar, 0, -hbar` on the
standard basis (the `m = +1, 0, -1` spherical-harmonic channels). -/
theorem l1_Lz_eigenvalues (hbar : ℝ) :
    lOneLz hbar *ᵥ Pi.single 0 1 = (hbar : ℂ) • Pi.single 0 1 ∧
    lOneLz hbar *ᵥ Pi.single 1 1 = 0 ∧
    lOneLz hbar *ᵥ Pi.single 2 1 = -(hbar : ℂ) • Pi.single 2 1 := by
  have h10 : (1 : Fin 3) ≠ 0 := by decide
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  refine ⟨?_, ?_, ?_⟩ <;> ext k <;>
    simp only [Matrix.mulVec, dotProduct] <;> fin_cases k <;>
    simp [lOneLz, Matrix.smul_apply, Pi.smul_apply, Pi.zero_apply,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Pi.single_eq_same, Pi.single_eq_of_ne, h10, h20, h21, h01, h02, h12,
      smul_eq_mul] <;>
    ring

/-- At the north pole, `Y_10 = sqrt 3 * Y_00`. -/
lemma sphericalHarmonic10_at_pole (φ : ℝ) :
    sphericalHarmonic10 0 φ = Real.sqrt 3 * sphericalHarmonic00 0 φ := by
  simp only [sphericalHarmonic10, sphericalHarmonic00, Real.cos_zero, mul_one]
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 3)]
  push_cast
  ring

/-- Rigid-rotor energy at `J = 1` is `hbar^2 / I`. -/
lemma rigidRotorEnergy_l1 {hbar I : ℝ} (hI : I ≠ 0) :
    rigidRotorEnergy hbar I 1 = hbar ^ 2 / I := by
  have h2I : (2 : ℝ) * I ≠ 0 := mul_ne_zero (by norm_num) hI
  unfold rigidRotorEnergy <;> norm_num <;> field_simp [hI, h2I] <;> ring

/-! ## D. Hydrogen-like atom -/

/-- Hydrogen-like radial function `R_10(r) = 2 * exp (-r)` (atomic units, Z = 1). -/
noncomputable def hydrogenRadial10 (r : ℝ) : ℝ := 2 * Real.exp (-r)

/-- Derivative of `R_10`: `R_10'(r) = -2 * exp (-r)`. -/
noncomputable def hydrogenRadial10' (r : ℝ) : ℝ := -2 * Real.exp (-r)

/-- Hydrogen-like radial function `R_20(r) = (1 / (2 * sqrt 2)) * (2 - r) * exp (-r / 2)`. -/
noncomputable def hydrogenRadial20 (r : ℝ) : ℝ :=
  (1 / (2 * Real.sqrt 2)) * (2 - r) * Real.exp (-r / 2)

/-- Derivative of `R_20`. -/
noncomputable def hydrogenRadial20' (r : ℝ) : ℝ :=
  (1 / (2 * Real.sqrt 2)) * Real.exp (-r / 2) * (r / 2 - 2)

/-- Second derivative of `R_20`. -/
noncomputable def hydrogenRadial20'' (r : ℝ) : ℝ :=
  (1 / (2 * Real.sqrt 2)) * Real.exp (-r / 2) * (-r / 4 + 3 / 2)

/-- Hydrogen-like radial function `R_21(r) = (1 / (2 * sqrt 6)) * r * exp (-r / 2)`. -/
noncomputable def hydrogenRadial21 (r : ℝ) : ℝ :=
  (1 / (2 * Real.sqrt 6)) * r * Real.exp (-r / 2)

/-- Derivative of `R_21`. -/
noncomputable def hydrogenRadial21' (r : ℝ) : ℝ :=
  (1 / (2 * Real.sqrt 6)) * Real.exp (-r / 2) * (1 - r / 2)

/-- Second derivative of `R_21`. -/
noncomputable def hydrogenRadial21'' (r : ℝ) : ℝ :=
  (1 / (2 * Real.sqrt 6)) * Real.exp (-r / 2) * (r / 4 - 1)

/-- Radial residual: `-1/2 * R'' - (1/r) * R' + (l*(l+1)/(2*r^2) - Z/r) * R`.
The eigen-equation is `radialResidual Z l R R' R'' r = E * R`. -/
noncomputable def radialResidual (Z l R R' R'' r : ℝ) : ℝ :=
  -1 / 2 * R'' - (1 / r) * R' + (l * (l + 1) / (2 * r ^ 2) - Z / r) * R

/-- Hydrogen-like energy `E_n = -(Z ^ 2 * R) / n ^ 2` for the principal quantum number
`n : ℕ+` (there is no level `n = 0`), with `R` the Rydberg energy. -/
noncomputable def hydrogenEnergy (Z R : ℝ) (n : ℕ+) : ℝ :=
  -(Z ^ 2 * R) / ((n : ℕ) : ℝ) ^ 2

/-- Rydberg line wavenumber `R * Z ^ 2 * (1 / n1 ^ 2 - 1 / n2 ^ 2)` between the levels with
principal quantum numbers `n1 n2 : ℕ+`, with `R` the Rydberg constant as a wavenumber. -/
noncomputable def rydbergWavenumber (R Z : ℝ) (n1 n2 : ℕ+) : ℝ :=
  R * Z ^ 2 * (1 / ((n1 : ℕ) : ℝ) ^ 2 - 1 / ((n2 : ℕ) : ℝ) ^ 2)

/-- Hydrogen energy scaling: `E_n = E_1 / n^2`. -/
theorem hydrogenEnergy_scaling (Z R : ℝ) (n : ℕ+) :
    hydrogenEnergy Z R n = hydrogenEnergy Z R 1 / ((n : ℕ) : ℝ) ^ 2 := by
  have hn' : ((n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast n.ne_zero
  unfold hydrogenEnergy
  simp

/-- Hydrogen degeneracy by counting: `sum_{l<n} (2l+1) = n^2`. -/
theorem hydrogen_degeneracy (n : ℕ) :
    ∑ l ∈ Finset.range n, (2 * l + 1) = n ^ 2 := by
  induction n with
  | zero => decide
  | succ k ih => rw [Finset.sum_range_succ, ih] <;> ring

/-- With spin, the degeneracy is `2 * n^2`. -/
lemma hydrogen_degeneracy_spin (n : ℕ) :
    2 * (∑ l ∈ Finset.range n, (2 * l + 1)) = 2 * n ^ 2 := by
  rw [hydrogen_degeneracy]

/-- 1s eigen-equation, algebraic form: with `R'' = R` and `R' = -R`, the radial
residual at `Z = 1, l = 0` is `(-1/2) * R`. -/
theorem radialResidual_1s {r : ℝ} (hr : r ≠ 0) :
    radialResidual 1 0 (hydrogenRadial10 r) (hydrogenRadial10' r)
      (hydrogenRadial10 r) r = (-1 / 2) * hydrogenRadial10 r := by
  have hr2 : (2 : ℝ) * r ^ 2 ≠ 0 := mul_ne_zero (by norm_num) (by positivity)
  unfold radialResidual hydrogenRadial10 hydrogenRadial10' <;>
    field_simp [hr, hr2] <;> ring

/-- 2s eigen-equation, algebraic form: the radial residual at `Z = 1, l = 0`
is `(-1/8) * R`. -/
theorem radialResidual_2s {r : ℝ} (hr : r ≠ 0) :
    radialResidual 1 0 (hydrogenRadial20 r) (hydrogenRadial20' r)
      (hydrogenRadial20'' r) r = (-1 / 8) * hydrogenRadial20 r := by
  have hsqrt2 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have h2s : (2 : ℝ) * Real.sqrt 2 ≠ 0 := mul_ne_zero (by norm_num) hsqrt2
  have hr2 : (2 : ℝ) * r ^ 2 ≠ 0 := mul_ne_zero (by norm_num) (by positivity)
  unfold radialResidual hydrogenRadial20 hydrogenRadial20' hydrogenRadial20'' <;>
    field_simp [hr, hr2, h2s] <;> ring

/-- 2p eigen-equation, algebraic form: the radial residual at `Z = 1, l = 1`
is `(-1/8) * R`. -/
theorem radialResidual_2p {r : ℝ} (hr : r ≠ 0) :
    radialResidual 1 1 (hydrogenRadial21 r) (hydrogenRadial21' r)
      (hydrogenRadial21'' r) r = (-1 / 8) * hydrogenRadial21 r := by
  have hsqrt6 : Real.sqrt 6 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have h2s : (2 : ℝ) * Real.sqrt 6 ≠ 0 := mul_ne_zero (by norm_num) hsqrt6
  have hr2 : (2 : ℝ) * r ^ 2 ≠ 0 := mul_ne_zero (by norm_num) (by positivity)
  unfold radialResidual hydrogenRadial21 hydrogenRadial21' hydrogenRadial21'' <;>
    field_simp [hr, hr2, h2s] <;> ring

/-- 1s derivatives: `R_10' = -R_10` and `(R_10')' = R_10`, via `HasDerivAt`. -/
lemma hydrogenRadial_deriv_1s (r : ℝ) :
    HasDerivAt hydrogenRadial10 (hydrogenRadial10' r) r ∧
    HasDerivAt hydrogenRadial10' (hydrogenRadial10 r) r := by
  refine ⟨?_, ?_⟩
  · have h1 := (hasDerivAt_id r).neg
    have h2 := h1.exp
    have h3 := h2.const_mul 2
    simp only [hydrogenRadial10, hydrogenRadial10']
    convert h3 using 1
    · funext y
      simp only [hydrogenRadial10, Pi.neg_apply, id_eq] <;> ring
    · simp only [Pi.neg_apply, id_eq]
      ring
  · have h1 := (hasDerivAt_id r).neg
    have h2 := h1.exp
    have h3 := h2.const_mul (-2)
    simp only [hydrogenRadial10', hydrogenRadial10]
    convert h3 using 1
    · funext y
      simp only [hydrogenRadial10', Pi.neg_apply, id_eq] <;> ring
    · simp only [Pi.neg_apply, id_eq]
      ring

/-- 2s derivatives, via `HasDerivAt`. -/
lemma hydrogenRadial_deriv_2s (r : ℝ) :
    HasDerivAt hydrogenRadial20 (hydrogenRadial20' r) r ∧
    HasDerivAt hydrogenRadial20' (hydrogenRadial20'' r) r := by
  refine ⟨?_, ?_⟩
  · have h2const : HasDerivAt (fun _ : ℝ => (2 : ℝ)) 0 r := hasDerivAt_const _ _
    have hid := hasDerivAt_id r
    have h2r := h2const.sub hid
    have hcm := h2r.const_mul (1 * (2 * Real.sqrt 2)⁻¹)
    have hneg := hid.neg
    have hhalfconst : HasDerivAt (fun _ : ℝ => ((2 : ℝ))⁻¹) 0 r :=
      hasDerivAt_const _ _
    have hhalf := hneg.mul hhalfconst
    have hexp := hhalf.exp
    have hfin := hcm.mul hexp
    simp only [hydrogenRadial20, hydrogenRadial20', div_eq_mul_inv]
    convert hfin using 1
    · funext y
      simp only [hydrogenRadial20, div_eq_mul_inv, Pi.mul_apply, Pi.sub_apply,
        Pi.neg_apply, id_eq] <;> ring
    · simp only [Pi.mul_apply, Pi.sub_apply, Pi.neg_apply, id_eq]
      ring
  · have hneg := (hasDerivAt_id r).neg
    have hhalfconst : HasDerivAt (fun _ : ℝ => ((2 : ℝ))⁻¹) 0 r :=
      hasDerivAt_const _ _
    have hhalf := hneg.mul hhalfconst
    have hexp := hhalf.exp
    have hce := hexp.const_mul (1 * (2 * Real.sqrt 2)⁻¹)
    have hid2 := hasDerivAt_id r
    have hhalf2 := hid2.mul hhalfconst
    have h2const : HasDerivAt (fun _ : ℝ => (2 : ℝ)) 0 r := hasDerivAt_const _ _
    have hsub := hhalf2.sub h2const
    have hfin := hce.mul hsub
    simp only [hydrogenRadial20', hydrogenRadial20'', div_eq_mul_inv]
    convert hfin using 1
    · funext y
      simp only [hydrogenRadial20', div_eq_mul_inv, Pi.mul_apply, Pi.sub_apply,
        Pi.neg_apply, id_eq] <;> ring
    · simp only [Pi.mul_apply, Pi.sub_apply, Pi.neg_apply, id_eq]
      ring

/-- 2p derivatives, via `HasDerivAt`. -/
lemma hydrogenRadial_deriv_2p (r : ℝ) :
    HasDerivAt hydrogenRadial21 (hydrogenRadial21' r) r ∧
    HasDerivAt hydrogenRadial21' (hydrogenRadial21'' r) r := by
  refine ⟨?_, ?_⟩
  · have hid := hasDerivAt_id r
    have hcm := hid.const_mul (1 * (2 * Real.sqrt 6)⁻¹)
    have hneg := hid.neg
    have hhalfconst : HasDerivAt (fun _ : ℝ => ((2 : ℝ))⁻¹) 0 r :=
      hasDerivAt_const _ _
    have hhalf := hneg.mul hhalfconst
    have hexp := hhalf.exp
    have hfin := hcm.mul hexp
    simp only [hydrogenRadial21, hydrogenRadial21', div_eq_mul_inv]
    convert hfin using 1
    · funext y
      simp only [hydrogenRadial21, div_eq_mul_inv, Pi.mul_apply, Pi.neg_apply,
        id_eq] <;> ring
    · simp only [Pi.mul_apply, Pi.neg_apply, id_eq]
      ring
  · have hneg := (hasDerivAt_id r).neg
    have hhalfconst : HasDerivAt (fun _ : ℝ => ((2 : ℝ))⁻¹) 0 r :=
      hasDerivAt_const _ _
    have hhalf := hneg.mul hhalfconst
    have hexp := hhalf.exp
    have hce := hexp.const_mul (1 * (2 * Real.sqrt 6)⁻¹)
    have hid2 := hasDerivAt_id r
    have hhalf2 := hid2.mul hhalfconst
    have h1const : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 r := hasDerivAt_const _ _
    have hsub := h1const.sub hhalf2
    have hfin := hce.mul hsub
    simp only [hydrogenRadial21', hydrogenRadial21'', div_eq_mul_inv]
    convert hfin using 1
    · funext y
      simp only [hydrogenRadial21', div_eq_mul_inv, Pi.mul_apply, Pi.sub_apply,
        Pi.neg_apply, id_eq] <;> ring
    · simp only [Pi.mul_apply, Pi.sub_apply, Pi.neg_apply, id_eq]
      ring

/-- Rydberg lines are positive for `n1 < n2` (emission, `n2 -> n1`); compare Physlib's
`QuantumMechanics.HydrogenAtom.transitionFrequency_pos`. -/
theorem rydbergWavenumber_pos {R Z : ℝ} (hR : 0 < R) (hZ : Z ≠ 0) {n1 n2 : ℕ+}
    (h12 : n1 < n2) :
    0 < rydbergWavenumber R Z n1 n2 := by
  unfold rydbergWavenumber
  have hn1' : (0 : ℝ) < ((n1 : ℕ) : ℝ) := by exact_mod_cast n1.pos
  have h12' : ((n1 : ℕ) : ℝ) < ((n2 : ℕ) : ℝ) := by exact_mod_cast h12
  have hn2' : (0 : ℝ) < ((n2 : ℕ) : ℝ) := lt_trans hn1' h12'
  have hmul := mul_pos (sub_pos.mpr h12') (add_pos hn1' hn2')
  have hsq : ((n1 : ℕ) : ℝ) ^ 2 < ((n2 : ℕ) : ℝ) ^ 2 := by nlinarith [hmul]
  have hA : (0 : ℝ) < ((n1 : ℕ) : ℝ) ^ 2 := by positivity
  have hB : (0 : ℝ) < ((n2 : ℕ) : ℝ) ^ 2 := by positivity
  have hdiv := (one_div_lt_one_div hB hA).mpr hsq
  have hsub := sub_pos.mpr hdiv
  have hZ2 : (0 : ℝ) < Z ^ 2 := by positivity
  exact mul_pos (mul_pos hR hZ2) hsub

/-- Bridge to Physlib's Bohr levels: for a three-dimensional `QuantumMechanics.HydrogenAtom`,
Physlib's level `n` (counted from `0`) is the level with principal quantum number `n + 1`, and
Physlib's Rydberg energy is `Z ^ 2 * R` here (the nuclear charge is part of Physlib's coupling
`k`, so `Z = 1`). -/
lemma energyLevel_eq_hydrogenEnergy (H : QuantumMechanics.HydrogenAtom) (hd : H.d = 3)
    (n : ℕ) : H.energyLevel n = hydrogenEnergy 1 H.rydbergEnergy n.succPNat := by
  rw [QuantumMechanics.HydrogenAtom.energyLevel_eq, QuantumMechanics.HydrogenAtom.levelIndex_eq,
    hd, hydrogenEnergy, Nat.succPNat_coe, Nat.cast_succ]
  norm_num

/-- Bridge to Physlib's Rydberg formula: for a three-dimensional
`QuantumMechanics.HydrogenAtom`, the inverse wavelength of the transition from Physlib's level
`n₂` to `n₁` is `rydbergWavenumber` between the principal quantum numbers `n₂ + 1` and
`n₁ + 1`, with the Rydberg constant `R_ν / c` (`Z = 1`, as in
`energyLevel_eq_hydrogenEnergy`). -/
lemma wavelength_inv_eq_rydbergWavenumber (H : QuantumMechanics.HydrogenAtom) (hd : H.d = 3)
    (c : SpeedOfLight) (n₁ n₂ : ℕ) :
    (H.wavelength c n₁ n₂)⁻¹ =
      rydbergWavenumber (H.rydbergFrequency / c) 1 n₁.succPNat n₂.succPNat := by
  rw [QuantumMechanics.HydrogenAtom.wavelength_inv, QuantumMechanics.HydrogenAtom.levelIndex_eq,
    QuantumMechanics.HydrogenAtom.levelIndex_eq, hd, rydbergWavenumber, Nat.succPNat_coe,
    Nat.succPNat_coe, Nat.cast_succ, Nat.cast_succ]
  norm_num

/-! ## E. Filling heuristics -/

/-- Hund's rule (empirical heuristic, counting form): unpaired electrons for
`e` electrons in a shell of degeneracy `g`. Meaningful for `e ≤ 2 * g`, the capacity of the
shell; for larger `e` the truncated subtraction returns `0`. -/
noncomputable def hundUnpaired (e g : ℕ) : ℕ := min e (2 * g - e)

/-- Aufbau shell capacity: filling shells `1..N` with `2 * n^2` electrons each
holds `N * (N+1) * (2*N+1) / 3` electrons (an empirical filling rule, not a
derived theorem about real atoms). -/
lemma aufbau_shellCapacity (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, 2 * ((n : ℝ)) ^ 2 =
      (N : ℝ) * ((N : ℝ) + 1) * (2 * (N : ℝ) + 1) / 3 := by
  induction N with
  | zero =>
      rw [Finset.Icc_eq_empty (by norm_num : ¬ (1 : ℕ) ≤ 0), Finset.sum_empty] <;>
        norm_num
  | succ k ih =>
      have hset : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hmem : (k + 1) ∉ Finset.Icc 1 k := by
        simp only [Finset.mem_Icc]
        omega
      rw [hset, Finset.sum_insert hmem, ih] <;> push_cast <;> ring

/-- Hund's unpaired count never exceeds the shell degeneracy. -/
lemma hundUnpaired_le_g {e g : ℕ} (he : e ≤ 2 * g) : hundUnpaired e g ≤ g := by
  unfold hundUnpaired <;> omega

end PhyslibExt.Chemistry.AngularMomentumRotorHydrogen
