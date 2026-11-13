/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Tactic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Order.Interval.Finset.Basic

@[expose] public section

/-!
# CH38: Angular momentum, rigid rotor and hydrogen-like atom

Finite-dimensional angular-momentum irreps (explicit `l = 0, 1/2, 1` instances),
the rigid rotor, hydrogen-like radial functions, the Rydberg formula, and the
Aufbau/Hund filling heuristics.

## Scope and non-claims

* The GENERAL classification of finite-dimensional irreps of the
  angular-momentum algebra is NOT proved; the three instances `l = 0, 1/2, 1`
  are (explicit matrices, commutators, Casimir values, dimensions `2 * l + 1`).
  `hbar` is kept symbolic (atomic units would set it to 1; we do not).
* Spherical-harmonic completeness on the sphere is DEFERRED. The Laplacian
  eigen-equation for `Y_lm` is NOT formalized (it needs the differential
  operator domain); the pinned content is the `Lz` eigenvalues in the `l = 1`
  matrix representation plus the `Y_10 / Y_00` pole ratio.
* The hydrogen eigen-equation is verified in this exact sense: derivative
  values are proved by `HasDerivAt`, and substituted into the radial equation
  they give the stated energies (the `radialResidual_*` identities, pure
  algebra). Atomic units (`a0 = 1`) for the radial functions; `Z` enters the
  energy formula only. `R` in `hydrogenEnergy` is the Rydberg constant as
  given (reduced mass folded into it); fine structure is ignored.
* Aufbau and Hund are LABELLED empirical heuristics (counting rules, not
  derived theorems about real atoms).

## Model boundary

MOD (rigid rotor, nonrelativistic one-electron atom, Born-Oppenheimer); MC;
EF/heuristic (Aufbau, Hund).

## Reuse-verified exception

This module is created under the lane rule's reuse-verified exception: it
depends ONLY on pinned Mathlib (matrices, `HasDerivAt`, real trigonometry)
and on no `CH36`/`CH37`/`MF02`/`MF03`/`MF05`/`MF10` file, nor on any
`MathlibExt`/`PhyslibExt` module owned by another roadmap module.
-/

namespace PhyslibExt.Chemistry.AngularMomentumRotorHydrogen

open scoped BigOperators
open scoped Matrix

/-- Commutator `[A, B] = A * B - B * A`. -/
noncomputable def commutator {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  A * B - B * A

/-- Spin-1/2 Pauli matrices. -/
noncomputable def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- Spin-1/2 Pauli matrices. -/
noncomputable def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- Spin-1/2 Pauli matrices. -/
noncomputable def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- Spin-1/2 angular momentum `Jx = (hbar / 2) * sigma_x`. -/
noncomputable def spinHalfJx (hbar : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((hbar : ℂ) / 2) • pauliX

/-- Spin-1/2 angular momentum `Jy = (hbar / 2) * sigma_y`. -/
noncomputable def spinHalfJy (hbar : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((hbar : ℂ) / 2) • pauliY

/-- Spin-1/2 angular momentum `Jz = (hbar / 2) * sigma_z`. -/
noncomputable def spinHalfJz (hbar : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((hbar : ℂ) / 2) • pauliZ

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

/-- Rigid-rotor energy `E_J = hbar ^ 2 * J * (J + 1) / (2 * I)`. -/
noncomputable def rigidRotorEnergy (hbar I : ℝ) (J : ℕ) : ℝ :=
  hbar ^ 2 * ((J * (J + 1) : ℕ) : ℝ) / (2 * I)

/-- Spherical harmonic `Y_00 = 1 / sqrt (4 * pi)` (constant). -/
noncomputable def sphericalHarmonic00 (_θ _φ : ℝ) : ℂ := 1 / Real.sqrt (4 * Real.pi)

/-- Spherical harmonic `Y_10 = sqrt (3 / (4 * pi)) * cos θ`. -/
noncomputable def sphericalHarmonic10 (θ _φ : ℝ) : ℂ :=
  Real.sqrt (3 / (4 * Real.pi)) * Real.cos θ

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

/-- Hydrogen-like energy `E_n = -(Z ^ 2 * R) / n ^ 2`. -/
noncomputable def hydrogenEnergy (Z R : ℝ) (n : ℕ) : ℝ :=
  -(Z ^ 2 * R) / ((n : ℝ)) ^ 2

/-- Rydberg line wavenumber `R * Z ^ 2 * (1 / n1 ^ 2 - 1 / n2 ^ 2)`. -/
noncomputable def rydbergWavenumber (R Z : ℝ) (n1 n2 : ℕ) : ℝ :=
  R * Z ^ 2 * (1 / ((n1 : ℝ)) ^ 2 - 1 / ((n2 : ℝ)) ^ 2)

/-- Hund's rule (empirical heuristic, counting form): unpaired electrons for
`e` electrons in a shell of degeneracy `g`. -/
noncomputable def hundUnpaired (e g : ℕ) : ℕ := min e (2 * g - e)

/-- Spin-1/2 angular-momentum commutators `[Jx, Jy] = i * hbar * Jz` (and cyclic). -/
theorem spinHalf_commutators (hbar : ℝ) :
    commutator (spinHalfJx hbar) (spinHalfJy hbar) =
      (Complex.I * (hbar : ℂ)) • spinHalfJz hbar ∧
    commutator (spinHalfJy hbar) (spinHalfJz hbar) =
      (Complex.I * (hbar : ℂ)) • spinHalfJx hbar ∧
    commutator (spinHalfJz hbar) (spinHalfJx hbar) =
      (Complex.I * (hbar : ℂ)) • spinHalfJy hbar := by
  refine ⟨?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [commutator, spinHalfJx, spinHalfJy, spinHalfJz, pauliX, pauliY, pauliZ,
      Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, pow_two, Complex.I_mul_I] <;>
    ring_nf <;> (try simp only [pow_two, Complex.I_mul_I]) <;>
    ring

/-- Spin-1/2 Casimir: `J^2 = (3/4) * hbar^2 * 1`. -/
theorem spinHalf_casimir (hbar : ℝ) :
    spinHalfJx hbar ^ 2 + spinHalfJy hbar ^ 2 + spinHalfJz hbar ^ 2 =
      ((3 / 4 : ℂ) * (hbar : ℂ) ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinHalfJx, spinHalfJy, spinHalfJz, pauliX, pauliY, pauliZ,
      Matrix.add_apply, Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply,
      Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, pow_two,
      Complex.I_mul_I] <;>
    ring_nf <;> (try simp only [pow_two, Complex.I_mul_I]) <;>
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

/-- Representation dimensions: 1, 2, 3 for l = 0, 1/2, 1 (i.e. `2l + 1`). -/
theorem angularMomentum_rep_dimensions :
    Module.finrank ℂ (Fin 1 → ℂ) = 1 ∧ Module.finrank ℂ (Fin 2 → ℂ) = 2 ∧
      Module.finrank ℂ (Fin 3 → ℂ) = 3 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [Module.finrank_pi, Module.finrank_self]

/-- Rigid-rotor level spacing: `E_{J+1} - E_J = hbar^2 * (J+1) / I`. -/
theorem rigidRotorEnergy_spacing {hbar I : ℝ} (hI : I ≠ 0) (J : ℕ) :
    rigidRotorEnergy hbar I (J + 1) - rigidRotorEnergy hbar I J =
      hbar ^ 2 * ((J + 1 : ℕ) : ℝ) / I := by
  have h2I : (2 : ℝ) * I ≠ 0 := mul_ne_zero (by norm_num) hI
  unfold rigidRotorEnergy <;> push_cast <;> field_simp [hI, h2I] <;> ring

/-- Rigid-rotor degeneracy: the magnetic quantum numbers `m ∈ {-J, ..., J}`
number `2 * J + 1`. -/
theorem rigidRotorMagnetic_count (J : ℕ) :
    (Finset.Icc (-(J : ℤ)) (J : ℤ)).card = 2 * J + 1 := by
  induction J with
  | zero => decide
  | succ k ih =>
      have hJ : (-(((k + 1 : ℕ)) : ℤ)) = (-(k : ℤ)) - 1 := by simp <;> ring
      have hJ2 : (((k + 1 : ℕ)) : ℤ) = (k : ℤ) + 1 := by simp
      rw [hJ, hJ2]
      have hset : Finset.Icc (-(k : ℤ) - 1) ((k : ℤ) + 1) =
          insert (-(k : ℤ) - 1)
            (insert ((k : ℤ) + 1) (Finset.Icc (-(k : ℤ)) (k : ℤ))) := by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [hset, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, ih]
      all_goals (try simp only [Finset.mem_Icc, Finset.mem_insert])
      all_goals omega

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
theorem sphericalHarmonic10_at_pole (φ : ℝ) :
    sphericalHarmonic10 0 φ = Real.sqrt 3 * sphericalHarmonic00 0 φ := by
  simp only [sphericalHarmonic10, sphericalHarmonic00, Real.cos_zero, mul_one]
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 3)]
  push_cast
  ring

/-- Rigid-rotor energy at `J = 1` is `hbar^2 / I`. -/
theorem rigidRotorEnergy_l1 {hbar I : ℝ} (hI : I ≠ 0) :
    rigidRotorEnergy hbar I 1 = hbar ^ 2 / I := by
  have h2I : (2 : ℝ) * I ≠ 0 := mul_ne_zero (by norm_num) hI
  unfold rigidRotorEnergy <;> norm_num <;> field_simp [hI, h2I] <;> ring

/-- Hydrogen energy scaling: `E_n = E_1 / n^2`. -/
theorem hydrogenEnergy_scaling (Z R : ℝ) {n : ℕ} (hn : n ≠ 0) :
    hydrogenEnergy Z R n = hydrogenEnergy Z R 1 / (n : ℝ) ^ 2 := by
  have hn' : ((n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hn
  have hn2 : ((n : ℕ) : ℝ) ^ 2 ≠ 0 := by positivity
  unfold hydrogenEnergy <;> field_simp [hn', hn2] <;> ring

/-- Hydrogen degeneracy by counting: `sum_{l<n} (2l+1) = n^2`. -/
theorem hydrogen_degeneracy (n : ℕ) :
    ∑ l ∈ Finset.range n, (2 * l + 1) = n ^ 2 := by
  induction n with
  | zero => decide
  | succ k ih => rw [Finset.sum_range_succ, ih] <;> ring

/-- With spin, the degeneracy is `2 * n^2`. -/
theorem hydrogen_degeneracy_spin (n : ℕ) :
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
theorem hydrogenRadial_deriv_1s (r : ℝ) :
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
theorem hydrogenRadial_deriv_2s (r : ℝ) :
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
theorem hydrogenRadial_deriv_2p (r : ℝ) :
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

/-- Rydberg lines are positive for `n1 < n2` (emission, `n2 -> n1`). -/
theorem rydbergWavenumber_pos {R Z : ℝ} (hR : 0 < R) (hZ : Z ≠ 0) {n1 n2 : ℕ}
    (hn1 : 0 < n1) (h12 : n1 < n2) :
    0 < rydbergWavenumber R Z n1 n2 := by
  unfold rydbergWavenumber
  have hn1' : (0 : ℝ) < (n1 : ℝ) := by exact_mod_cast hn1
  have h12' : (n1 : ℝ) < (n2 : ℝ) := by exact_mod_cast h12
  have hn2' : (0 : ℝ) < (n2 : ℝ) := lt_trans hn1' h12'
  have hmul := mul_pos (sub_pos.mpr h12') (add_pos hn1' hn2')
  have hsq : (n1 : ℝ) ^ 2 < (n2 : ℝ) ^ 2 := by nlinarith [hmul]
  have hA : (0 : ℝ) < (n1 : ℝ) ^ 2 := by positivity
  have hB : (0 : ℝ) < (n2 : ℝ) ^ 2 := by positivity
  have hdiv := (one_div_lt_one_div hB hA).mpr hsq
  have hsub := sub_pos.mpr hdiv
  have hZ2 : (0 : ℝ) < Z ^ 2 := by positivity
  exact mul_pos (mul_pos hR hZ2) hsub

/-- Aufbau shell capacity: filling shells `1..N` with `2 * n^2` electrons each
holds `N * (N+1) * (2*N+1) / 3` electrons (an empirical filling rule, not a
derived theorem about real atoms). -/
theorem aufbau_shellCapacity (N : ℕ) :
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
theorem hundUnpaired_le_g {e g : ℕ} (he : e ≤ 2 * g) : hundUnpaired e g ≤ g := by
  unfold hundUnpaired <;> omega

end PhyslibExt.Chemistry.AngularMomentumRotorHydrogen
