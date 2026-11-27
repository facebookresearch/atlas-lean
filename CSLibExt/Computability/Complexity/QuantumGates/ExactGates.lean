/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Classes
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Exact Gaussian-rational gate exports

Canonical encodings of the exact gates used by the Atlas circuit model. The
five-gate Toffoli construction follows Barenco, Bennett, Cleve, DiVincenzo,
Margolus, Shor, Sleator, Smolin and Weinfurter, Elementary gates for quantum
computation, Physical Review A 52 (1995), Lemma 6.1. Only encodings and
well-formedness are proved here; gate-action lemmas are outside this file.
-/

@[expose] public section

namespace Cslib.Complexity.Classes.QuantumGates

set_option autoImplicit false

open scoped Matrix BigOperators

/-- A Gaussian rational encoded as a pair of rational encodings. -/
abbrev GRat := RatEnc × RatEnc

/-- Encode a rational number in Atlas `RatEnc` form. -/
def ratEncOfRat (q : ℚ) : RatEnc :=
  (if q < 0 then true else false, q.num.natAbs, q.den)

/-- Encode a Gaussian rational with real part `a` and imaginary part `b`. -/
def gaussRatEnc (a b : ℚ) : GRat :=
  (ratEncOfRat a, ratEncOfRat b)

private theorem ratEnc_den_ne (q : ℚ) : q.den ≠ 0 := Rat.den_nz q

private theorem ratEnc_den_cast_ne (q : ℚ) : ((q.den : ℕ) : ℚ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (ratEnc_den_ne q)

private theorem ratEnc_roundtrip_nonneg (q : ℚ) (h : ¬ q < 0) :
    ((q.num.natAbs : ℕ) : ℚ) / ((q.den : ℕ) : ℚ) = q := by
  have hq : 0 ≤ q := le_of_not_gt h
  have hnn : 0 ≤ q.num := Rat.num_nonneg.mpr hq
  have h1 : ((q.num.natAbs : ℕ) : ℤ) = q.num := Int.natAbs_of_nonneg hnn
  have hcast : ((q.num.natAbs : ℕ) : ℚ) = (q.num : ℚ) := by
    rw [← Int.cast_natCast, h1]
  rw [hcast]
  exact Rat.num_div_den q

private theorem ratEnc_roundtrip_neg (q : ℚ) (h : q < 0) :
    -(((q.num.natAbs : ℕ) : ℚ) / ((q.den : ℕ) : ℚ)) = q := by
  have hnum : q.num < 0 :=
    not_le.mp (mt Rat.num_nonneg.mp (not_le_of_gt h))
  have h1 : ((q.num.natAbs : ℕ) : ℤ) = -q.num := by
    rw [Int.natCast_natAbs, abs_of_neg hnum]
  have hcast : ((q.num.natAbs : ℕ) : ℚ) = -(q.num : ℚ) := by
    rw [← Int.cast_natCast, h1, Int.cast_neg]
  rw [hcast, neg_div, neg_neg]
  exact Rat.num_div_den q

/-- Decoding `ratEncOfRat` recovers the rational number. -/
theorem toRat_ratEncOfRat (q : ℚ) : toRat (ratEncOfRat q) = q := by
  by_cases h : q < 0
  · simpa [ratEncOfRat, toRat, h, neg_div, neg_one_mul, one_mul,
      Int.cast_neg, Int.cast_natCast, ratEnc_den_ne,
      ratEnc_den_cast_ne] using ratEnc_roundtrip_neg q h
  · simpa [ratEncOfRat, toRat, h, neg_div, neg_one_mul, one_mul,
      Int.cast_neg, Int.cast_natCast, ratEnc_den_ne,
      ratEnc_den_cast_ne] using ratEnc_roundtrip_nonneg q h

/-- Decoding a Gaussian-rational encoding recovers the complex number. -/
theorem toComplex_gaussRatEnc (a b : ℚ) :
    toComplex (gaussRatEnc a b) = ⟨(a : ℝ), (b : ℝ)⟩ := by
  simp [gaussRatEnc, toComplex, toRat_ratEncOfRat, Complex.ext_iff]

private theorem toComplex_gaussRatEnc_zero :
    toComplex (gaussRatEnc 0 0) = 0 := by
  simp [toComplex_gaussRatEnc, Complex.ext_iff]

private theorem toComplex_gaussRatEnc_one :
    toComplex (gaussRatEnc 1 0) = 1 := by
  simp [toComplex_gaussRatEnc, Complex.ext_iff]

/-- The complex matrix represented by a Gaussian-rational matrix. -/
def complexOfGRatMatrix {m n : Type*} (M : Matrix m n GRat) : Matrix m n ℂ :=
  fun i j => toComplex (M i j)

/-- The entries of a two-qubit Gaussian-rational matrix in Atlas row-major
order. -/
def entriesOf (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) GRat) :
    List (RatEnc × RatEnc) :=
  [M (0, 0) (0, 0), M (0, 0) (0, 1), M (0, 0) (1, 0), M (0, 0) (1, 1),
   M (0, 1) (0, 0), M (0, 1) (0, 1), M (0, 1) (1, 0), M (0, 1) (1, 1),
   M (1, 0) (0, 0), M (1, 0) (0, 1), M (1, 0) (1, 0), M (1, 0) (1, 1),
   M (1, 1) (0, 0), M (1, 1) (0, 1), M (1, 1) (1, 0), M (1, 1) (1, 1)]

/-- Atlas decoding of `entriesOf` gives the represented complex matrix. -/
theorem matrixOfEntries_entriesOf
    (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) GRat) :
    matrixOfEntries (entriesOf M) = complexOfGRatMatrix M := by
  ext p q
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  fin_cases p1 <;> fin_cases p2 <;> fin_cases q1 <;> fin_cases q2 <;> rfl

/-- An entry list produced by `entriesOf` has sixteen entries. -/
theorem entriesOf_length
    (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) GRat) :
    (entriesOf M).length = 16 := by
  rfl

private theorem mem_entry_den_ne_zero
    (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) GRat)
    (hM : ∀ p q, ∃ a b : ℚ, M p q = gaussRatEnc a b) (p q) :
    (M p q).1.2.2 ≠ 0 ∧ (M p q).2.2.2 ≠ 0 := by
  obtain ⟨a, b, hab⟩ := hM p q
  rw [hab]
  exact ⟨Rat.den_nz _, Rat.den_nz _⟩

/-- Every denominator in an entry list generated from Gaussian rationals is
nonzero. -/
theorem entriesOf_den_ne_zero
    (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) GRat)
    (hM : ∀ p q, ∃ a b : ℚ, M p q = gaussRatEnc a b) :
    ∀ e ∈ entriesOf M, e.1.2.2 ≠ 0 ∧ e.2.2.2 ≠ 0 := by
  intro e he
  unfold entriesOf at he
  simp at he
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals exact mem_entry_den_ne_zero M hM _ _

/-- Embed a one-qubit matrix on the first (low) qubit of a pair. -/
def onLow (U : Matrix (Fin 2) (Fin 2) GRat) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) GRat :=
  fun p q => if p.2 = q.2 then U p.1 q.1 else gaussRatEnc 0 0

/-- Embed a one-qubit matrix on the second (high) qubit of a pair. -/
def onHigh (U : Matrix (Fin 2) (Fin 2) GRat) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) GRat :=
  fun p q => if p.1 = q.1 then U p.2 q.2 else gaussRatEnc 0 0

/-- Controlled `U`, with the first qubit as control. -/
def ctrlLow (U : Matrix (Fin 2) (Fin 2) GRat) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) GRat :=
  fun p q =>
    if p.1 = 0 ∧ q.1 = 0 ∧ p.2 = q.2 then gaussRatEnc 1 0
    else if p.1 = 1 ∧ q.1 = 1 then U p.2 q.2
    else gaussRatEnc 0 0

/-- Controlled `U`, with the second qubit as control. -/
def ctrlHigh (U : Matrix (Fin 2) (Fin 2) GRat) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) GRat :=
  fun p q =>
    if p.2 = 0 ∧ q.2 = 0 ∧ p.1 = q.1 then gaussRatEnc 1 0
    else if p.2 = 1 ∧ q.2 = 1 then U p.1 q.1
    else gaussRatEnc 0 0

/-- The two-qubit swap matrix in Gaussian-rational form. -/
def swapMatrix : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) GRat :=
  fun p q => if p = (q.2, q.1) then gaussRatEnc 1 0 else gaussRatEnc 0 0

/-- The complex form of a low embedding is a Kronecker product. -/
theorem complexOfGRatMatrix_onLow (U : Matrix (Fin 2) (Fin 2) GRat) :
    complexOfGRatMatrix (onLow U) =
      Matrix.kronecker (complexOfGRatMatrix U) 1 := by
  ext p q
  simp only [complexOfGRatMatrix, onLow, Matrix.kronecker]
  by_cases h : p.2 = q.2 <;>
    simp [h, toComplex_gaussRatEnc_zero, complexOfGRatMatrix,
      Matrix.one_apply]

/-- The complex form of a high embedding is a Kronecker product. -/
theorem complexOfGRatMatrix_onHigh (U : Matrix (Fin 2) (Fin 2) GRat) :
    complexOfGRatMatrix (onHigh U) =
      Matrix.kronecker 1 (complexOfGRatMatrix U) := by
  ext p q
  simp only [complexOfGRatMatrix, onHigh, Matrix.kronecker]
  by_cases h : p.1 = q.1 <;>
    simp [h, toComplex_gaussRatEnc_zero, complexOfGRatMatrix,
      Matrix.one_apply]

/-- Decoding the entry list of the low embedding of `U` gives the Kronecker product `U ⊗ 1`. -/
theorem matrixOfEntries_onLow (U : Matrix (Fin 2) (Fin 2) GRat) :
    matrixOfEntries (entriesOf (onLow U)) =
      Matrix.kronecker (complexOfGRatMatrix U) 1 := by
  rw [matrixOfEntries_entriesOf, complexOfGRatMatrix_onLow]

/-- Decoding the entry list of the high embedding of `U` gives the Kronecker product `1 ⊗ U`. -/
theorem matrixOfEntries_onHigh (U : Matrix (Fin 2) (Fin 2) GRat) :
    matrixOfEntries (entriesOf (onHigh U)) =
      Matrix.kronecker 1 (complexOfGRatMatrix U) := by
  rw [matrixOfEntries_entriesOf, complexOfGRatMatrix_onHigh]

/-- A low embedding of a unitary is a well-formed Atlas gate. -/
theorem qGateWellFormed_onLow (U : Matrix (Fin 2) (Fin 2) GRat)
    (hU : star (complexOfGRatMatrix U) * complexOfGRatMatrix U = 1)
    {N i j : ℕ} (hij : i < j) (hjN : j < N) :
    QGateWellFormed N (i, j, entriesOf (onLow U)) := by
  refine ⟨hij, hjN, ?_⟩
  show star (matrixOfEntries (entriesOf (onLow U))) *
    matrixOfEntries (entriesOf (onLow U)) = 1
  rw [matrixOfEntries_onLow]
  have hUentry : ∀ a b : Fin 2,
      (star (complexOfGRatMatrix U) * complexOfGRatMatrix U) a b =
        (1 : Matrix (Fin 2) (Fin 2) ℂ) a b :=
    fun a b => congrFun (congrFun hU a) b
  simp [Matrix.mul_apply, Matrix.star_apply, complexOfGRatMatrix,
    Fin.sum_univ_two] at hUentry
  ext p q
  obtain ⟨a, b⟩ := p
  obtain ⟨c, d⟩ := q
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [Matrix.kronecker, complexOfGRatMatrix, Matrix.mul_apply,
      Matrix.star_apply, Fintype.sum_prod_type, Fin.sum_univ_two, hUentry]

/-- A high embedding of a unitary is a well-formed Atlas gate. -/
theorem qGateWellFormed_onHigh (U : Matrix (Fin 2) (Fin 2) GRat)
    (hU : star (complexOfGRatMatrix U) * complexOfGRatMatrix U = 1)
    {N i j : ℕ} (hij : i < j) (hjN : j < N) :
    QGateWellFormed N (i, j, entriesOf (onHigh U)) := by
  refine ⟨hij, hjN, ?_⟩
  show star (matrixOfEntries (entriesOf (onHigh U))) *
    matrixOfEntries (entriesOf (onHigh U)) = 1
  rw [matrixOfEntries_onHigh]
  have hUentry : ∀ a b : Fin 2,
      (star (complexOfGRatMatrix U) * complexOfGRatMatrix U) a b =
        (1 : Matrix (Fin 2) (Fin 2) ℂ) a b :=
    fun a b => congrFun (congrFun hU a) b
  simp [Matrix.mul_apply, Matrix.star_apply, complexOfGRatMatrix,
    Fin.sum_univ_two] at hUentry
  ext p q
  obtain ⟨a, b⟩ := p
  obtain ⟨c, d⟩ := q
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [Matrix.kronecker, complexOfGRatMatrix, Matrix.mul_apply,
      Matrix.star_apply, Fintype.sum_prod_type, Fin.sum_univ_two, hUentry]

/-- A low-controlled unitary is a well-formed Atlas gate. -/
theorem qGateWellFormed_ctrlLow (U : Matrix (Fin 2) (Fin 2) GRat)
    (hU : star (complexOfGRatMatrix U) * complexOfGRatMatrix U = 1)
    {N i j : ℕ} (hij : i < j) (hjN : j < N) :
    QGateWellFormed N (i, j, entriesOf (ctrlLow U)) := by
  refine ⟨hij, hjN, ?_⟩
  show star (matrixOfEntries (entriesOf (ctrlLow U))) *
    matrixOfEntries (entriesOf (ctrlLow U)) = 1
  rw [matrixOfEntries_entriesOf]
  have hUentry : ∀ a b : Fin 2,
      (star (complexOfGRatMatrix U) * complexOfGRatMatrix U) a b =
        (1 : Matrix (Fin 2) (Fin 2) ℂ) a b :=
    fun a b => congrFun (congrFun hU a) b
  simp [Matrix.mul_apply, Matrix.star_apply, complexOfGRatMatrix,
    Fin.sum_univ_two] at hUentry
  ext p q
  obtain ⟨a, b⟩ := p
  obtain ⟨c, d⟩ := q
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [complexOfGRatMatrix, ctrlLow, toComplex_gaussRatEnc_zero,
      toComplex_gaussRatEnc_one, Matrix.mul_apply, Matrix.star_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, hUentry]

/-- A high-controlled unitary is a well-formed Atlas gate. -/
theorem qGateWellFormed_ctrlHigh (U : Matrix (Fin 2) (Fin 2) GRat)
    (hU : star (complexOfGRatMatrix U) * complexOfGRatMatrix U = 1)
    {N i j : ℕ} (hij : i < j) (hjN : j < N) :
    QGateWellFormed N (i, j, entriesOf (ctrlHigh U)) := by
  refine ⟨hij, hjN, ?_⟩
  show star (matrixOfEntries (entriesOf (ctrlHigh U))) *
    matrixOfEntries (entriesOf (ctrlHigh U)) = 1
  rw [matrixOfEntries_entriesOf]
  have hUentry : ∀ a b : Fin 2,
      (star (complexOfGRatMatrix U) * complexOfGRatMatrix U) a b =
        (1 : Matrix (Fin 2) (Fin 2) ℂ) a b :=
    fun a b => congrFun (congrFun hU a) b
  simp [Matrix.mul_apply, Matrix.star_apply, complexOfGRatMatrix,
    Fin.sum_univ_two] at hUentry
  ext p q
  obtain ⟨a, b⟩ := p
  obtain ⟨c, d⟩ := q
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [complexOfGRatMatrix, ctrlHigh, toComplex_gaussRatEnc_zero,
      toComplex_gaussRatEnc_one, Matrix.mul_apply, Matrix.star_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, hUentry]

/-- The entry list for SWAP. -/
def swapEntries : List (RatEnc × RatEnc) := entriesOf swapMatrix

/-- SWAP is a well-formed Atlas gate. -/
theorem qGateWellFormed_swap {N i j : ℕ} (hij : i < j) (hjN : j < N) :
    QGateWellFormed N (i, j, swapEntries) := by
  refine ⟨hij, hjN, ?_⟩
  show star (matrixOfEntries swapEntries) * matrixOfEntries swapEntries = 1
  unfold swapEntries
  rw [matrixOfEntries_entriesOf]
  ext p q
  obtain ⟨a, b⟩ := p
  obtain ⟨c, d⟩ := q
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [complexOfGRatMatrix, swapMatrix, toComplex_gaussRatEnc,
      Complex.ext_iff, Matrix.mul_apply, Matrix.star_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two]

/-- The phase-shifted Hadamard matrix `e^{iπ/4} H` in Gaussian rationals. -/
def omegaH : Matrix (Fin 2) (Fin 2) GRat :=
  !![gaussRatEnc (1 / 2) (1 / 2), gaussRatEnc (1 / 2) (1 / 2);
     gaussRatEnc (1 / 2) (1 / 2), gaussRatEnc (-1 / 2) (-1 / 2)]

/-- The phase gate `S`. -/
def sGate : Matrix (Fin 2) (Fin 2) GRat :=
  !![gaussRatEnc 1 0, gaussRatEnc 0 0;
     gaussRatEnc 0 0, gaussRatEnc 0 1]

/-- The adjoint phase gate `S†`. -/
def sDagGate : Matrix (Fin 2) (Fin 2) GRat :=
  !![gaussRatEnc 1 0, gaussRatEnc 0 0;
     gaussRatEnc 0 0, gaussRatEnc 0 (-1)]

/-- The Pauli `X` gate. -/
def xGate : Matrix (Fin 2) (Fin 2) GRat :=
  !![gaussRatEnc 0 0, gaussRatEnc 1 0;
     gaussRatEnc 1 0, gaussRatEnc 0 0]

/-- The Pauli `Z` gate. -/
def zGate : Matrix (Fin 2) (Fin 2) GRat :=
  !![gaussRatEnc 1 0, gaussRatEnc 0 0;
     gaussRatEnc 0 0, gaussRatEnc (-1) 0]

/-- The square-root-of-`X` gate `V`. -/
def vGate : Matrix (Fin 2) (Fin 2) GRat :=
  !![gaussRatEnc (1 / 2) (1 / 2), gaussRatEnc (1 / 2) (-1 / 2);
     gaussRatEnc (1 / 2) (-1 / 2), gaussRatEnc (1 / 2) (1 / 2)]

/-- The adjoint square-root-of-`X` gate `V†`. -/
def vDagGate : Matrix (Fin 2) (Fin 2) GRat :=
  !![gaussRatEnc (1 / 2) (-1 / 2), gaussRatEnc (1 / 2) (1 / 2);
     gaussRatEnc (1 / 2) (1 / 2), gaussRatEnc (1 / 2) (-1 / 2)]

theorem omegaH_unitary :
    star (complexOfGRatMatrix omegaH) * complexOfGRatMatrix omegaH = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [complexOfGRatMatrix, omegaH, toComplex_gaussRatEnc,
      Complex.ext_iff, Matrix.mul_apply, Matrix.star_apply,
      Fin.sum_univ_two, Matrix.one_apply]

theorem sGate_unitary :
    star (complexOfGRatMatrix sGate) * complexOfGRatMatrix sGate = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [complexOfGRatMatrix, sGate, toComplex_gaussRatEnc,
      Complex.ext_iff, Matrix.mul_apply, Matrix.star_apply,
      Fin.sum_univ_two, Matrix.one_apply]

theorem sDagGate_unitary :
    star (complexOfGRatMatrix sDagGate) * complexOfGRatMatrix sDagGate = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [complexOfGRatMatrix, sDagGate, toComplex_gaussRatEnc,
      Complex.ext_iff, Matrix.mul_apply, Matrix.star_apply,
      Fin.sum_univ_two, Matrix.one_apply]

theorem xGate_unitary :
    star (complexOfGRatMatrix xGate) * complexOfGRatMatrix xGate = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [complexOfGRatMatrix, xGate, toComplex_gaussRatEnc,
      Complex.ext_iff, Matrix.mul_apply, Matrix.star_apply,
      Fin.sum_univ_two, Matrix.one_apply]

theorem zGate_unitary :
    star (complexOfGRatMatrix zGate) * complexOfGRatMatrix zGate = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [complexOfGRatMatrix, zGate, toComplex_gaussRatEnc,
      Complex.ext_iff, Matrix.mul_apply, Matrix.star_apply,
      Fin.sum_univ_two, Matrix.one_apply]

theorem vGate_unitary :
    star (complexOfGRatMatrix vGate) * complexOfGRatMatrix vGate = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [complexOfGRatMatrix, vGate, toComplex_gaussRatEnc,
      Complex.ext_iff, Matrix.mul_apply, Matrix.star_apply,
      Fin.sum_univ_two, Matrix.one_apply]

theorem vDagGate_unitary :
    star (complexOfGRatMatrix vDagGate) * complexOfGRatMatrix vDagGate = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [complexOfGRatMatrix, vDagGate, toComplex_gaussRatEnc,
      Complex.ext_iff, Matrix.mul_apply, Matrix.star_apply,
      Fin.sum_univ_two, Matrix.one_apply]

/-- The entry list of the phase-shifted Hadamard gate on the low qubit, the identity on the
high one; the entry lists of the other spectator embeddings follow. -/
def omegaHLowEntries : List (RatEnc × RatEnc) := entriesOf (onLow omegaH)
def omegaHHighEntries : List (RatEnc × RatEnc) := entriesOf (onHigh omegaH)
def sLowEntries : List (RatEnc × RatEnc) := entriesOf (onLow sGate)
def sHighEntries : List (RatEnc × RatEnc) := entriesOf (onHigh sGate)
def sDagLowEntries : List (RatEnc × RatEnc) := entriesOf (onLow sDagGate)
def sDagHighEntries : List (RatEnc × RatEnc) := entriesOf (onHigh sDagGate)
def xLowEntries : List (RatEnc × RatEnc) := entriesOf (onLow xGate)
def xHighEntries : List (RatEnc × RatEnc) := entriesOf (onHigh xGate)
def zLowEntries : List (RatEnc × RatEnc) := entriesOf (onLow zGate)
def zHighEntries : List (RatEnc × RatEnc) := entriesOf (onHigh zGate)

/-- The entry list of the controlled-NOT gate with the low qubit as control; the entry lists
of the other controlled gates follow. -/
def cnotLowEntries : List (RatEnc × RatEnc) := entriesOf (ctrlLow xGate)
def cnotHighEntries : List (RatEnc × RatEnc) := entriesOf (ctrlHigh xGate)
def controlledOmegaHLowEntries : List (RatEnc × RatEnc) :=
  entriesOf (ctrlLow omegaH)
def controlledOmegaHHighEntries : List (RatEnc × RatEnc) :=
  entriesOf (ctrlHigh omegaH)
def controlledSLowEntries : List (RatEnc × RatEnc) :=
  entriesOf (ctrlLow sGate)
def controlledSHighEntries : List (RatEnc × RatEnc) :=
  entriesOf (ctrlHigh sGate)
def controlledSDagLowEntries : List (RatEnc × RatEnc) :=
  entriesOf (ctrlLow sDagGate)
def controlledSDagHighEntries : List (RatEnc × RatEnc) :=
  entriesOf (ctrlHigh sDagGate)
def cvLowEntries : List (RatEnc × RatEnc) := entriesOf (ctrlLow vGate)
def cvHighEntries : List (RatEnc × RatEnc) := entriesOf (ctrlHigh vGate)
def cvDagLowEntries : List (RatEnc × RatEnc) := entriesOf (ctrlLow vDagGate)
def cvDagHighEntries : List (RatEnc × RatEnc) := entriesOf (ctrlHigh vDagGate)

/-- A controlled gate on control `c` and target `t`, encoded on `(min c t, max c t)`; for `c = t`
it is `(c, c, entriesOf (ctrlHigh U))`, an encoding but not a well-formed gate. -/
def controlledGate (U : Matrix (Fin 2) (Fin 2) GRat) (c t : ℕ) : QGate :=
  if c < t then (c, t, entriesOf (ctrlLow U))
  else (t, c, entriesOf (ctrlHigh U))

/-- Every controlled unitary gate in either orientation is well-formed. -/
theorem controlledGate_wellFormed (U : Matrix (Fin 2) (Fin 2) GRat)
    (hU : star (complexOfGRatMatrix U) * complexOfGRatMatrix U = 1)
    {N c t : ℕ} (hct : c ≠ t) (hcN : c < N) (htN : t < N) :
    QGateWellFormed N (controlledGate U c t) := by
  unfold controlledGate
  by_cases h : c < t
  · rw [if_pos h]
    exact qGateWellFormed_ctrlLow U hU h htN
  · rw [if_neg h]
    have htc : t < c := by omega
    exact qGateWellFormed_ctrlHigh U hU htc hcN

/-- The five-gate Toffoli list from Barenco Lemma 6.1, with controls `a, b`
and target `c`. -/
def toffoliGates (a b c : ℕ) : List QGate :=
  [controlledGate vGate b c,
   controlledGate xGate a b,
   controlledGate vDagGate b c,
   controlledGate xGate a b,
   controlledGate vGate a c]

/-- Every gate in the five-gate Toffoli list is well-formed for distinct
in-range indices in any order. -/
theorem toffoliGates_wellFormed {N a b c : ℕ}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (haN : a < N) (hbN : b < N) (hcN : c < N) :
    ∀ g ∈ toffoliGates a b c, QGateWellFormed N g := by
  intro g hg
  unfold toffoliGates at hg
  simp at hg
  rcases hg with rfl|rfl|rfl|rfl|rfl
  · exact controlledGate_wellFormed vGate vGate_unitary hbc hbN hcN
  · exact controlledGate_wellFormed xGate xGate_unitary hab haN hbN
  · exact controlledGate_wellFormed vDagGate vDagGate_unitary hbc hbN hcN
  · exact controlledGate_wellFormed xGate xGate_unitary hab haN hbN
  · exact controlledGate_wellFormed vGate vGate_unitary hac haN hcN

/-- The complex Hadamard matrix. -/
noncomputable def hadamard : Matrix (Fin 2) (Fin 2) ℂ :=
  ((1 / Real.sqrt 2 : ℝ) : ℂ) • !![1, 1; 1, -1]

private theorem exp_pi_div_four_I :
    Complex.exp (Real.pi / 4 * Complex.I) =
      ⟨Real.sqrt 2 / 2, Real.sqrt 2 / 2⟩ := by
  apply Complex.ext
  · simp [Complex.exp_re, Real.cos_pi_div_four]
  · simp [Complex.exp_im, Real.sin_pi_div_four]

/-- The encoded phase-shifted Hadamard is the global phase times Hadamard. -/
theorem omegaH_eq_smul_hadamard :
    complexOfGRatMatrix omegaH =
      Complex.exp (Real.pi / 4 * Complex.I) • hadamard := by
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt h2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexOfGRatMatrix, omegaH, hadamard, toComplex_gaussRatEnc,
      exp_pi_div_four_I, Complex.ext_iff] <;>
    ((first | rw [div_mul_div_comm, hsq]); norm_num)

end Cslib.Complexity.Classes.QuantumGates
