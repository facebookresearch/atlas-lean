/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Chemistry.Symmetry.GroupRepresentations

/-!

# Tests for `PhyslibExt.Chemistry.Symmetry.GroupRepresentations`

-/

@[expose] public section

namespace Chemistry.Symmetry.GroupRepresentationsTest

open Chemistry.Symmetry Module Representation ComplexConjugate Matrix TensorProduct

/-! ### Character orthogonality on `Ci` (explicit sums and the general theorem) -/

example : charInner inversionAu.character inversionAu.character = 1 := by
  rw [charInner, sum_units_int, Nat.card_eq_fintype_card, Fintype.card_units_int]
  simp only [character_inversionAu]
  norm_num

example : charInner inversionAg.character inversionAu.character = 0 := by
  rw [charInner, sum_units_int, Nat.card_eq_fintype_card, Fintype.card_units_int]
  simp only [character_trivial, character_inversionAu]
  norm_num

example : charInner inversionAu.character inversionAu.character = 1 :=
  charInner_character_self inversionAu

lemma character_inversionAu_ne_inversionAg : inversionAu.character ≠ inversionAg.character := by
  intro h
  have h1 := congrFun h (-1)
  rw [character_inversionAu, character_trivial] at h1
  norm_num at h1

example : charInner inversionAg.character inversionAu.character = 0 :=
  charInner_character_eq_zero_of_ne _ _ character_inversionAu_ne_inversionAg.symm

lemma not_nonempty_equiv_inversionAg_inversionAu : ¬ Nonempty (inversionAg.Equiv inversionAu) := by
  rw [nonempty_equiv_iff_character_eq]
  exact character_inversionAu_ne_inversionAg

lemma not_nonempty_equiv_inversionAu_inversionAg : ¬ Nonempty (inversionAu.Equiv inversionAg) := by
  rw [nonempty_equiv_iff_character_eq]
  exact character_inversionAu_ne_inversionAg.symm

example (g : ℤˣ) : inversionAu.character g⁻¹ = conj (inversionAu.character g) :=
  character_inv_eq_conj inversionAu g

/-! ### Reduction formula on concrete representations -/

example : (irrepMultiplicity inversionAu (vectorRepresentation inversionAction) : ℂ) =
    (2 : ℂ)⁻¹ * (3 * conj 1 + (-3) * conj (-1)) := by
  rw [irrepMultiplicity_eq_charInner, charInner, sum_units_int, Nat.card_eq_fintype_card,
    Fintype.card_units_int]
  simp only [character_vectorRepresentation_inversionAction, character_inversionAu]
  norm_num

example : (vectorRepresentation inversionAction).character (-1) = -3 := by
  rw [character_vectorRepresentation_inversionAction]
  norm_num

example : irrepMultiplicity inversionAg (vectorRepresentation inversionAction) = 0 :=
  inversion_vector_decomposition.1

example : irrepMultiplicity inversionAu (vectorRepresentation inversionAction) = 3 :=
  inversion_vector_decomposition.2

example : irrepMultiplicity inversionAg (quadraticRepresentation inversionAction) = 6 :=
  inversion_quadratic_decomposition.1

example : irrepMultiplicity inversionAu (quadraticRepresentation inversionAction) = 0 :=
  inversion_quadratic_decomposition.2

example : irrepMultiplicity inversionAu (inversionAu.prod inversionAg) = 1 := by
  rw [irrepMultiplicity_prod, irrepMultiplicity_of_isIrreducible,
    irrepMultiplicity_of_isIrreducible, ite_eq_left ⟨Representation.Equiv.refl _⟩,
    ite_eq_right not_nonempty_equiv_inversionAu_inversionAg]

example :
    irrepMultiplicity inversionAg (vectorRepresentation inversionAction) * finrank ℂ ℂ +
        irrepMultiplicity inversionAu (vectorRepresentation inversionAction) * finrank ℂ ℂ =
      finrank ℂ (Fin 3 → ℂ) := by
  rw [inversion_vector_decomposition.1, inversion_vector_decomposition.2, finrank_self,
    Module.finrank_fin_fun]

example :
    irrepMultiplicity inversionAg (quadraticRepresentation inversionAction) * finrank ℂ ℂ +
        irrepMultiplicity inversionAu (quadraticRepresentation inversionAction) * finrank ℂ ℂ =
      finrank ℂ symmetricMatrices := by
  rw [inversion_quadratic_decomposition.1, inversion_quadratic_decomposition.2, finrank_self,
    finrank_symmetricMatrices]

/-! ### `3N - 6` and `3N - 5` on concrete configurations -/

/-- A bent triatomic (water-like) configuration. -/
def bentPositions : Fin 3 → Fin 3 → ℝ := ![![0, 0, 0], ![1, 0, 0], ![0, 1, 0]]

/-- Masses for `bentPositions`. -/
def bentMasses : Fin 3 → ℝ := ![16, 1, 1]

lemma bentMasses_pos : ∀ i, 0 < bentMasses i := by
  intro i
  fin_cases i <;> norm_num [bentMasses]

lemma bentPositions_not_collinear : ¬ Collinear ℝ (Set.range bentPositions) := by
  apply not_collinear_of_cross_ne_zero 0 1 2
  intro h
  have h2 := congrFun h 2
  norm_num [bentPositions, cross_apply] at h2

example : finrank ℝ (InternalModeSpace bentMasses bentPositions) = 3 := by
  rw [finrank_internalModeSpace_of_not_collinear bentMasses bentPositions bentMasses_pos
    bentPositions_not_collinear]

/-- A pyramidal tetratomic (ammonia-like) configuration. -/
def pyramidPositions : Fin 4 → Fin 3 → ℝ :=
  ![![0, 0, 1], ![1, 0, 0], ![0, 1, 0], ![-1, -1, 0]]

/-- Masses for `pyramidPositions`. -/
def pyramidMasses : Fin 4 → ℝ := ![14, 1, 1, 1]

example : finrank ℝ (InternalModeSpace pyramidMasses pyramidPositions) = 6 := by
  rw [finrank_internalModeSpace_of_not_collinear]
  · intro i
    fin_cases i <;> norm_num [pyramidMasses]
  · apply not_collinear_of_cross_ne_zero 0 1 2
    intro h
    have h2 := congrFun h 2
    norm_num [pyramidPositions, cross_apply] at h2

/-- A linear triatomic (carbon-dioxide-like) configuration along the `x` axis. -/
def linearPositions : Fin 3 → Fin 3 → ℝ := ![![-1, 0, 0], ![0, 0, 0], ![1, 0, 0]]

/-- Masses for `linearPositions`. -/
def linearMasses : Fin 3 → ℝ := ![16, 12, 16]

lemma linearMasses_pos : ∀ i, 0 < linearMasses i := by
  intro i
  fin_cases i <;> norm_num [linearMasses]

lemma linearPositions_collinear : Collinear ℝ (Set.range linearPositions) := by
  rw [collinear_iff_of_mem (Set.mem_range_self 1)]
  refine ⟨![1, 0, 0], ?_⟩
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact ⟨-1, by ext k; fin_cases k <;> simp [linearPositions]⟩
  · exact ⟨0, by ext k; fin_cases k <;> simp [linearPositions]⟩
  · exact ⟨1, by ext k; fin_cases k <;> simp [linearPositions]⟩

lemma linearPositions_ne : linearPositions 0 ≠ linearPositions 2 := by
  intro h
  have h0 := congrFun h 0
  norm_num [linearPositions] at h0

lemma finrank_internalModeSpace_linear :
    finrank ℝ (InternalModeSpace linearMasses linearPositions) = 4 := by
  rw [finrank_internalModeSpace_of_collinear linearMasses linearPositions linearMasses_pos
    linearPositions_collinear linearPositions_ne]

/-- A diatomic configuration. -/
def diatomicPositions : Fin 2 → Fin 3 → ℝ := ![![0, 0, 0], ![0, 0, 1]]

example : finrank ℝ (InternalModeSpace ![1, 35] diatomicPositions) = 1 := by
  rw [finrank_internalModeSpace_of_collinear (a := 0) (b := 1)]
  · intro i
    fin_cases i <;> norm_num
  · by_contra h
    have := three_le_of_not_collinear h
    omega
  · intro h
    have h2 := congrFun h 2
    norm_num [diatomicPositions] at h2

/-! ### The internal-mode representation of the linear triatomic under `Ci` -/

/-- Inversion swaps the two end nuclei of `linearPositions`. -/
def linearPerm : ℤˣ →* Equiv.Perm (Fin 3) where
  toFun u := if u = 1 then 1 else Equiv.swap 0 2
  map_one' := ite_eq_left rfl
  map_mul' u v := by
    rcases Int.units_eq_one_or u with rfl | rfl <;>
      rcases Int.units_eq_one_or v with rfl | rfl <;> decide

lemma centreOfMass_linear : centreOfMass linearMasses linearPositions = 0 := by
  ext k
  fin_cases k <;> norm_num [centreOfMass, Fin.sum_univ_three, linearMasses, linearPositions]

lemma linear_compat (u : ℤˣ) (i : Fin 3) :
    (inversionAction u : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ
        (linearPositions i - centreOfMass linearMasses linearPositions) =
      linearPositions (linearPerm u i) - centreOfMass linearMasses linearPositions := by
  rw [centreOfMass_linear, sub_zero, sub_zero]
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp [inversionAction, linearPerm]
  · fin_cases i <;>
    · ext k
      fin_cases k <;>
        simp [inversionAction, linearPerm, linearPositions, Equiv.swap_apply_def, neg_mulVec]

/-- The `4`-dimensional internal-mode representation of the linear triatomic under `Ci`. -/
noncomputable def linearInternalModes :
    Representation ℝ ℤˣ (InternalModeSpace linearMasses linearPositions) :=
  internalModeRepresentation inversionAction linearPerm linearMasses linearPositions linear_compat

/-- The symmetric stretch is gerade: inversion fixes its class. -/
example : linearInternalModes (-1) (Submodule.Quotient.mk ![![-1, 0, 0], 0, ![1, 0, 0]]) =
    Submodule.Quotient.mk ![![-1, 0, 0], 0, ![1, 0, 0]] := by
  rw [linearInternalModes, internalModeRepresentation_mk]
  congr 1
  funext i
  rw [displacementRepresentation_apply]
  fin_cases i <;>
  · ext k
    fin_cases k <;> simp [inversionAction, linearPerm, Equiv.swap_apply_def, neg_mulVec]

/-- The in-phase stretch of the end nuclei is ungerade: inversion negates its class. -/
example : linearInternalModes (-1) (Submodule.Quotient.mk ![![1, 0, 0], 0, ![1, 0, 0]]) =
    -Submodule.Quotient.mk ![![1, 0, 0], 0, ![1, 0, 0]] := by
  rw [linearInternalModes, internalModeRepresentation_mk, ← Submodule.Quotient.mk_neg]
  congr 1
  funext i
  rw [displacementRepresentation_apply]
  fin_cases i <;>
  · ext k
    fin_cases k <;> simp [inversionAction, linearPerm, Equiv.swap_apply_def, neg_mulVec]

/-! ### Boundary cases -/

/-- The `3N - 6` formula does not apply to the linear configuration: it has `4` modes, not `3`. -/
example : finrank ℝ (InternalModeSpace linearMasses linearPositions) ≠ 3 * 3 - 6 := by
  rw [finrank_internalModeSpace_linear]
  norm_num

/-- The noncollinearity hypothesis of the `3N - 6` rule fails for the linear configuration. -/
example : ¬ ¬ Collinear ℝ (Set.range linearPositions) :=
  not_not_intro linearPositions_collinear

/-- Every two-nucleus configuration is collinear, so the `3N - 6` hypothesis never holds. -/
example (x : Fin 2 → Fin 3 → ℝ) : Collinear ℝ (Set.range x) := by
  by_contra h
  have := three_le_of_not_collinear h
  omega

/-- A product with no trivial component averages to zero (`Au ⊗ Ag` in `Ci`). -/
example : groupAverage (inversionAu.tprod inversionAg) ((1 : ℂ) ⊗ₜ (1 : ℂ)) = 0 := by
  apply groupAverage_tprod_tmul_eq_zero
  rw [charInner, sum_units_int, Nat.card_eq_fintype_card, Fintype.card_units_int]
  simp only [Pi.mul_apply, character_inversionAu, character_trivial]
  norm_num

/-- `Au ⊗ Au` does contain the trivial representation, so the vanishing hypothesis fails. -/
example : charInner (inversionAu.character * inversionAu.character)
    (trivial ℂ ℤˣ ℂ).character ≠ 0 := by
  rw [charInner, sum_units_int, Nat.card_eq_fintype_card, Fintype.card_units_int]
  simp only [Pi.mul_apply, character_inversionAu, character_trivial]
  norm_num

/-- Every inversion-invariant linear form on Cartesian space vanishes. -/
example (ℓ : (Fin 3 → ℂ) →ₗ[ℂ] ℂ) (hℓ : ∀ g, ℓ ∘ₗ vectorRepresentation inversionAction g = ℓ) :
    ℓ = 0 := by
  apply invariant_linearForm_eq_zero _ _ ℓ hℓ
  rw [← irrepMultiplicity_trivial_eq_zero_iff]
  exact inversion_vector_decomposition.1

/-! ### Group averaging as a projection: `C2` about the `z` axis -/

/-- The Cartesian matrix `diag(u, u, 1)` of `C2` with axis `z` (index `2`). -/
def c2Matrix (u : ℤˣ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal ![((u : ℤ) : ℝ), ((u : ℤ) : ℝ), 1]

lemma c2Matrix_mem (u : ℤˣ) : c2Matrix u ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
  have hu : ((u : ℤ) : ℝ) * ((u : ℤ) : ℝ) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  rw [Matrix.mem_orthogonalGroup_iff, c2Matrix, Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp [hu]

/-- The point group `C2` with axis `z`: `-1` acts by `diag(-1, -1, 1)`. -/
def c2Action : ℤˣ →* Matrix.orthogonalGroup (Fin 3) ℝ where
  toFun u := ⟨c2Matrix u, c2Matrix_mem u⟩
  map_one' := Subtype.ext <| by
    change c2Matrix 1 = 1
    rw [c2Matrix, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp
  map_mul' u v := Subtype.ext <| by
    change c2Matrix (u * v) = c2Matrix u * c2Matrix v
    rw [c2Matrix, c2Matrix, c2Matrix, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp

lemma cartesianMatrix_c2Action (u : ℤˣ) :
    cartesianMatrix c2Action u = Matrix.diagonal ![((u : ℤ) : ℂ), ((u : ℤ) : ℂ), 1] := by
  rw [cartesianMatrix_apply, show ((c2Action u : Matrix.orthogonalGroup (Fin 3) ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ) = c2Matrix u from rfl, c2Matrix, Matrix.diagonal_map (map_zero _)]
  congr 1
  funext i
  fin_cases i <;> simp

example (v : Fin 3 → ℂ) :
    groupAverage (vectorRepresentation c2Action) v = ![0, 0, v 2] := by
  rw [groupAverage_apply, sum_units_int, Nat.card_eq_fintype_card, Fintype.card_units_int,
    vectorRepresentation_apply, vectorRepresentation_apply, cartesianMatrix_c2Action,
    cartesianMatrix_c2Action]
  ext k
  fin_cases k
  · simp [mulVec_diagonal]
  · simp [mulVec_diagonal]
  · simp [mulVec_diagonal]
    ring

example (v : Fin 3 → ℂ) :
    groupAverage (vectorRepresentation c2Action) v ∈ (vectorRepresentation c2Action).invariants :=
  groupAverage_apply_mem_invariants _ v

lemma character_vectorRepresentation_c2Action (u : ℤˣ) :
    (vectorRepresentation c2Action).character u = 2 * ((u : ℤ) : ℂ) + 1 := by
  rw [character, show vectorRepresentation c2Action u = Matrix.toLin' (cartesianMatrix c2Action u)
    from rfl, Matrix.trace_toLin'_eq, cartesianMatrix_c2Action]
  simp [Matrix.trace, Fin.sum_univ_three]
  ring

/-- Under `C2` (axis `z`), `z` spans the totally symmetric `A` and `x, y` span `B`:
`Γ_xyz = A + 2 B`. -/
example : irrepMultiplicity (trivial ℂ ℤˣ ℂ) (vectorRepresentation c2Action) = 1 ∧
    irrepMultiplicity inversionAu (vectorRepresentation c2Action) = 2 := by
  constructor <;> apply Nat.cast_injective (R := ℂ) <;>
    rw [irrepMultiplicity_eq_charInner, charInner, sum_units_int, Nat.card_eq_fintype_card,
      Fintype.card_units_int] <;>
    simp only [character_vectorRepresentation_c2Action, character_trivial,
      character_inversionAu] <;>
    norm_num

/-! ### IR / Raman classification on `Ci` -/

example : IsIRActive inversionAction inversionAu := inversion_activity.2.2.1

example : ¬ IsIRActive inversionAction inversionAg := inversion_activity.2.1

example : IsRamanActive inversionAction inversionAg := inversion_activity.1

example : ¬ IsRamanActive inversionAction inversionAu := inversion_activity.2.2.2

example : IsIRActive inversionAction inversionAu := by
  rw [isIRActive_iff_charInner_ne_zero, charInner, sum_units_int, Nat.card_eq_fintype_card,
    Fintype.card_units_int]
  simp only [character_vectorRepresentation_inversionAction, character_inversionAu]
  norm_num

example : ¬ IsRamanActive inversionAction inversionAu := by
  rw [isRamanActive_iff_charInner_ne_zero, not_not, charInner, sum_units_int,
    Nat.card_eq_fintype_card, Fintype.card_units_int]
  simp only [character_quadraticRepresentation_inversionAction, character_inversionAu]
  norm_num

/-! ### Great orthogonality on `Ci` -/

example (f : ℂ →ₗ[ℂ] ℂ) : ∑ g, inversionAu g ∘ₗ f ∘ₗ inversionAg g⁻¹ = 0 :=
  sum_comp_comp_inv_eq_zero_of_not_nonempty_equiv _ _ not_nonempty_equiv_inversionAg_inversionAu f

example (f : ℂ →ₗ[ℂ] ℂ) :
    (Nat.card ℤˣ : ℂ)⁻¹ • ∑ g, inversionAu g ∘ₗ f ∘ₗ inversionAu g⁻¹ =
      LinearMap.trace ℂ ℂ f • LinearMap.id := by
  rw [groupAverage_comp_comp_inv_eq_trace_smul, finrank_self, Nat.cast_one, div_one]

end Chemistry.Symmetry.GroupRepresentationsTest
