/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.RepresentationTheory.Character
public import Mathlib.RingTheory.SimpleModule.Rank

/-!

# Molecular symmetry and finite group representations

Point-group characters, vibrational mode counting, vanishing integrals and IR/Raman activity.

## i. Overview

A point group is modelled as a finite group `G`; its representations are finite-dimensional
complex representations `ρ : Representation ℂ G V`. Mathlib states character orthogonality and
the dimension formula for intertwining maps with the normalisation
`(Nat.card G)⁻¹ * ∑ g, χ g * ψ g⁻¹`. We prove `χ g⁻¹ = conj (χ g)` for every finite-dimensional
complex representation of a finite group (the unitary trick) and restate these results with
the chemistry normalisation `charInner χ ψ = (Nat.card G)⁻¹ * ∑ g, χ g * conj (ψ g)`. The
multiplicity of an irreducible `σ` in `ρ` is the natural number
`finrank ℂ (IntertwiningMap σ ρ)`.

For `N` point masses at positions `x : Fin N → Fin 3 → ℝ` the internal-mode space is the
quotient of the Cartesian displacement space `Fin N → Fin 3 → ℝ` (dimension `3 * N`) by the
rigid translations and the linearised rigid rotations about the centre of mass. Its dimension
is `3 * N - 6` for a noncollinear configuration and `3 * N - 5` for a linear one. This is a
kinematic dimension count of a quotient space: zero or imaginary frequencies are properties of
the dynamical (Hessian) problem, which is not modelled and not inferred here. A point group
permuting the nuclei acts on displacements; translations transform like `x, y, z`, rotations
like `Rx, Ry, Rz`, and the internal-mode representation is the quotient representation.

The group average `(Nat.card G)⁻¹ • ∑ g, ρ g` is the projection onto the invariant (totally
symmetric) subspace. If the trivial representation does not occur (character inner product with
the trivial character equal to `0`), then the average and every `G`-invariant linear form
vanish; for a tensor product of factors this is the finite-group vanishing-integral rule.

IR and Raman activity are definitions inside the dipole/polarizability model: an irrep is
IR-active iff it occurs in the vector representation on Cartesian `x, y, z`, and Raman-active
iff it occurs in the symmetric-square representation on symmetric `3 × 3` matrices (quadratic
forms). Intensities, accidental degeneracies and observation of a band are not predicted.
Irrep labels refer to the fixed convention stated with each example. The inversion group `Ci`
is worked out explicitly: `Au` is IR-active and Raman-inactive, `Ag` is Raman-active and
IR-inactive.

## ii. Key results

- `Chemistry.Symmetry.character_inv_eq_conj` : `χ g⁻¹ = conj (χ g)`.
- `Chemistry.Symmetry.charInner_character_eq_ite` : irreducible characters are orthonormal.
- `Chemistry.Symmetry.irrepMultiplicity_eq_charInner` : the reduction formula.
- `Chemistry.Symmetry.sum_comp_comp_inv_eq_zero_of_not_nonempty_equiv` and
  `Chemistry.Symmetry.groupAverage_comp_comp_inv_eq_trace_smul` : great orthogonality.
- `Chemistry.Symmetry.isProj_groupAverage` : group averaging projects onto the invariants.
- `Chemistry.Symmetry.groupAverage_eq_zero_of_charInner_trivial_eq_zero`,
  `Chemistry.Symmetry.invariant_linearForm_eq_zero` and
  `Chemistry.Symmetry.groupAverage_tprod_tmul_eq_zero` : the vanishing-integral rule.
- `Chemistry.Symmetry.finrank_internalModeSpace_of_not_collinear` (`3 * N - 6`) and
  `Chemistry.Symmetry.finrank_internalModeSpace_of_collinear` (`3 * N - 5`).
- `Chemistry.Symmetry.internalModeRepresentation` : the internal-mode representation, the
  quotient of the displacement representation by translations (`x, y, z`) and rotations
  (`Rx, Ry, Rz`).
- `Chemistry.Symmetry.IsIRActive`, `Chemistry.Symmetry.IsRamanActive` and
  `Chemistry.Symmetry.inversion_activity`.

## iii. Table of contents

- A. Characters and the conjugation bridge
- B. Orthogonality relations and the reduction formula
- C. Group averaging and the vanishing-integral rule
- D. Great orthogonality
- E. Vibrational mode counting
  - E.1. Translations, rotations and the internal-mode space
  - E.2. The point-group action and the internal-mode representation
- F. IR and Raman activity
- G. Worked example: the inversion group `Ci`

## iv. References

- MIT OpenCourseWare, *5.61 Physical Chemistry*, Fall 2017.
- J.-P. Serre, *Linear Representations of Finite Groups*, Graduate Texts in Mathematics 42,
  Springer (1977), Chapters 1 and 2.
- E. B. Wilson, J. C. Decius, P. C. Cross, *Molecular Vibrations*, McGraw-Hill (1955).

-/

@[expose] public section

noncomputable section

namespace Chemistry.Symmetry

open Module Representation ComplexConjugate Matrix

/-!

## A. Characters and the conjugation bridge

-/

/-- The character inner product `⟨χ, ψ⟩ = |G|⁻¹ * ∑ g, χ g * conj (ψ g)` of complex class
functions on a finite group, with `|G| = Nat.card G`. -/
def charInner {G : Type*} [Fintype G] (χ ψ : G → ℂ) : ℂ :=
  (Nat.card G : ℂ)⁻¹ * ∑ g, χ g * conj (ψ g)

open scoped ComplexOrder in
/-- For a finite-dimensional complex representation of a finite group, `χ g⁻¹ = conj (χ g)`.
The proof averages `Aᴴ * A` over the group to obtain an invariant positive definite matrix
`P`, so that `(A g)ᴴ * P = P * A g⁻¹`. -/
lemma character_inv_eq_conj {G V : Type*} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (g : G) :
    ρ.character g⁻¹ = conj (ρ.character g) := by
  classical
  let b := Module.finBasis ℂ V
  let A : G → Matrix (Fin (finrank ℂ V)) (Fin (finrank ℂ V)) ℂ :=
    fun h => LinearMap.toMatrix b b (ρ h)
  have hA : ∀ h k, A (h * k) = A h * A k := fun h k => by
    simp only [A, map_mul, LinearMap.toMatrix_mul]
  have hA1 : A 1 = 1 := by simp only [A, map_one, LinearMap.toMatrix_one]
  let P := ∑ h, (A h)ᴴ * A h
  have hP : (A g)ᴴ * P * A g = P := by
    simp only [P, Finset.mul_sum, Finset.sum_mul]
    refine Fintype.sum_equiv (Equiv.mulRight g) _ _ fun h => ?_
    simp only [Equiv.coe_mulRight, hA, conjTranspose_mul, Matrix.mul_assoc]
  have hPpos : P.PosDef := by
    have hsplit : P = 1 + ∑ h ∈ Finset.univ.erase 1, (A h)ᴴ * A h := by
      change ∑ h, (A h)ᴴ * A h = _
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : G)), hA1, conjTranspose_one,
        Matrix.mul_one]
    rw [hsplit]
    exact PosDef.one.add_posSemidef
      (posSemidef_sum _ fun h _ => posSemidef_conjTranspose_mul_self (A h))
  have hPu : IsUnit P.det := (isUnit_iff_isUnit_det P).mp hPpos.isUnit
  have key : (A g)ᴴ * P = P * A g⁻¹ := by
    calc (A g)ᴴ * P = (A g)ᴴ * P * (A g * A g⁻¹) := by
          rw [← hA, mul_inv_cancel, hA1, Matrix.mul_one]
      _ = P * A g⁻¹ := by rw [← Matrix.mul_assoc, hP]
  calc ρ.character g⁻¹ = (A g⁻¹).trace := LinearMap.trace_eq_matrix_trace ℂ b _
    _ = (P⁻¹ * (P * A g⁻¹)).trace := by
      rw [← Matrix.mul_assoc, nonsing_inv_mul P hPu, Matrix.one_mul]
    _ = (P⁻¹ * ((A g)ᴴ * P)).trace := by rw [key]
    _ = ((A g)ᴴ * P * P⁻¹).trace := by rw [Matrix.trace_mul_comm]
    _ = ((A g)ᴴ).trace := by rw [Matrix.mul_assoc, mul_nonsing_inv P hPu, Matrix.mul_one]
    _ = star (A g).trace := trace_conjTranspose _
    _ = conj (ρ.character g) := by rw [character, LinearMap.trace_eq_matrix_trace ℂ b]; rfl

/-- Bridge between `charInner` and Mathlib's normalisation `∑ g, χ g * ψ g⁻¹`. -/
lemma charInner_character_eq_sum_inv {G V W : Type*} [Group G] [Fintype G] [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) :
    charInner ρ.character σ.character =
      (Nat.card G : ℂ)⁻¹ * ∑ g, ρ.character g * σ.character g⁻¹ := by
  simp only [charInner, character_inv_eq_conj]

/-!

## B. Orthogonality relations and the reduction formula

-/

/-- The multiplicity of a representation `σ` (in applications an irreducible one) in `ρ`
(note the order: `σ` occurs in `ρ`), defined as the natural number
`finrank ℂ (IntertwiningMap σ ρ)`. For a finite group, finite-dimensional representations and
irreducible `σ`, this counts the copies of `σ` in a decomposition of `ρ` into irreducibles
(`irrepMultiplicity_of_isIrreducible`, `irrepMultiplicity_prod`, `irrepMultiplicity_congr`). -/
def irrepMultiplicity {G V W : Type*} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (σ : Representation ℂ G W) (ρ : Representation ℂ G V) : ℕ :=
  finrank ℂ (IntertwiningMap σ ρ)

/-- **Reduction formula**: the multiplicity of `σ` in `ρ` is
`|G|⁻¹ * ∑ g, χ_ρ g * conj (χ_σ g)`. -/
theorem irrepMultiplicity_eq_charInner {G V W : Type*} [Group G] [Fintype G] [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ G W) (ρ : Representation ℂ G V) :
    (irrepMultiplicity σ ρ : ℂ) = charInner ρ.character σ.character := by
  have : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  rw [charInner_character_eq_sum_inv, card_inv_mul_sum_char_mul_char_eq_finrank σ ρ]
  rfl

open scoped Classical in
/-- **Orthogonality of irreducible characters** in the `conj` normalisation, transported from
Mathlib's `Representation.char_orthonormal`. -/
theorem charInner_character_eq_ite_nonempty_equiv {G V W : Type*} [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    [IsIrreducible ρ] [IsIrreducible σ] :
    charInner ρ.character σ.character = if Nonempty (σ.Equiv ρ) then 1 else 0 := by
  have : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  rw [charInner_character_eq_sum_inv, char_orthonormal ρ σ]

/-- An irreducible character has norm one: `⟨χ, χ⟩ = 1`. -/
lemma charInner_character_self {G V : Type*} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) [IsIrreducible ρ] :
    charInner ρ.character ρ.character = 1 := by
  classical
  rw [charInner_character_eq_ite_nonempty_equiv, ite_eq_left ⟨Representation.Equiv.refl ρ⟩]

/-- Distinct irreducible characters are orthogonal. -/
lemma charInner_character_eq_zero_of_ne {G V W : Type*} [Group G] [Fintype G] [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) [IsIrreducible ρ] [IsIrreducible σ]
    (h : ρ.character ≠ σ.character) : charInner ρ.character σ.character = 0 := by
  classical
  rw [charInner_character_eq_ite_nonempty_equiv, ite_eq_right]
  rintro ⟨φ⟩
  exact h (char_iso φ).symm

open scoped Classical in
/-- **Character orthogonality**: for irreducible `ρ` and `σ`,
`|G|⁻¹ * ∑ g, χ_ρ g * conj (χ_σ g)` is `1` if the characters are equal and `0` otherwise. -/
theorem charInner_character_eq_ite {G V W : Type*} [Group G] [Fintype G] [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) [IsIrreducible ρ] [IsIrreducible σ] :
    charInner ρ.character σ.character = if ρ.character = σ.character then 1 else 0 := by
  split_ifs with h
  · rw [h]
    exact charInner_character_self σ
  · exact charInner_character_eq_zero_of_ne ρ σ h

/-- Irreducible representations are isomorphic iff their characters are equal. -/
lemma nonempty_equiv_iff_character_eq {G V W : Type*} [Group G] [Fintype G] [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) [IsIrreducible ρ] [IsIrreducible σ] :
    Nonempty (σ.Equiv ρ) ↔ ρ.character = σ.character := by
  classical
  refine ⟨fun ⟨φ⟩ => (char_iso φ).symm, fun h => ?_⟩
  by_contra hne
  have h1 := charInner_character_eq_ite_nonempty_equiv ρ σ
  rw [ite_eq_right hne, h, charInner_character_self] at h1
  exact one_ne_zero h1

open scoped Classical in
/-- Schur's lemma as a count: an irreducible `τ` contains an irreducible `σ` once if they are
isomorphic and zero times otherwise. -/
lemma irrepMultiplicity_of_isIrreducible {G V W : Type*} [Group G] [Fintype G] [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ G W) (τ : Representation ℂ G V) [IsIrreducible σ] [IsIrreducible τ] :
    irrepMultiplicity σ τ = if Nonempty (σ.Equiv τ) then 1 else 0 := by
  have h := irrepMultiplicity_eq_charInner σ τ
  rw [charInner_character_eq_ite_nonempty_equiv τ σ] at h
  split_ifs at h ⊢ <;> exact_mod_cast h

/-- Multiplicities only depend on the isomorphism class of the ambient representation. -/
lemma irrepMultiplicity_congr {G V V' W : Type*} [Group G] [Fintype G] [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (σ : Representation ℂ G W)
    {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'} (φ : ρ.Equiv ρ') :
    irrepMultiplicity σ ρ = irrepMultiplicity σ ρ' := by
  apply Nat.cast_injective (R := ℂ)
  simp only [irrepMultiplicity_eq_charInner, char_iso φ]

/-- The character of a direct sum is the sum of the characters. -/
lemma character_prod {G V₁ V₂ : Type*} [Group G] [AddCommGroup V₁] [Module ℂ V₁]
    [FiniteDimensional ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂] [FiniteDimensional ℂ V₂]
    (ρ₁ : Representation ℂ G V₁) (ρ₂ : Representation ℂ G V₂) (g : G) :
    (ρ₁.prod ρ₂).character g = ρ₁.character g + ρ₂.character g :=
  LinearMap.trace_prodMap' (ρ₁ g) (ρ₂ g)

/-- Multiplicities are additive over direct sums. -/
lemma irrepMultiplicity_prod {G V₁ V₂ W : Type*} [Group G] [Fintype G] [AddCommGroup V₁]
    [Module ℂ V₁] [FiniteDimensional ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂] [FiniteDimensional ℂ V₂]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (σ : Representation ℂ G W)
    (ρ₁ : Representation ℂ G V₁) (ρ₂ : Representation ℂ G V₂) :
    irrepMultiplicity σ (ρ₁.prod ρ₂) = irrepMultiplicity σ ρ₁ + irrepMultiplicity σ ρ₂ := by
  apply Nat.cast_injective (R := ℂ)
  push_cast
  simp only [irrepMultiplicity_eq_charInner, charInner, character_prod, add_mul,
    Finset.sum_add_distrib, mul_add]

/-- A representation on a one-dimensional space is irreducible. -/
lemma isIrreducible_of_finrank_eq_one {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (h : finrank ℂ V = 1) : IsIrreducible ρ := by
  have : IsSimpleModule ℂ V := isSimpleModule_iff_finrank_eq_one.mpr h
  exact
    { exists_pair_ne := ⟨⊥, ⊤, fun hbt =>
        (bot_ne_top : (⊥ : Submodule ℂ V) ≠ ⊤) (congrArg Subrepresentation.toSubmodule hbt)⟩
      eq_bot_or_eq_top := fun W => (eq_bot_or_eq_top W.toSubmodule).imp
        (fun hW => Subrepresentation.toSubmodule_injective hW)
        (fun hW => Subrepresentation.toSubmodule_injective hW) }

/-!

## C. Group averaging and the vanishing-integral rule

-/

/-- The group average `|G|⁻¹ • ∑ g, ρ g` of a representation of a finite group. -/
def groupAverage {G V : Type*} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) : V →ₗ[ℂ] V :=
  (Nat.card G : ℂ)⁻¹ • ∑ g, ρ g

lemma groupAverage_apply {G V : Type*} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (v : V) :
    groupAverage ρ v = (Nat.card G : ℂ)⁻¹ • ∑ g, ρ g v := by
  simp [groupAverage, LinearMap.sum_apply]

/-- `groupAverage` agrees with Mathlib's `Representation.averageMap`. -/
lemma groupAverage_eq_averageMap {G V : Type*} [Group G] [Fintype G] [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ G V) [Invertible (Fintype.card G : ℂ)] :
    groupAverage ρ = averageMap ρ := by
  ext v
  simp [groupAverage_apply, averageMap, GroupAlgebra.average, map_sum, Nat.card_eq_fintype_card]

/-- The group average is the projection onto the invariant (totally symmetric) subspace. -/
lemma isProj_groupAverage {G V : Type*} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) : LinearMap.IsProj ρ.invariants (groupAverage ρ) := by
  have : Invertible (Fintype.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  rw [groupAverage_eq_averageMap]
  exact isProj_averageMap ρ

lemma groupAverage_apply_mem_invariants {G V : Type*} [Group G] [Fintype G] [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ G V) (v : V) : groupAverage ρ v ∈ ρ.invariants :=
  (isProj_groupAverage ρ).map_mem v

lemma groupAverage_apply_of_mem_invariants {G V : Type*} [Group G] [Fintype G] [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ G V) (v : V) (hv : v ∈ ρ.invariants) :
    groupAverage ρ v = v :=
  (isProj_groupAverage ρ).map_id v hv

lemma range_groupAverage {G V : Type*} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) : LinearMap.range (groupAverage ρ) = ρ.invariants :=
  (isProj_groupAverage ρ).range

lemma groupAverage_mul_self {G V : Type*} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) : groupAverage ρ * groupAverage ρ = groupAverage ρ :=
  (isProj_groupAverage ρ).isIdempotentElem

/-- The trivial (totally symmetric) character is the constant function `1`. -/
lemma character_trivial {G : Type*} [Group G] (g : G) :
    (trivial ℂ G ℂ).character g = 1 := by
  rw [character, show trivial ℂ G ℂ g = 1 from rfl, LinearMap.trace_one, finrank_self,
    Nat.cast_one]

/-- The dimension of the invariant subspace is `⟨χ, χ_trivial⟩`. -/
lemma finrank_invariants_eq_charInner_trivial {G V : Type*} [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) :
    (finrank ℂ ρ.invariants : ℂ) = charInner ρ.character (trivial ℂ G ℂ).character := by
  have : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  rw [← card_inv_mul_sum_char_eq_finrank ρ]
  simp [charInner, character_trivial]

lemma irrepMultiplicity_trivial_eq_finrank_invariants {G V : Type*} [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) :
    irrepMultiplicity (trivial ℂ G ℂ) ρ = finrank ℂ ρ.invariants := by
  exact_mod_cast (irrepMultiplicity_eq_charInner _ ρ).trans
    (finrank_invariants_eq_charInner_trivial ρ).symm

/-- The trivial representation does not occur iff `⟨χ, χ_trivial⟩ = 0`. -/
lemma irrepMultiplicity_trivial_eq_zero_iff {G V : Type*} [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) :
    irrepMultiplicity (trivial ℂ G ℂ) ρ = 0 ↔
      charInner ρ.character (trivial ℂ G ℂ).character = 0 := by
  rw [← irrepMultiplicity_eq_charInner, Nat.cast_eq_zero]

lemma invariants_eq_bot_of_charInner_trivial_eq_zero {G V : Type*} [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)
    (h : charInner ρ.character (trivial ℂ G ℂ).character = 0) : ρ.invariants = ⊥ := by
  rw [← finrank_invariants_eq_charInner_trivial, Nat.cast_eq_zero] at h
  exact Submodule.finrank_eq_zero.mp h

/-- **Vanishing rule**: if `⟨χ, χ_trivial⟩ = 0`, the group average is zero. -/
theorem groupAverage_eq_zero_of_charInner_trivial_eq_zero {G V : Type*} [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)
    (h : charInner ρ.character (trivial ℂ G ℂ).character = 0) : groupAverage ρ = 0 :=
  (isProj_groupAverage ρ).submodule_eq_bot_iff.mp
    (invariants_eq_bot_of_charInner_trivial_eq_zero ρ h)

lemma groupAverage_eq_zero_of_irrepMultiplicity_trivial_eq_zero {G V : Type*} [Group G]
    [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)
    (h : irrepMultiplicity (trivial ℂ G ℂ) ρ = 0) : groupAverage ρ = 0 :=
  groupAverage_eq_zero_of_charInner_trivial_eq_zero ρ
    ((irrepMultiplicity_trivial_eq_zero_iff ρ).mp h)

/-- A `G`-invariant linear form factors through the group average. -/
lemma linearForm_comp_groupAverage {G V : Type*} [Group G] [Fintype G] [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ G V) (ℓ : V →ₗ[ℂ] ℂ) (hℓ : ∀ g, ℓ ∘ₗ ρ g = ℓ) :
    ℓ ∘ₗ groupAverage ρ = ℓ := by
  ext v
  have hcard : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hg : ∀ g, ℓ (ρ g v) = ℓ v := fun g => LinearMap.congr_fun (hℓ g) v
  simp only [LinearMap.coe_comp, Function.comp_apply, groupAverage_apply, map_smul, map_sum, hg,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
  exact inv_mul_cancel_left₀ hcard _

/-- **Vanishing integral, finite form**: a `G`-invariant linear form (an "integral") on a
representation with no trivial component is zero. -/
theorem invariant_linearForm_eq_zero {G V : Type*} [Group G] [Fintype G] [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)
    (h : charInner ρ.character (trivial ℂ G ℂ).character = 0) (ℓ : V →ₗ[ℂ] ℂ)
    (hℓ : ∀ g, ℓ ∘ₗ ρ g = ℓ) : ℓ = 0 := by
  rw [← linearForm_comp_groupAverage ρ ℓ hℓ, groupAverage_eq_zero_of_charInner_trivial_eq_zero ρ h,
    LinearMap.comp_zero]

open TensorProduct in
/-- **Vanishing rule for a product**: if the product character `χ_ρ * χ_σ` has zero inner
product with the trivial character, the group average of every product `v ⊗ₜ w` vanishes. -/
theorem groupAverage_tprod_tmul_eq_zero {G V W : Type*} [Group G] [Fintype G] [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (h : charInner (ρ.character * σ.character) (trivial ℂ G ℂ).character = 0) (v : V) (w : W) :
    groupAverage (ρ.tprod σ) (v ⊗ₜ w) = 0 := by
  rw [groupAverage_eq_zero_of_charInner_trivial_eq_zero (ρ.tprod σ) (by rwa [char_tensor])]
  rfl

/-!

## D. Great orthogonality

-/

lemma groupAverage_linHom_apply {G V W : Type*} [Group G] [Fintype G] [AddCommGroup V]
    [Module ℂ V] [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G W)
    (ρ : Representation ℂ G V) (f : W →ₗ[ℂ] V) :
    groupAverage (linHom σ ρ) f = (Nat.card G : ℂ)⁻¹ • ∑ g, ρ g ∘ₗ f ∘ₗ σ g⁻¹ := by
  simp [groupAverage_apply]

lemma finrank_pos_of_isIrreducible {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) [IsIrreducible ρ] : 0 < finrank ℂ V := by
  refine Nat.pos_of_ne_zero fun h => ?_
  have : Subsingleton V := Module.finrank_zero_iff.mp h
  refine (bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤) ?_
  apply Subrepresentation.toSubmodule_injective
  exact Subsingleton.elim _ _

/-- **Great orthogonality, inequivalent case** (basis-free form): for non-isomorphic
irreducible `ρ` and `σ` and every linear map `f`, `∑ g, ρ g ∘ₗ f ∘ₗ σ g⁻¹ = 0`. Taking `f` to
be a matrix unit gives the matrix-coefficient form `∑ g, D_ρ(g)ᵢⱼ D_σ(g⁻¹)ₖₗ = 0` (not stated
separately here). -/
theorem sum_comp_comp_inv_eq_zero_of_not_nonempty_equiv {G V W : Type*} [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    [IsIrreducible ρ] [IsIrreducible σ] (h : ¬ Nonempty (σ.Equiv ρ)) (f : W →ₗ[ℂ] V) :
    ∑ g, ρ g ∘ₗ f ∘ₗ σ g⁻¹ = 0 := by
  have : IsEmpty (σ.Equiv ρ) := not_nonempty_iff.mp h
  have : Subsingleton (linHom σ ρ).invariants :=
    (invariantsEquivIntertwiningMap σ ρ).toEquiv.subsingleton
  have hmem := groupAverage_apply_mem_invariants (linHom σ ρ) f
  rw [Submodule.eq_bot_of_subsingleton (p := (linHom σ ρ).invariants), Submodule.mem_bot,
    groupAverage_linHom_apply] at hmem
  exact (smul_eq_zero.mp hmem).resolve_left
    (inv_ne_zero (Nat.cast_ne_zero.mpr Nat.card_pos.ne'))

/-- **Great orthogonality, equivalent case** (basis-free form): for irreducible `ρ` of
dimension `n` and every endomorphism `f`, `|G|⁻¹ • ∑ g, ρ g ∘ₗ f ∘ₗ ρ g⁻¹ = (tr f / n) • id`.
Taking `f` to be a matrix unit gives `|G|⁻¹ * ∑ g, D(g)ᵢⱼ D(g⁻¹)ₖₗ = δᵢₗ δⱼₖ / n` (not stated
separately here). -/
theorem groupAverage_comp_comp_inv_eq_trace_smul {G V : Type*} [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)
    [IsIrreducible ρ] (f : V →ₗ[ℂ] V) :
    (Nat.card G : ℂ)⁻¹ • ∑ g, ρ g ∘ₗ f ∘ₗ ρ g⁻¹ =
      (LinearMap.trace ℂ V f / finrank ℂ V) • LinearMap.id := by
  have hn : (finrank ℂ V : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (finrank_pos_of_isIrreducible ρ).ne'
  have hcard : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hid : (LinearMap.id : V →ₗ[ℂ] V) ∈ (linHom ρ ρ).invariants := fun g => by
    ext v
    simp
  have hid0 : (⟨LinearMap.id, hid⟩ : (linHom ρ ρ).invariants) ≠ 0 := by
    intro h0
    have h1 := congrArg (fun x : (linHom ρ ρ).invariants => LinearMap.trace ℂ V x.1) h0
    simp only [LinearMap.trace_id, ZeroMemClass.coe_zero, map_zero] at h1
    exact hn h1
  have hrank : finrank ℂ (linHom ρ ρ).invariants = 1 := by
    rw [(invariantsEquivIntertwiningMap ρ ρ).finrank_eq,
      IsIrreducible.finrank_intertwiningMap_self ρ]
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hid0).mp hrank
    ⟨_, groupAverage_apply_mem_invariants (linHom ρ ρ) f⟩
  have hc' : c • LinearMap.id = groupAverage (linHom ρ ρ) f := congrArg Subtype.val hc
  rw [groupAverage_linHom_apply] at hc'
  have htr : LinearMap.trace ℂ V ((Nat.card G : ℂ)⁻¹ • ∑ g, ρ g ∘ₗ f ∘ₗ ρ g⁻¹) =
      LinearMap.trace ℂ V f := by
    have hconj : ∀ g, LinearMap.trace ℂ V (ρ g ∘ₗ f ∘ₗ ρ g⁻¹) = LinearMap.trace ℂ V f := by
      intro g
      rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, LinearMap.trace_mul_comm,
        mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
    simp only [map_smul, map_sum, hconj, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      nsmul_eq_mul, ← Nat.card_eq_fintype_card]
    exact inv_mul_cancel_left₀ hcard _
  rw [← hc', map_smul, LinearMap.trace_id, smul_eq_mul] at htr
  rw [← hc', ← htr]
  congr 1
  exact (mul_div_cancel_right₀ c hn).symm

/-!

## E. Vibrational mode counting

Positions and displacements of `N` nuclei live in `Fin N → Fin 3 → ℝ`.

### E.1. Translations, rotations and the internal-mode space

-/

/-- The centre of mass `(∑ i, m i)⁻¹ • ∑ i, m i • x i` of masses `m i` at positions `x i`. -/
def centreOfMass {N : ℕ} (m : Fin N → ℝ) (x : Fin N → Fin 3 → ℝ) : Fin 3 → ℝ :=
  (∑ i, m i)⁻¹ • ∑ i, m i • x i

lemma sum_smul_sub_centreOfMass {N : ℕ} (m : Fin N → ℝ) (x : Fin N → Fin 3 → ℝ)
    (hm : ∑ i, m i ≠ 0) : ∑ i, m i • (x i - centreOfMass m x) = 0 := by
  simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul]
  rw [centreOfMass, smul_smul, mul_inv_cancel₀ hm, one_smul, sub_self]

/-- The rigid-translation map `v ↦ (fun _ => v)` into the displacement space. -/
def translationMap (N : ℕ) : (Fin 3 → ℝ) →ₗ[ℝ] (Fin N → Fin 3 → ℝ) :=
  LinearMap.pi fun _ => LinearMap.id

/-- The rigid-translation subspace: diagonal constant displacements. -/
def translationSubspace (N : ℕ) : Submodule ℝ (Fin N → Fin 3 → ℝ) :=
  LinearMap.range (translationMap N)

/-- The linearised rigid-rotation map `ω ↦ (fun i => ω ⨯₃ (x i - centreOfMass m x))`:
infinitesimal rotations with angular velocity `ω` about the centre of mass. -/
def rotationMap {N : ℕ} (m : Fin N → ℝ) (x : Fin N → Fin 3 → ℝ) :
    (Fin 3 → ℝ) →ₗ[ℝ] (Fin N → Fin 3 → ℝ) :=
  LinearMap.pi fun i => (crossProduct (R := ℝ)).flip (x i - centreOfMass m x)

lemma rotationMap_apply {N : ℕ} (m : Fin N → ℝ) (x : Fin N → Fin 3 → ℝ) (ω : Fin 3 → ℝ)
    (i : Fin N) : rotationMap m x ω i = ω ⨯₃ (x i - centreOfMass m x) := rfl

/-- The rigid-rotation subspace of the configuration `x` with masses `m`. -/
def rotationSubspace {N : ℕ} (m : Fin N → ℝ) (x : Fin N → Fin 3 → ℝ) :
    Submodule ℝ (Fin N → Fin 3 → ℝ) :=
  LinearMap.range (rotationMap m x)

/-- The internal-mode space: displacements modulo rigid translations and rigid rotations. Its
dimension is a kinematic count; zero or imaginary vibrational frequencies belong to the
dynamical (Hessian) problem and are neither counted by nor inferred from this quotient. -/
abbrev InternalModeSpace {N : ℕ} (m : Fin N → ℝ) (x : Fin N → Fin 3 → ℝ) :=
  (Fin N → Fin 3 → ℝ) ⧸ (translationSubspace N ⊔ rotationSubspace m x)

lemma finrank_displacement (N : ℕ) : finrank ℝ (Fin N → Fin 3 → ℝ) = 3 * N := by
  rw [Module.finrank_pi_fintype]
  simp [mul_comm]

lemma finrank_translationSubspace {N : ℕ} (hN : 0 < N) :
    finrank ℝ (translationSubspace N) = 3 := by
  have hinj : Function.Injective (translationMap N) := fun v w h => congrFun h ⟨0, hN⟩
  rw [translationSubspace, LinearMap.finrank_range_of_inj hinj, Module.finrank_fin_fun]

/-- Rigid translations and rotations about the centre of mass intersect trivially. -/
lemma translationSubspace_inf_rotationSubspace {N : ℕ} (m : Fin N → ℝ)
    (x : Fin N → Fin 3 → ℝ) (hm : ∀ i, 0 < m i) :
    translationSubspace N ⊓ rotationSubspace m x = ⊥ := by
  rw [eq_bot_iff]
  rintro u ⟨⟨v, rfl⟩, ⟨ω, hω⟩⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact (Submodule.mem_bot ℝ).mpr (Subsingleton.elim _ _)
  have hM : 0 < ∑ i, m i := Finset.sum_pos (fun i _ => hm i) ⟨⟨0, hN⟩, Finset.mem_univ _⟩
  have hv : ∀ i, ω ⨯₃ (x i - centreOfMass m x) = v := fun i => congrFun hω i
  have hsum : (∑ i, m i) • v = 0 := by
    calc (∑ i, m i) • v = ∑ i, m i • (ω ⨯₃ (x i - centreOfMass m x)) := by
          simp only [hv, Finset.sum_smul]
      _ = ω ⨯₃ ∑ i, m i • (x i - centreOfMass m x) := by simp only [map_sum, map_smul]
      _ = 0 := by rw [sum_smul_sub_centreOfMass m x hM.ne', map_zero]
  have hv0 : v = 0 := (smul_eq_zero.mp hsum).resolve_left hM.ne'
  subst hv0
  exact (Submodule.mem_bot ℝ).mpr (map_zero _)

lemma eq_smul_of_cross_eq_zero {ω r : Fin 3 → ℝ} (hω : ω ≠ 0) (h : ω ⨯₃ r = 0) :
    r = ((ω ⬝ᵥ r) / (ω ⬝ᵥ ω)) • ω := by
  have hωω : ω ⬝ᵥ ω ≠ 0 := fun h0 => hω (dotProduct_self_eq_zero.mp h0)
  have h2 := cross_cross_eq_smul_sub_smul' ω ω r
  rw [h, map_zero, eq_comm, sub_eq_zero] at h2
  rw [div_eq_inv_mul, mul_smul, h2, smul_smul, inv_mul_cancel₀ hωω, one_smul]

/-- A noncollinear configuration has at least three nuclei. -/
lemma three_le_of_not_collinear {N : ℕ} {x : Fin N → Fin 3 → ℝ}
    (hx : ¬ Collinear ℝ (Set.range x)) : 3 ≤ N := by
  by_contra hN
  apply hx
  rcases N with _ | N
  · rw [Set.range_eq_empty]
    exact collinear_empty ℝ _
  · rw [collinear_iff_finrank_le_one]
    have := finrank_vectorSpan_range_le ℝ x (n := N) (by simp)
    omega

/-- Two distinct positions require at least two nuclei. -/
lemma two_le_of_ne {N : ℕ} {x : Fin N → Fin 3 → ℝ} {a b : Fin N} (hab : x a ≠ x b) : 2 ≤ N := by
  have hne : a.val ≠ b.val := fun h => hab (congrArg x (Fin.ext h))
  have := a.isLt
  have := b.isLt
  omega

/-- A configuration whose affine span is all of `ℝ³` is noncollinear. -/
lemma not_collinear_of_affineSpan_eq_top {N : ℕ} {x : Fin N → Fin 3 → ℝ}
    (h : affineSpan ℝ (Set.range x) = ⊤) : ¬ Collinear ℝ (Set.range x) := by
  intro hc
  have h1 := collinear_iff_finrank_le_one.mp hc
  rw [← direction_affineSpan, h, AffineSubspace.direction_top, finrank_top,
    Module.finrank_fin_fun] at h1
  omega

/-- A nonzero cross product of two relative positions certifies noncollinearity. -/
lemma not_collinear_of_cross_ne_zero {N : ℕ} {x : Fin N → Fin 3 → ℝ} (i j k : Fin N)
    (h : (x j - x i) ⨯₃ (x k - x i) ≠ 0) : ¬ Collinear ℝ (Set.range x) := by
  intro hc
  obtain ⟨p₀, v, hv⟩ := (collinear_iff_exists_forall_eq_smul_vadd _).mp hc
  obtain ⟨ri, hi⟩ := hv (x i) ⟨i, rfl⟩
  obtain ⟨rj, hj⟩ := hv (x j) ⟨j, rfl⟩
  obtain ⟨rk, hk⟩ := hv (x k) ⟨k, rfl⟩
  apply h
  rw [hi, hj, hk]
  simp only [vadd_eq_add, add_sub_add_right_eq_sub, ← sub_smul, map_smul, LinearMap.smul_apply,
    cross_self, smul_zero]

/-- For a noncollinear configuration the rigid rotations form a `3`-dimensional subspace (no
hypothesis on the masses is needed here; positivity enters through
`translationSubspace_inf_rotationSubspace`). -/
lemma finrank_rotationSubspace_of_not_collinear {N : ℕ} (m : Fin N → ℝ)
    (x : Fin N → Fin 3 → ℝ) (hx : ¬ Collinear ℝ (Set.range x)) :
    finrank ℝ (rotationSubspace m x) = 3 := by
  have hinj : Function.Injective (rotationMap m x) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro ω hω
    by_contra hω0
    apply hx
    rw [collinear_iff_exists_forall_eq_smul_vadd]
    refine ⟨centreOfMass m x, ω, ?_⟩
    rintro _ ⟨i, rfl⟩
    have hi : ω ⨯₃ (x i - centreOfMass m x) = 0 := congrFun hω i
    exact ⟨_, by rw [vadd_eq_add, ← eq_smul_of_cross_eq_zero hω0 hi, sub_add_cancel]⟩
  rw [rotationSubspace, LinearMap.finrank_range_of_inj hinj, Module.finrank_fin_fun]

/-- For a linear configuration (collinear, with two distinct positions) the rigid rotations
form a `2`-dimensional subspace: rotations about the molecular axis do not move the nuclei. -/
lemma finrank_rotationSubspace_of_collinear {N : ℕ} (m : Fin N → ℝ) (x : Fin N → Fin 3 → ℝ)
    (hm : ∀ i, 0 < m i) (hx : Collinear ℝ (Set.range x)) {a b : Fin N} (hab : x a ≠ x b) :
    finrank ℝ (rotationSubspace m x) = 2 := by
  obtain ⟨p₀, v, hv⟩ := (collinear_iff_exists_forall_eq_smul_vadd _).mp hx
  choose t ht using fun i => hv (x i) ⟨i, rfl⟩
  simp only [vadd_eq_add] at ht
  have hv0 : v ≠ 0 := by
    rintro rfl
    apply hab
    rw [ht a, ht b, smul_zero, smul_zero]
  have hN : 0 < N := by have := two_le_of_ne hab; omega
  have hM : 0 < ∑ i, m i := Finset.sum_pos (fun i _ => hm i) ⟨⟨0, hN⟩, Finset.mem_univ _⟩
  have hsum : ∑ i, m i • x i = (∑ i, m i * t i) • v + (∑ i, m i) • p₀ := by
    rw [Finset.sum_smul, Finset.sum_smul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ht i, smul_add, smul_smul]
  have hc : centreOfMass m x = ((∑ j, m j)⁻¹ * ∑ j, m j * t j) • v + p₀ := by
    rw [centreOfMass, hsum, smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hM.ne', one_smul]
  have hrel : ∀ i, x i - centreOfMass m x = (t i - (∑ j, m j)⁻¹ * ∑ j, m j * t j) • v :=
    fun i => by
      rw [hc, ht i, sub_smul]
      abel
  have hker : LinearMap.ker (rotationMap m x) = ℝ ∙ v := by
    ext ω
    simp only [LinearMap.mem_ker, Submodule.mem_span_singleton]
    constructor
    · intro hω
      have hex : ∃ i, x i - centreOfMass m x ≠ 0 := by
        by_contra hall
        have hall' : ∀ i, x i - centreOfMass m x = 0 := fun i => by
          by_contra h
          exact hall ⟨i, h⟩
        apply hab
        rw [sub_eq_zero.mp (hall' a), sub_eq_zero.mp (hall' b)]
      obtain ⟨i, hi⟩ := hex
      have h1 : ω ⨯₃ (x i - centreOfMass m x) = 0 := congrFun hω i
      rw [hrel i] at h1 hi
      have hs : t i - (∑ j, m j)⁻¹ * ∑ j, m j * t j ≠ 0 := fun hs => hi (by rw [hs, zero_smul])
      rw [map_smul, smul_eq_zero] at h1
      have h3 : v ⨯₃ ω = 0 := by rw [← cross_anticomm, h1.resolve_left hs, neg_zero]
      exact ⟨_, (eq_smul_of_cross_eq_zero hv0 h3).symm⟩
    · rintro ⟨k, rfl⟩
      funext i
      rw [rotationMap_apply, hrel i]
      simp only [map_smul, LinearMap.smul_apply, cross_self, smul_zero]
      rfl
  have := LinearMap.finrank_range_add_finrank_ker (rotationMap m x)
  rw [hker, finrank_span_singleton hv0, Module.finrank_fin_fun] at this
  rw [rotationSubspace]
  omega

/-- Additive form of the `3N - 6` count for a noncollinear configuration. -/
theorem finrank_internalModeSpace_add_six {N : ℕ} (m : Fin N → ℝ) (x : Fin N → Fin 3 → ℝ)
    (hm : ∀ i, 0 < m i) (hx : ¬ Collinear ℝ (Set.range x)) :
    finrank ℝ (InternalModeSpace m x) + 6 = 3 * N := by
  unfold InternalModeSpace
  have hN : 3 ≤ N := three_le_of_not_collinear hx
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq (translationSubspace N)
    (rotationSubspace m x)
  rw [translationSubspace_inf_rotationSubspace m x hm, finrank_bot,
    finrank_translationSubspace (by omega), finrank_rotationSubspace_of_not_collinear m x hx]
    at hsup
  have hq := Submodule.finrank_quotient_add_finrank
    (translationSubspace N ⊔ rotationSubspace m x)
  rw [finrank_displacement] at hq
  omega

/-- **`3N - 6` rule**: a noncollinear configuration of `N` nuclei has `3 * N - 6` internal
modes (kinematic count). Since `3 ≤ N` holds automatically the natural-number subtraction is
exact; the additive form is `finrank_internalModeSpace_add_six`. -/
theorem finrank_internalModeSpace_of_not_collinear {N : ℕ} (m : Fin N → ℝ)
    (x : Fin N → Fin 3 → ℝ) (hm : ∀ i, 0 < m i) (hx : ¬ Collinear ℝ (Set.range x)) :
    finrank ℝ (InternalModeSpace m x) = 3 * N - 6 := by
  have := finrank_internalModeSpace_add_six m x hm hx
  omega

/-- The `3N - 6` rule under the hypothesis that the affine span is all of `ℝ³`. -/
lemma finrank_internalModeSpace_of_affineSpan_eq_top {N : ℕ} (m : Fin N → ℝ)
    (x : Fin N → Fin 3 → ℝ) (hm : ∀ i, 0 < m i) (hx : affineSpan ℝ (Set.range x) = ⊤) :
    finrank ℝ (InternalModeSpace m x) = 3 * N - 6 :=
  finrank_internalModeSpace_of_not_collinear m x hm (not_collinear_of_affineSpan_eq_top hx)

/-- Additive form of the `3N - 5` count for a linear configuration. -/
theorem finrank_internalModeSpace_add_five {N : ℕ} (m : Fin N → ℝ) (x : Fin N → Fin 3 → ℝ)
    (hm : ∀ i, 0 < m i) (hx : Collinear ℝ (Set.range x)) {a b : Fin N} (hab : x a ≠ x b) :
    finrank ℝ (InternalModeSpace m x) + 5 = 3 * N := by
  unfold InternalModeSpace
  have hN : 2 ≤ N := two_le_of_ne hab
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq (translationSubspace N)
    (rotationSubspace m x)
  rw [translationSubspace_inf_rotationSubspace m x hm, finrank_bot,
    finrank_translationSubspace (by omega), finrank_rotationSubspace_of_collinear m x hm hx hab]
    at hsup
  have hq := Submodule.finrank_quotient_add_finrank
    (translationSubspace N ⊔ rotationSubspace m x)
  rw [finrank_displacement] at hq
  omega

/-- **`3N - 5` rule**: a linear configuration (collinear with two distinct positions, so the
affine span is a line and `2 ≤ N`) has `3 * N - 5` internal modes (kinematic count). The
natural-number subtraction is exact; the additive form is `finrank_internalModeSpace_add_five`. -/
theorem finrank_internalModeSpace_of_collinear {N : ℕ} (m : Fin N → ℝ) (x : Fin N → Fin 3 → ℝ)
    (hm : ∀ i, 0 < m i) (hx : Collinear ℝ (Set.range x)) {a b : Fin N} (hab : x a ≠ x b) :
    finrank ℝ (InternalModeSpace m x) = 3 * N - 5 := by
  have := finrank_internalModeSpace_add_five m x hm hx hab
  omega

/-- The `3N - 5` rule under the hypothesis that the affine span is a line, i.e. its direction
`vectorSpan ℝ (Set.range x)` is one-dimensional. -/
lemma finrank_internalModeSpace_of_finrank_vectorSpan_eq_one {N : ℕ} (m : Fin N → ℝ)
    (x : Fin N → Fin 3 → ℝ) (hm : ∀ i, 0 < m i)
    (hx : finrank ℝ (vectorSpan ℝ (Set.range x)) = 1) :
    finrank ℝ (InternalModeSpace m x) = 3 * N - 5 := by
  have hcol : Collinear ℝ (Set.range x) := collinear_iff_finrank_le_one.mpr hx.le
  have hne : ∃ a b, x a ≠ x b := by
    by_contra hall
    have hsub : (Set.range x).Subsingleton := by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      by_contra hab
      exact hall ⟨a, b, hab⟩
    rw [vectorSpan_of_subsingleton ℝ hsub, finrank_bot] at hx
    exact zero_ne_one hx
  obtain ⟨a, b, hab⟩ := hne
  exact finrank_internalModeSpace_of_collinear m x hm hcol hab

/-!

### E.2. The point-group action and the internal-mode representation

A point group acts on a configuration through `R : G →* Matrix.orthogonalGroup (Fin 3) ℝ` and
a permutation `π : G →* Equiv.Perm (Fin N)` of the nuclei, with
`R g *ᵥ (x i - centreOfMass m x) = x (π g i) - centreOfMass m x`.

-/

/-- The cross product transforms with the cofactor matrix: `(Q a) ⨯₃ (Q b) = (adj Q)ᵀ (a ⨯₃ b)`. -/
lemma mulVec_cross_mulVec (Q : Matrix (Fin 3) (Fin 3) ℝ) (a b : Fin 3 → ℝ) :
    (Q *ᵥ a) ⨯₃ (Q *ᵥ b) = (adjugate Q)ᵀ *ᵥ (a ⨯₃ b) := by
  ext i
  fin_cases i <;>
  · simp [cross_apply, adjugate_fin_three, mulVec, dotProduct, Fin.sum_univ_three]
    ring

/-- An orthogonal matrix `Q` maps cross products to `det Q •` cross products. -/
lemma mulVec_cross_mulVec_of_mem_orthogonalGroup {Q : Matrix (Fin 3) (Fin 3) ℝ}
    (hQ : Q ∈ Matrix.orthogonalGroup (Fin 3) ℝ) (a b : Fin 3 → ℝ) :
    (Q *ᵥ a) ⨯₃ (Q *ᵥ b) = Q.det • (Q *ᵥ (a ⨯₃ b)) := by
  have h2 : Qᵀ * Q = 1 := (Matrix.mem_orthogonalGroup_iff' _ _).mp hQ
  have hadj : adjugate Q = Q.det • Qᵀ := by
    calc adjugate Q = Qᵀ * Q * adjugate Q := by rw [h2, Matrix.one_mul]
      _ = Qᵀ * (Q.det • 1) := by rw [Matrix.mul_assoc, mul_adjugate]
      _ = Q.det • Qᵀ := by rw [Matrix.mul_smul, Matrix.mul_one]
  rw [mulVec_cross_mulVec, hadj, transpose_smul, transpose_transpose, smul_mulVec]

lemma det_mul_self_of_mem_orthogonalGroup {Q : Matrix (Fin 3) (Fin 3) ℝ}
    (hQ : Q ∈ Matrix.orthogonalGroup (Fin 3) ℝ) : Q.det * Q.det = 1 := by
  have h2 : Qᵀ * Q = 1 := (Matrix.mem_orthogonalGroup_iff' _ _).mp hQ
  have := congrArg Matrix.det h2
  rwa [det_mul, det_transpose, det_one] at this

/-- The Cartesian displacement representation of a point group `R` that permutes the nuclei by
`π`: `(g • u) i = R g *ᵥ u ((π g)⁻¹ i)`. -/
def displacementRepresentation {G : Type*} [Group G] {N : ℕ}
    (R : G →* Matrix.orthogonalGroup (Fin 3) ℝ) (π : G →* Equiv.Perm (Fin N)) :
    Representation ℝ G (Fin N → Fin 3 → ℝ) where
  toFun g := LinearMap.pi fun i =>
    Matrix.toLin' (R g : Matrix (Fin 3) (Fin 3) ℝ) ∘ₗ LinearMap.proj ((π g)⁻¹ i)
  map_one' := LinearMap.ext fun u => funext fun i => by simp
  map_mul' g h := LinearMap.ext fun u => funext fun i => by
    simp [Matrix.mulVec_mulVec, _root_.mul_inv_rev]

lemma displacementRepresentation_apply {G : Type*} [Group G] {N : ℕ}
    (R : G →* Matrix.orthogonalGroup (Fin 3) ℝ) (π : G →* Equiv.Perm (Fin N)) (g : G)
    (u : Fin N → Fin 3 → ℝ) (i : Fin N) :
    displacementRepresentation R π g u i = (R g : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ u ((π g)⁻¹ i) :=
  show Matrix.toLin' (R g : Matrix (Fin 3) (Fin 3) ℝ) (u ((π g)⁻¹ i)) = _ from
    Matrix.toLin'_apply _ _

/-- Rigid translations transform like the vector representation `x, y, z`. -/
lemma displacementRepresentation_translationMap {G : Type*} [Group G] {N : ℕ}
    (R : G →* Matrix.orthogonalGroup (Fin 3) ℝ) (π : G →* Equiv.Perm (Fin N)) (g : G)
    (v : Fin 3 → ℝ) :
    displacementRepresentation R π g (translationMap N v) =
      translationMap N ((R g : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v) :=
  funext fun i => displacementRepresentation_apply R π g _ i

/-- Rigid rotations transform like an axial vector (`Rx, Ry, Rz`): `ω ↦ det (R g) • R g ω`,
provided `R g` maps relative positions to relative positions along `π g`. -/
lemma displacementRepresentation_rotationMap {G : Type*} [Group G] {N : ℕ}
    (R : G →* Matrix.orthogonalGroup (Fin 3) ℝ) (π : G →* Equiv.Perm (Fin N))
    (m : Fin N → ℝ) (x : Fin N → Fin 3 → ℝ)
    (hx : ∀ g i, (R g : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ (x i - centreOfMass m x) =
      x (π g i) - centreOfMass m x) (g : G) (ω : Fin 3 → ℝ) :
    displacementRepresentation R π g (rotationMap m x ω) =
      rotationMap m x ((R g : Matrix (Fin 3) (Fin 3) ℝ).det •
        ((R g : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ ω)) := by
  funext i
  set Q : Matrix (Fin 3) (Fin 3) ℝ := (R g : Matrix (Fin 3) (Fin 3) ℝ) with hQdef
  have hQ : Q ∈ Matrix.orthogonalGroup (Fin 3) ℝ := (R g).2
  have hrel : Q *ᵥ (x ((π g)⁻¹ i) - centreOfMass m x) = x i - centreOfMass m x := by
    rw [hx g, Equiv.Perm.inv_def, Equiv.apply_symm_apply]
  rw [displacementRepresentation_apply, rotationMap_apply, rotationMap_apply, ← hQdef,
    LinearMap.map_smul_of_tower, LinearMap.smul_apply, ← hrel,
    mulVec_cross_mulVec_of_mem_orthogonalGroup hQ, smul_smul,
    det_mul_self_of_mem_orthogonalGroup hQ, one_smul]

lemma translationSubspace_le_comap {G : Type*} [Group G] {N : ℕ}
    (R : G →* Matrix.orthogonalGroup (Fin 3) ℝ) (π : G →* Equiv.Perm (Fin N)) (g : G) :
    translationSubspace N ≤
      (translationSubspace N).comap (displacementRepresentation R π g) := by
  rintro _ ⟨v, rfl⟩
  exact ⟨_, (displacementRepresentation_translationMap R π g v).symm⟩

lemma rotationSubspace_le_comap {G : Type*} [Group G] {N : ℕ}
    (R : G →* Matrix.orthogonalGroup (Fin 3) ℝ) (π : G →* Equiv.Perm (Fin N))
    (m : Fin N → ℝ) (x : Fin N → Fin 3 → ℝ)
    (hx : ∀ g i, (R g : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ (x i - centreOfMass m x) =
      x (π g i) - centreOfMass m x) (g : G) :
    rotationSubspace m x ≤ (rotationSubspace m x).comap (displacementRepresentation R π g) := by
  rintro _ ⟨ω, rfl⟩
  exact ⟨_, (displacementRepresentation_rotationMap R π m x hx g ω).symm⟩

/-- The internal-mode representation: the displacement representation on the quotient by the
rigid translations and rotations (`Representation.quotient`). Its carrier is
`InternalModeSpace m x`, of dimension `3 * N - 6` (noncollinear) or `3 * N - 5` (linear). -/
def internalModeRepresentation {G : Type*} [Group G] {N : ℕ}
    (R : G →* Matrix.orthogonalGroup (Fin 3) ℝ) (π : G →* Equiv.Perm (Fin N))
    (m : Fin N → ℝ) (x : Fin N → Fin 3 → ℝ)
    (hx : ∀ g i, (R g : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ (x i - centreOfMass m x) =
      x (π g i) - centreOfMass m x) :
    Representation ℝ G (InternalModeSpace m x) :=
  (displacementRepresentation R π).quotient (translationSubspace N ⊔ rotationSubspace m x)
    fun g => sup_le
      ((translationSubspace_le_comap R π g).trans (Submodule.comap_mono le_sup_left))
      ((rotationSubspace_le_comap R π m x hx g).trans (Submodule.comap_mono le_sup_right))

lemma internalModeRepresentation_mk {G : Type*} [Group G] {N : ℕ}
    (R : G →* Matrix.orthogonalGroup (Fin 3) ℝ) (π : G →* Equiv.Perm (Fin N))
    (m : Fin N → ℝ) (x : Fin N → Fin 3 → ℝ)
    (hx : ∀ g i, (R g : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ (x i - centreOfMass m x) =
      x (π g i) - centreOfMass m x) (g : G) (u : Fin N → Fin 3 → ℝ) :
    internalModeRepresentation R π m x hx g (Submodule.Quotient.mk u) =
      Submodule.Quotient.mk (displacementRepresentation R π g u) :=
  rfl

/-!

## F. IR and Raman activity

A point group is given by `R : G →* Matrix.orthogonalGroup (Fin 3) ℝ`, its action on Cartesian
coordinates `x, y, z` (index `0, 1, 2`) about the centre of mass.

-/

/-- The Cartesian matrices of a point group, viewed as complex matrices. -/
def cartesianMatrix {G : Type*} [Group G] (R : G →* Matrix.orthogonalGroup (Fin 3) ℝ) :
    G →* Matrix (Fin 3) (Fin 3) ℂ :=
  (RingHom.mapMatrix Complex.ofRealHom).toMonoidHom.comp
    ((Matrix.orthogonalGroup (Fin 3) ℝ).subtype.comp R)

lemma cartesianMatrix_apply {G : Type*} [Group G] (R : G →* Matrix.orthogonalGroup (Fin 3) ℝ)
    (g : G) : cartesianMatrix R g = (R g : Matrix (Fin 3) (Fin 3) ℝ).map Complex.ofRealHom :=
  rfl

lemma cartesianMatrix_inv {G : Type*} [Group G] (R : G →* Matrix.orthogonalGroup (Fin 3) ℝ)
    (g : G) : cartesianMatrix R g⁻¹ = (cartesianMatrix R g)ᵀ := by
  rw [cartesianMatrix_apply, cartesianMatrix_apply, map_inv, Matrix.UnitaryGroup.inv_val,
    star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial, transpose_map]

/-- The vector representation: the point group acting on Cartesian `x, y, z`. -/
def vectorRepresentation {G : Type*} [Group G] (R : G →* Matrix.orthogonalGroup (Fin 3) ℝ) :
    Representation ℂ G (Fin 3 → ℂ) where
  toFun g := Matrix.toLin' (cartesianMatrix R g)
  map_one' := by rw [map_one, Matrix.toLin'_one]; rfl
  map_mul' g h := by rw [map_mul, Matrix.toLin'_mul]; rfl

lemma vectorRepresentation_apply {G : Type*} [Group G]
    (R : G →* Matrix.orthogonalGroup (Fin 3) ℝ) (g : G) (v : Fin 3 → ℂ) :
    vectorRepresentation R g v = cartesianMatrix R g *ᵥ v :=
  Matrix.toLin'_apply _ _

/-- The vector character is the trace of the real Cartesian matrix; in particular it is
real-valued. -/
lemma character_vectorRepresentation {G : Type*} [Group G]
    (R : G →* Matrix.orthogonalGroup (Fin 3) ℝ) (g : G) :
    (vectorRepresentation R).character g = ((R g : Matrix (Fin 3) (Fin 3) ℝ).trace : ℂ) := by
  rw [character, show vectorRepresentation R g = Matrix.toLin' (cartesianMatrix R g) from rfl,
    Matrix.trace_toLin'_eq, cartesianMatrix_apply]
  simp [Matrix.trace, Complex.ofReal_sum]

/-- The tensor square of the vector representation on `3 × 3` matrices, `M ↦ A * M * Aᵀ`,
under the identification `v ⊗ w ↦ vecMulVec v w` (see `tensorSquareRepresentation_vecMulVec`). -/
def tensorSquareRepresentation {G : Type*} [Group G]
    (R : G →* Matrix.orthogonalGroup (Fin 3) ℝ) :
    Representation ℂ G (Matrix (Fin 3) (Fin 3) ℂ) where
  toFun g :=
    { toFun := fun M => cartesianMatrix R g * M * (cartesianMatrix R g)ᵀ
      map_add' := fun M N => by rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c M => by rw [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply] }
  map_one' := LinearMap.ext fun M => by simp
  map_mul' g h := LinearMap.ext fun M => by
    simp [transpose_mul, Matrix.mul_assoc]

lemma tensorSquareRepresentation_apply {G : Type*} [Group G]
    (R : G →* Matrix.orthogonalGroup (Fin 3) ℝ) (g : G) (M : Matrix (Fin 3) (Fin 3) ℂ) :
    tensorSquareRepresentation R g M = cartesianMatrix R g * M * (cartesianMatrix R g)ᵀ :=
  rfl

/-- On rank-one matrices `vecMulVec v w` (pure tensors `v ⊗ w`) the tensor-square action is
`v ⊗ w ↦ (g • v) ⊗ (g • w)`. -/
lemma tensorSquareRepresentation_vecMulVec {G : Type*} [Group G]
    (R : G →* Matrix.orthogonalGroup (Fin 3) ℝ) (g : G) (v w : Fin 3 → ℂ) :
    tensorSquareRepresentation R g (vecMulVec v w) =
      vecMulVec (vectorRepresentation R g v) (vectorRepresentation R g w) := by
  rw [tensorSquareRepresentation_apply, vectorRepresentation_apply, vectorRepresentation_apply,
    Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose]

/-- The symmetric `3 × 3` complex matrices, the carrier of the symmetric square. -/
def symmetricMatrices : Submodule ℂ (Matrix (Fin 3) (Fin 3) ℂ) where
  carrier := {S | Sᵀ = S}
  add_mem' := fun {S T} (hS : Sᵀ = S) (hT : Tᵀ = T) =>
    show (S + T)ᵀ = S + T by rw [transpose_add, hS, hT]
  zero_mem' := transpose_zero
  smul_mem' := fun c {S} (hS : Sᵀ = S) => show (c • S)ᵀ = c • S by rw [transpose_smul, hS]

lemma mem_symmetricMatrices (S : Matrix (Fin 3) (Fin 3) ℂ) :
    S ∈ symmetricMatrices ↔ Sᵀ = S :=
  Iff.rfl

/-- Coordinates `(S₀₀, S₁₁, S₂₂, S₀₁, S₀₂, S₁₂)` on symmetric matrices. In the quadratic form
`rᵀ S r` (`quadraticFormOf`) the coefficients of `x², y², z²` are `S₀₀, S₁₁, S₂₂` and the
coefficients of `xy, xz, yz` are `2 * S₀₁, 2 * S₀₂, 2 * S₁₂`. -/
def symmetricMatricesEquiv : symmetricMatrices ≃ₗ[ℂ] (Fin 6 → ℂ) where
  toFun S := ![S.1 0 0, S.1 1 1, S.1 2 2, S.1 0 1, S.1 0 2, S.1 1 2]
  map_add' S T := by
    ext k
    fin_cases k <;> rfl
  map_smul' c S := by
    ext k
    fin_cases k <;> rfl
  invFun v := ⟨!![v 0, v 3, v 4; v 3, v 1, v 5; v 4, v 5, v 2], by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl⟩
  left_inv S := by
    obtain ⟨S, hS⟩ := S
    have h : ∀ i j, S j i = S i j := fun i j => congrFun (congrFun hS i) j
    ext i j
    fin_cases i <;> fin_cases j <;> first | rfl | exact h _ _
  right_inv v := by
    ext k
    fin_cases k <;> rfl

/-- The symmetric square of `ℂ³` is `6`-dimensional. -/
lemma finrank_symmetricMatrices : finrank ℂ symmetricMatrices = 6 := by
  rw [symmetricMatricesEquiv.finrank_eq, Module.finrank_fin_fun]

/-- The symmetric-square (quadratic-form) representation `S ↦ A * S * Aᵀ` on symmetric
matrices. For orthogonal `A` this is the action on quadratic forms `r ↦ rᵀ S r`
(`quadraticFormOf_tensorSquareRepresentation`) and the transformation law of a polarizability
tensor. -/
def quadraticRepresentation {G : Type*} [Group G] (R : G →* Matrix.orthogonalGroup (Fin 3) ℝ) :
    Representation ℂ G symmetricMatrices :=
  (tensorSquareRepresentation R).subrepresentation symmetricMatrices fun g S (hS : Sᵀ = S) =>
    show (cartesianMatrix R g * S * (cartesianMatrix R g)ᵀ)ᵀ =
        cartesianMatrix R g * S * (cartesianMatrix R g)ᵀ by
      rw [transpose_mul, transpose_mul, transpose_transpose, hS, Matrix.mul_assoc]

lemma quadraticRepresentation_apply_coe {G : Type*} [Group G]
    (R : G →* Matrix.orthogonalGroup (Fin 3) ℝ) (g : G) (S : symmetricMatrices) :
    ((quadraticRepresentation R g S : symmetricMatrices) : Matrix (Fin 3) (Fin 3) ℂ) =
      cartesianMatrix R g * S * (cartesianMatrix R g)ᵀ :=
  rfl

/-- The quadratic form `r ↦ r ⬝ᵥ S *ᵥ r` of a matrix `S`. -/
def quadraticFormOf (S : Matrix (Fin 3) (Fin 3) ℂ) (r : Fin 3 → ℂ) : ℂ :=
  r ⬝ᵥ S *ᵥ r

/-- The tensor-square action is the action on quadratic forms, `(g • q)(r) = q (g⁻¹ • r)`. -/
lemma quadraticFormOf_tensorSquareRepresentation {G : Type*} [Group G]
    (R : G →* Matrix.orthogonalGroup (Fin 3) ℝ) (g : G) (S : Matrix (Fin 3) (Fin 3) ℂ)
    (r : Fin 3 → ℂ) :
    quadraticFormOf (tensorSquareRepresentation R g S) r =
      quadraticFormOf S (vectorRepresentation R g⁻¹ r) := by
  rw [quadraticFormOf, quadraticFormOf, tensorSquareRepresentation_apply,
    vectorRepresentation_apply, cartesianMatrix_inv, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]

/-- **IR activity (dipole model, MOD)**: a vibrational mode transforming as `σ` (an irreducible
component of the internal-mode representation) is IR-active iff `σ` occurs in the vector
representation, i.e. transforms like `x`, `y` or `z`. This is a definition inside the dipole
model; it does not predict intensities or observation, and labels of `σ` refer to the fixed
axis convention of `R`. The predicate is stated for every `σ`; its selection-rule reading
requires `σ` to be irreducible, and a claim about a vibrational mode additionally requires `σ`
to occur in the (complexified) internal-mode representation `internalModeRepresentation`. -/
def IsIRActive {G W : Type*} [Group G] [AddCommGroup W] [Module ℂ W]
    (R : G →* Matrix.orthogonalGroup (Fin 3) ℝ) (σ : Representation ℂ G W) : Prop :=
  0 < irrepMultiplicity σ (vectorRepresentation R)

/-- **Raman activity (polarizability model, MOD)**: a vibrational mode transforming as `σ` is
Raman-active iff `σ` occurs in the symmetric-square (quadratic-form) representation, i.e.
transforms like a quadratic form in `x, y, z`. This is a definition inside the polarizability
model; it does not predict intensities or observation. The predicate is stated for every `σ`;
its selection-rule reading requires `σ` to be irreducible, and a claim about a vibrational mode
additionally requires `σ` to occur in the (complexified) internal-mode representation
`internalModeRepresentation`. -/
def IsRamanActive {G W : Type*} [Group G] [AddCommGroup W] [Module ℂ W]
    (R : G →* Matrix.orthogonalGroup (Fin 3) ℝ) (σ : Representation ℂ G W) : Prop :=
  0 < irrepMultiplicity σ (quadraticRepresentation R)

lemma isIRActive_iff_charInner_ne_zero {G W : Type*} [Group G] [Fintype G] [AddCommGroup W]
    [Module ℂ W] [FiniteDimensional ℂ W] (R : G →* Matrix.orthogonalGroup (Fin 3) ℝ)
    (σ : Representation ℂ G W) :
    IsIRActive R σ ↔ charInner (vectorRepresentation R).character σ.character ≠ 0 := by
  rw [IsIRActive, ← irrepMultiplicity_eq_charInner, Nat.cast_ne_zero, Nat.pos_iff_ne_zero]

lemma isRamanActive_iff_charInner_ne_zero {G W : Type*} [Group G] [Fintype G] [AddCommGroup W]
    [Module ℂ W] [FiniteDimensional ℂ W] (R : G →* Matrix.orthogonalGroup (Fin 3) ℝ)
    (σ : Representation ℂ G W) :
    IsRamanActive R σ ↔ charInner (quadraticRepresentation R).character σ.character ≠ 0 := by
  rw [IsRamanActive, ← irrepMultiplicity_eq_charInner, Nat.cast_ne_zero, Nat.pos_iff_ne_zero]

/-!

## G. Worked example: the inversion group `Ci`

`Ci = {E, i}` is realised as `ℤˣ = {1, -1}`, with `-1` acting on Cartesian space by the
inversion `r ↦ -r` through the centre of mass at the origin. The irreps are `Ag` (trivial,
gerade) and `Au` (sign, ungerade); inversion labels do not depend on the choice of axes.

-/

lemma sum_units_int {M : Type*} [AddCommMonoid M] (f : ℤˣ → M) : ∑ u, f u = f 1 + f (-1) := by
  have huniv : (Finset.univ : Finset ℤˣ) = {1, -1} := by
    ext u
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact Int.units_eq_one_or u
  rw [huniv, Finset.sum_pair (by decide)]

/-- The inversion point group `Ci`: `u : ℤˣ` acts on Cartesian space by `u • 1`. -/
def inversionAction : ℤˣ →* Matrix.orthogonalGroup (Fin 3) ℝ where
  toFun u := ⟨((u : ℤ) : ℝ) • 1, by
    rw [Matrix.mem_orthogonalGroup_iff, transpose_smul, transpose_one, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.one_mul, smul_smul, ← Int.cast_mul, ← Units.val_mul,
      Int.units_mul_self, Units.val_one, Int.cast_one, one_smul]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' u v := Subtype.ext (by simp [smul_smul, mul_comm])

lemma cartesianMatrix_inversionAction (u : ℤˣ) :
    cartesianMatrix inversionAction u = ((u : ℤ) : ℂ) • 1 := by
  ext i j
  rw [cartesianMatrix_apply]
  by_cases hij : i = j <;> simp [inversionAction, hij]

/-- `Ag`: the totally symmetric irrep of `Ci`. -/
abbrev inversionAg : Representation ℂ ℤˣ ℂ :=
  trivial ℂ ℤˣ ℂ

/-- `Au`: the irrep of `Ci` on which the inversion acts by `-1`. -/
def inversionAu : Representation ℂ ℤˣ ℂ where
  toFun u := ((u : ℤ) : ℂ) • LinearMap.id
  map_one' := LinearMap.ext fun z => by simp
  map_mul' u v := LinearMap.ext fun z => by
    change (((u * v : ℤˣ) : ℤ) : ℂ) • z = ((u : ℤ) : ℂ) • ((v : ℤ) : ℂ) • z
    rw [Units.val_mul, Int.cast_mul, mul_smul]

/-- `Ag` is irreducible. -/
instance isIrreducible_inversionAg : IsIrreducible inversionAg :=
  isIrreducible_of_finrank_eq_one _ (finrank_self ℂ)

/-- `Au` is irreducible. -/
instance isIrreducible_inversionAu : IsIrreducible inversionAu :=
  isIrreducible_of_finrank_eq_one _ (finrank_self ℂ)

lemma character_inversionAu (u : ℤˣ) : inversionAu.character u = ((u : ℤ) : ℂ) := by
  rw [character, show inversionAu u = ((u : ℤ) : ℂ) • LinearMap.id from rfl, map_smul,
    LinearMap.trace_id, finrank_self, Nat.cast_one, smul_eq_mul, mul_one]

lemma character_vectorRepresentation_inversionAction (u : ℤˣ) :
    (vectorRepresentation inversionAction).character u = 3 * ((u : ℤ) : ℂ) := by
  rw [character_vectorRepresentation]
  simp [inversionAction, trace_smul, mul_comm]

lemma quadraticRepresentation_inversionAction (u : ℤˣ) :
    quadraticRepresentation inversionAction u = 1 := by
  refine LinearMap.ext fun S => Subtype.ext ?_
  rw [quadraticRepresentation_apply_coe, cartesianMatrix_inversionAction, transpose_smul,
    transpose_one, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul,
    ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one, one_smul]
  rfl

lemma character_quadraticRepresentation_inversionAction (u : ℤˣ) :
    (quadraticRepresentation inversionAction).character u = 6 := by
  rw [character, quadraticRepresentation_inversionAction, LinearMap.trace_one,
    finrank_symmetricMatrices]
  norm_num

/-- Decomposition of the vector representation of `Ci`: `Γ_xyz = 0 Ag + 3 Au`. -/
lemma inversion_vector_decomposition :
    irrepMultiplicity inversionAg (vectorRepresentation inversionAction) = 0 ∧
      irrepMultiplicity inversionAu (vectorRepresentation inversionAction) = 3 := by
  constructor <;> apply Nat.cast_injective (R := ℂ) <;>
    rw [irrepMultiplicity_eq_charInner, charInner, sum_units_int, Nat.card_eq_fintype_card,
      Fintype.card_units_int] <;>
    simp only [character_vectorRepresentation_inversionAction, character_trivial,
      character_inversionAu] <;>
    norm_num

/-- Decomposition of the quadratic representation of `Ci`: `Γ_quad = 6 Ag + 0 Au`. -/
lemma inversion_quadratic_decomposition :
    irrepMultiplicity inversionAg (quadraticRepresentation inversionAction) = 6 ∧
      irrepMultiplicity inversionAu (quadraticRepresentation inversionAction) = 0 := by
  constructor <;> apply Nat.cast_injective (R := ℂ) <;>
    rw [irrepMultiplicity_eq_charInner, charInner, sum_units_int, Nat.card_eq_fintype_card,
      Fintype.card_units_int] <;>
    simp only [character_quadraticRepresentation_inversionAction, character_trivial,
      character_inversionAu] <;>
    norm_num

/-- Mutual exclusion in `Ci`: `Ag` is Raman-active and IR-inactive, `Au` is IR-active and
Raman-inactive. -/
lemma inversion_activity :
    IsRamanActive inversionAction inversionAg ∧ ¬ IsIRActive inversionAction inversionAg ∧
      IsIRActive inversionAction inversionAu ∧ ¬ IsRamanActive inversionAction inversionAu := by
  simp only [IsIRActive, IsRamanActive, inversion_vector_decomposition.1,
    inversion_vector_decomposition.2, inversion_quadratic_decomposition.1,
    inversion_quadratic_decomposition.2]
  decide

end Chemistry.Symmetry
