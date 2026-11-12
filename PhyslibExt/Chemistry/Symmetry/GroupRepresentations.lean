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
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.RepresentationTheory.Character
public import Mathlib.RingTheory.SimpleModule.Rank
public import MathlibExt.RepresentationTheory.CharacterInnerProduct

/-!

# Molecular symmetry and finite group representations

Point-group characters, vibrational mode counting, vanishing integrals and IR/Raman activity.

## i. Overview

A point group is modelled as a finite group `G`; its representations are finite-dimensional
complex representations `ρ : Representation ℂ G V`. The generic finite-group character theory
used here (character inner product, irrep multiplicities, group averaging, great
orthogonality) lives in `MathlibExt/RepresentationTheory/CharacterInnerProduct.lean`
(`CharacterTheory`); in particular `irrepMultiplicity σ ρ` there requires `σ` irreducible,
and the unrestricted intertwining-space rank is `intertwiningRank σ ρ`.

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

- `Chemistry.Symmetry.finrank_internalModeSpace_of_not_collinear` (`3 * N - 6`) and
  `Chemistry.Symmetry.finrank_internalModeSpace_of_collinear` (`3 * N - 5`).
- `Chemistry.Symmetry.internalModeRepresentation` : the internal-mode representation, the
  quotient of the displacement representation by translations (`x, y, z`) and rotations
  (`Rx, Ry, Rz`).
- `Chemistry.Symmetry.IsIRActive`, `Chemistry.Symmetry.IsRamanActive` and
  `Chemistry.Symmetry.inversion_activity`.

## iii. Table of contents

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

open CharacterTheory

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

/-- **IR activity (dipole model, MOD)**: a vibrational mode transforming as the irreducible
representation `σ` (an irreducible component of the internal-mode representation) is
IR-active iff `σ` occurs in the vector representation, i.e. transforms like `x`, `y` or `z`.
This is a definition inside the dipole model; it does not predict intensities or observation,
and labels of `σ` refer to the fixed axis convention of `R`. The `IsIrreducible σ` argument
is part of the predicate: activity is only defined for irreps, so a reducible `σ` with a
nonzero intertwining space cannot be classified as active. A claim about a vibrational mode
additionally requires `σ` to occur in the (complexified) internal-mode representation
`internalModeRepresentation`. -/
def IsIRActive {G W : Type*} [Group G] [AddCommGroup W] [Module ℂ W]
    (R : G →* Matrix.orthogonalGroup (Fin 3) ℝ) (σ : Representation ℂ G W)
    [IsIrreducible σ] : Prop :=
  0 < irrepMultiplicity σ (vectorRepresentation R)

/-- **Raman activity (polarizability model, MOD)**: a vibrational mode transforming as the
irreducible representation `σ` is Raman-active iff `σ` occurs in the symmetric-square
(quadratic-form) representation, i.e. transforms like a quadratic form in `x, y, z`. This is
a definition inside the polarizability model; it does not predict intensities or observation.
The `IsIrreducible σ` argument is part of the predicate, as for `IsIRActive`. A claim about a
vibrational mode additionally requires `σ` to occur in the (complexified) internal-mode
representation `internalModeRepresentation`. -/
def IsRamanActive {G W : Type*} [Group G] [AddCommGroup W] [Module ℂ W]
    (R : G →* Matrix.orthogonalGroup (Fin 3) ℝ) (σ : Representation ℂ G W)
    [IsIrreducible σ] : Prop :=
  0 < irrepMultiplicity σ (quadraticRepresentation R)

lemma isIRActive_iff_charInner_ne_zero {G W : Type*} [Group G] [Fintype G] [AddCommGroup W]
    [Module ℂ W] [FiniteDimensional ℂ W] (R : G →* Matrix.orthogonalGroup (Fin 3) ℝ)
    (σ : Representation ℂ G W) [IsIrreducible σ] :
    IsIRActive R σ ↔ charInner (vectorRepresentation R).character σ.character ≠ 0 := by
  rw [IsIRActive, ← irrepMultiplicity_eq_charInner, Nat.cast_ne_zero, Nat.pos_iff_ne_zero]

lemma isRamanActive_iff_charInner_ne_zero {G W : Type*} [Group G] [Fintype G] [AddCommGroup W]
    [Module ℂ W] [FiniteDimensional ℂ W] (R : G →* Matrix.orthogonalGroup (Fin 3) ℝ)
    (σ : Representation ℂ G W) [IsIrreducible σ] :
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
