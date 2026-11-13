/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RepresentationTheory.CharacterInvEqConj
public import MathlibExt.RepresentationTheory.RepresentationMultiplicity
public import Mathlib.RepresentationTheory.Character
public import Mathlib.RingTheory.SimpleModule.Rank

/-!
# Character inner product, multiplicities and group averaging

Generic finite-group representation theory over the complex numbers: the character
inner product, the intertwining-space rank and the multiplicity of an irreducible
representation, orthogonality of irreducible characters, the reduction formula,
group averaging and the vanishing-integral rule, and great orthogonality.

## i. Overview

For a finite group `G`, Mathlib states character orthogonality and the dimension formula
for intertwining maps with the normalisation `(Nat.card G)⁻¹ * ∑ g, χ g * ψ g⁻¹`. The
character inner product here uses the normalisation
`charInner χ ψ = (Nat.card G)⁻¹ * ∑ g, χ g * conj (ψ g)`; the bridge between the two is
`charInner_character_eq_sum_inv`, which uses the existing
`CharacterTheory.char_inv_eq_conj` (character at `g⁻¹` is the conjugate of the character
at `g`).

The unrestricted quantity `intertwiningRank σ ρ = finrank ℂ (IntertwiningMap σ ρ)` is the
dimension of the intertwining space for every `σ`. It is the multiplicity of `σ` in `ρ`
only when `σ` is irreducible: `irrepMultiplicity` therefore requires `IsIrreducible σ`, and
`irrepMultiplicity_of_isIrreducible` is proved from the existing Schur-dimension theorem
`CharacterTheory.finrank_intertwiningMap_eq_one_or_zero`.

The group average `(Nat.card G)⁻¹ • ∑ g, ρ g` is the projection onto the invariant
(totally symmetric) subspace. If the trivial representation does not occur (character inner
product with the trivial character equal to `0`), then the average and every `G`-invariant
linear form vanish; for a tensor product of factors this is the finite-group
vanishing-integral rule.

## ii. Key results

- `CharacterTheory.charInner_character_eq_sum_inv` : bridge to Mathlib's normalisation.
- `CharacterTheory.intertwiningRank`, `CharacterTheory.irrepMultiplicity` : intertwining
  rank (unrestricted) and irrep multiplicity (irreducible `σ` only).
- `CharacterTheory.intertwiningRank_eq_charInner`,
  `CharacterTheory.irrepMultiplicity_eq_charInner` : the reduction formula.
- `CharacterTheory.charInner_character_eq_ite` : irreducible characters are orthonormal.
- `CharacterTheory.irrepMultiplicity_of_isIrreducible` : Schur's lemma as a count.
- `CharacterTheory.sum_comp_comp_inv_eq_zero_of_not_nonempty_equiv` and
  `CharacterTheory.groupAverage_comp_comp_inv_eq_trace_smul` : great orthogonality.
- `CharacterTheory.isProj_groupAverage` : group averaging projects onto the invariants.
- `CharacterTheory.groupAverage_eq_zero_of_charInner_trivial_eq_zero`,
  `CharacterTheory.invariant_linearForm_eq_zero` and
  `CharacterTheory.groupAverage_tprod_tmul_eq_zero` : the vanishing-integral rule.

## iii. Table of contents

- A. Characters and the conjugation bridge
- B. Orthogonality relations and the reduction formula
- C. Group averaging and the vanishing-integral rule
- D. Great orthogonality

## iv. References

- J.-P. Serre, Linear Representations of Finite Groups, Graduate Texts in Mathematics 42,
  Springer (1977), Chapters 1 and 2.

-/
@[expose] public section

noncomputable section

namespace CharacterTheory

open Module Representation ComplexConjugate Matrix

/-!

## A. Characters and the conjugation bridge

-/

/-- The character inner product `⟨χ, ψ⟩ = |G|⁻¹ * ∑ g, χ g * conj (ψ g)` of complex class
functions on a finite group, with `|G| = Nat.card G`. -/
def charInner {G : Type*} [Fintype G] (χ ψ : G → ℂ) : ℂ :=
  (Nat.card G : ℂ)⁻¹ * ∑ g, χ g * conj (ψ g)

-- The inverse-character identity `χ g⁻¹ = conj (χ g)` is the existing
-- `CharacterTheory.char_inv_eq_conj` in
-- `MathlibExt/RepresentationTheory/CharacterInvEqConj.lean`; it is not re-proved here. The
-- bridge below uses it (as `char_inv_eq_conj`, since `conj` is notation for
-- `starRingEnd`).

/-- Bridge between `charInner` and Mathlib's normalisation `∑ g, χ g * ψ g⁻¹`. -/
lemma charInner_character_eq_sum_inv {G V W : Type*} [Group G] [Fintype G] [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) :
    charInner ρ.character σ.character =
      (Nat.card G : ℂ)⁻¹ * ∑ g, ρ.character g * σ.character g⁻¹ := by
  simp only [charInner, char_inv_eq_conj]

/-!

## B. Orthogonality relations and the reduction formula

-/

/-- The intertwining-space rank of `σ` in `ρ` (note the order: `σ` occurs in `ρ`),
defined as the natural number `finrank ℂ (IntertwiningMap σ ρ)`. This is defined for every
`σ`; it is the multiplicity of `σ` in `ρ` only when `σ` is irreducible
(`irrepMultiplicity`). In particular, for reducible `σ` a nonzero rank does not mean `σ`
occurs in `ρ`: over `Ci`, the reducible `σ = inversionAu.prod inversionAg` has a nonzero
intertwining space with `ρ = 3 · Au` although `σ` does not occur in `ρ`. -/
def intertwiningRank {G V W : Type*} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (σ : Representation ℂ G W) (ρ : Representation ℂ G V) : ℕ :=
  finrank ℂ (IntertwiningMap σ ρ)

/-- The multiplicity of an irreducible representation `σ` in `ρ` (note the order: `σ`
occurs in `ρ`). The `IsIrreducible σ` argument is what makes this a multiplicity rather
than an intertwining-space rank: callers must supply it, so a reducible `σ` cannot be
passed off as an irrep. For a finite group, finite-dimensional representations and
irreducible `σ`, this counts the copies of `σ` in a decomposition of `ρ` into irreducibles
(`irrepMultiplicity_of_isIrreducible`, `irrepMultiplicity_prod`, `irrepMultiplicity_congr`). -/
def irrepMultiplicity {G V W : Type*} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (σ : Representation ℂ G W) (ρ : Representation ℂ G V) [IsIrreducible σ] : ℕ :=
  intertwiningRank σ ρ

/-- **Reduction formula** for the intertwining-space rank: it is
`|G|⁻¹ * ∑ g, χ_ρ g * conj (χ_σ g)`. -/
theorem intertwiningRank_eq_charInner {G V W : Type*} [Group G] [Fintype G] [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ G W) (ρ : Representation ℂ G V) :
    (intertwiningRank σ ρ : ℂ) = charInner ρ.character σ.character := by
  have : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  rw [charInner_character_eq_sum_inv, card_inv_mul_sum_char_mul_char_eq_finrank σ ρ]
  rfl

/-- **Reduction formula**: the multiplicity of an irreducible `σ` in `ρ` is
`|G|⁻¹ * ∑ g, χ_ρ g * conj (χ_σ g)`. -/
theorem irrepMultiplicity_eq_charInner {G V W : Type*} [Group G] [Fintype G] [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ G W) (ρ : Representation ℂ G V) [IsIrreducible σ] :
    (irrepMultiplicity σ ρ : ℂ) = charInner ρ.character σ.character :=
  intertwiningRank_eq_charInner σ ρ

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
  change Module.finrank ℂ (σ.IntertwiningMap τ) = _
  have h := finrank_intertwiningMap_eq_one_or_zero σ τ
  have hiff : Nonempty (τ.Equiv σ) ↔ Nonempty (σ.Equiv τ) :=
    ⟨fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ => ⟨e.symm⟩⟩
  rw [h, hiff]

/-- Multiplicities only depend on the isomorphism class of the ambient representation. -/
lemma irrepMultiplicity_congr {G V V' W : Type*} [Group G] [Fintype G] [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (σ : Representation ℂ G W)
    [IsIrreducible σ]
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
    [IsIrreducible σ]
    (ρ₁ : Representation ℂ G V₁) (ρ₂ : Representation ℂ G V₂) :
    irrepMultiplicity σ (ρ₁.prod ρ₂) = irrepMultiplicity σ ρ₁ + irrepMultiplicity σ ρ₂ := by
  apply Nat.cast_injective (R := ℂ)
  push_cast
  simp only [irrepMultiplicity_eq_charInner, charInner, character_prod, add_mul,
    Finset.sum_add_distrib, mul_add]

/-- The intertwining rank is additive over direct sums in the first argument. Unlike
`irrepMultiplicity_prod`, this needs no irreducibility: it is the form used for the
reducible `σ = inversionAu.prod inversionAg` in the `Ci` counterexample below. -/
lemma intertwiningRank_prod_left {G V₁ V₂ W : Type*} [Group G] [Fintype G] [AddCommGroup V₁]
    [Module ℂ V₁] [FiniteDimensional ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    [FiniteDimensional ℂ V₂] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ₁ : Representation ℂ G V₁) (σ₂ : Representation ℂ G V₂) (ρ : Representation ℂ G W) :
    intertwiningRank (σ₁.prod σ₂) ρ = intertwiningRank σ₁ ρ + intertwiningRank σ₂ ρ := by
  apply Nat.cast_injective (R := ℂ)
  push_cast
  simp only [intertwiningRank_eq_charInner, charInner, character_prod, map_add,
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

/-- The trivial one-dimensional representation is irreducible. -/
instance trivial_isIrreducible {G : Type*} [Group G] : IsIrreducible (trivial ℂ G ℂ) :=
  isIrreducible_of_finrank_eq_one _ (finrank_self ℂ)

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


end CharacterTheory
