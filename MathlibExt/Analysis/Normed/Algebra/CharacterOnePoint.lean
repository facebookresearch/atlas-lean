/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.Normed.Algebra.NonUnitalGelfand
public import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# Actual pointed compactification and nonunital character precomposition

The existing nonzero weak characters together with the actual zero functional
are the one-point compactification of the same original character space.
The distinguished point is zero, including the already-compact and zero-
algebra cases. Every continuous nonunital algebra homomorphism induces literal
precomposition on this compactification and preserves that distinguished point.

The actual homeomorphism is the existing compact-Hausdorff one-point factory
applied to the proved original inclusion and its exact range. No inverse,
character model, homeomorphism or desired map is a supplied certificate.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Topology
open scoped OnePoint

namespace WeakDual

universe uA uB

variable {A : Type uA} [NonUnitalNormedRing A] [NormedSpace ℂ A]

/-- **Character space with zero.** Let `A` be a nonunital normed ring with a complex normed vector-space
structure. Write `Δ(A)` for its nonzero continuous complex characters, in the topology of pointwise
convergence. This is the subspace `Δ(A) ∪ {0}` of the pointwise-topologized continuous dual of `A`. -/
abbrev characterSpaceWithZero (A : Type uA) [NonUnitalNormedRing A] [NormedSpace ℂ A] :=
  characterSpace ℂ A ∪ ({0} : Set (WeakDual ℂ A))

/-- **Zero character point.** Let `A` be a nonunital normed ring with a complex normed vector-space
structure. Write `Δ(A)` for its nonzero continuous complex characters, in the topology of pointwise
convergence. The distinguished point of `Δ(A) ∪ {0}` is the zero functional. -/
def zeroCharacter : characterSpaceWithZero A := ⟨0, Or.inr rfl⟩

/-- **Inclusion of nonzero characters.** Let `A` be a nonunital normed ring with a complex normed
vector-space structure. Write `Δ(A)` for its nonzero continuous complex characters, in the topology
of pointwise convergence. The inclusion `Δ(A) → Δ(A) ∪ {0}` sends each nonzero character to the same
continuous functional. -/
def characterWithZeroEmbedding (φ : characterSpace ℂ A) : characterSpaceWithZero A :=
  ⟨φ, Or.inl φ.property⟩

/-- **Topological embedding of the character space.** Let `A` be a nonunital normed ring with a complex
normed vector-space structure. Write `Δ(A)` for its nonzero continuous complex characters, in the
topology of pointwise convergence. The inclusion of `Δ(A)` into `Δ(A) ∪ {0}` is a topological
embedding for the pointwise topologies. -/
theorem characterWithZeroEmbedding_isEmbedding :
    IsEmbedding (characterWithZeroEmbedding (A := A)) :=
  (IsEmbedding.of_comp_iff
    (IsEmbedding.subtypeVal :
      IsEmbedding (Subtype.val : characterSpaceWithZero A → WeakDual ℂ A))).mp
    (show IsEmbedding ((Subtype.val : characterSpaceWithZero A → WeakDual ℂ A) ∘
        characterWithZeroEmbedding) from IsEmbedding.subtypeVal)

/-- **Range of the nonzero-character inclusion.** Let `A` be a nonunital normed ring with a complex
normed vector-space structure. Write `Δ(A)` for its nonzero continuous complex characters, in the
topology of pointwise convergence. The range of the inclusion is exactly the complement of the zero
functional in `Δ(A) ∪ {0}`. -/
theorem characterWithZeroEmbedding_range :
    Set.range (characterWithZeroEmbedding (A := A)) =
      ({zeroCharacter} : Set (characterSpaceWithZero A))ᶜ := by
  ext φ
  constructor
  · rintro ⟨ψ, rfl⟩
    intro hzero
    have hz : (ψ : WeakDual ℂ A) = 0 := congrArg Subtype.val hzero
    exact ψ.property.1 hz
  · intro hφ
    have hnonzero : (φ : WeakDual ℂ A) ≠ 0 := by
      intro hz
      exact hφ (Subtype.ext hz)
    have hcharacter : (φ : WeakDual ℂ A) ∈ characterSpace ℂ A := by
      rcases φ.property with hcharacter | hzero
      · exact hcharacter
      · exact (hnonzero (Set.mem_singleton_iff.mp hzero)).elim
    exact ⟨⟨φ, hcharacter⟩, Subtype.ext rfl⟩

section Compactification

variable [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [CompleteSpace A]

instance characterSpaceWithZero_compactSpace : CompactSpace (characterSpaceWithZero A) :=
  isCompact_iff_compactSpace.mp (CharacterSpace.union_zero_isCompact (A := A))

/-- **One-point compactification of the character space.** Let `A` be a nonunital complex Banach algebra
and let `Δ(A)` be its nonzero continuous character space with pointwise topology. The one-point
compactification of `Δ(A)` is homeomorphic to `Δ(A) ∪ {0}` in the pointwise-topologized continuous
dual. -/
def onePointCharacterSpaceHomeomorph :
    OnePoint (characterSpace ℂ A) ≃ₜ characterSpaceWithZero A :=
  OnePoint.equivOfIsEmbeddingOfRangeEq zeroCharacter characterWithZeroEmbedding
    characterWithZeroEmbedding_isEmbedding characterWithZeroEmbedding_range

/-- **Infinity corresponds to the zero character.** Let `A` be a nonunital complex Banach algebra and
let `Δ(A)` be its nonzero continuous character space with pointwise topology. The canonical
homeomorphism from the one-point compactification of `Δ(A)` to `Δ(A) ∪ {0}` sends infinity to the
zero functional. -/
@[simp]
theorem onePointCharacterSpaceHomeomorph_infty :
    onePointCharacterSpaceHomeomorph (A := A) ∞ = zeroCharacter := rfl

/-- **Finite points in the character compactification.** Let `A` be a nonunital complex Banach algebra
and let `Δ(A)` be its nonzero continuous character space with pointwise topology. The canonical
compactification homeomorphism sends each character `χ ∈ Δ(A)` to the same nonzero functional in
`Δ(A) ∪ {0}`. -/
@[simp]
theorem onePointCharacterSpaceHomeomorph_coe (φ : characterSpace ℂ A) :
    onePointCharacterSpaceHomeomorph φ = characterWithZeroEmbedding φ := rfl

/-- **Zero corresponds to infinity.** Let `A` be a nonunital complex Banach algebra and let `Δ(A)` be
its nonzero continuous character space with pointwise topology. The inverse canonical homeomorphism
from `Δ(A) ∪ {0}` to its one-point character compactification sends the zero functional to infinity. -/
@[simp]
theorem onePointCharacterSpaceHomeomorph_symm_zero :
    (onePointCharacterSpaceHomeomorph (A := A)).symm zeroCharacter = ∞ := by
  apply (onePointCharacterSpaceHomeomorph (A := A)).injective
  rw [Homeomorph.apply_symm_apply, onePointCharacterSpaceHomeomorph_infty]

end Compactification

section Precomposition

variable {B : Type uB} [NonUnitalNormedRing B] [NormedSpace ℂ B]

/-- **Continuous precomposition of characters with zero.** Let `A,B` be nonunital normed rings with
complex normed vector-space structures, and let `f : A → B` be a continuous nonunital complex
algebra homomorphism. Precomposition `χ ↦ χ ∘ f` defines a continuous map `Δ(B) ∪ {0} → Δ(A) ∪ {0}`
in pointwise topology, allowing a nonzero character to become zero. -/
def characterWithZeroPrecomposition (f : A →ₙₐ[ℂ] B) (hf : Continuous f) :
    C(characterSpaceWithZero B, characterSpaceWithZero A) := by
  let fL : A →L[ℂ] B := ContinuousLinearMap.mk (LinearMap.ofClass f) hf
  refine {
    toFun := fun φ => ⟨StrongDual.toWeakDual ((toStrongDual (φ : WeakDual ℂ B)).comp fL), ?_⟩
    continuous_toFun := ?_ }
  · have hφ : (φ : WeakDual ℂ B) ∈ characterSpace ℂ B ∪ {0} := φ.property
    rw [CharacterSpace.union_zero ℂ B] at hφ
    change _ ∈ characterSpace ℂ A ∪ {0}
    rw [CharacterSpace.union_zero ℂ A]
    intro x y
    change (φ : WeakDual ℂ B) (f (x * y)) =
      (φ : WeakDual ℂ B) (f x) * (φ : WeakDual ℂ B) (f y)
    rw [map_mul]
    exact hφ (f x) (f y)
  · apply Continuous.subtype_mk
    apply WeakDual.continuous_of_continuous_eval
    intro a
    change Continuous (fun φ : characterSpaceWithZero B => (φ : WeakDual ℂ B) (f a))
    exact (WeakDual.eval_continuous (f a)).comp continuous_subtype_val

/-- **Precomposition preserves the zero character.** Let `A,B` be nonunital normed rings with complex
normed vector-space structures, and let `f : A → B` be a continuous nonunital complex algebra
homomorphism. Precomposition sends the zero character of `B` to the zero character of `A`. -/
@[simp]
theorem characterWithZeroPrecomposition_zero (f : A →ₙₐ[ℂ] B) (hf : Continuous f) :
    characterWithZeroPrecomposition f hf zeroCharacter = zeroCharacter := by
  apply Subtype.ext
  apply DFunLike.ext
  intro a
  rfl

/-- **Evaluation of character precomposition.** Let `A,B` be nonunital normed rings with complex normed
vector-space structures, and let `f : A → B` be a continuous nonunital complex algebra homomorphism.
For `χ ∈ Δ(B) ∪ {0}` and `a ∈ A`, the precomposed functional has value `χ(f(a))`. -/
@[simp]
theorem characterWithZeroPrecomposition_apply (f : A →ₙₐ[ℂ] B) (hf : Continuous f)
    (φ : characterSpaceWithZero B) (a : A) :
    (characterWithZeroPrecomposition f hf φ : WeakDual ℂ A) a = (φ : WeakDual ℂ B) (f a) := rfl

end Precomposition

section OnePointPrecomposition

variable {B : Type uB} [NonUnitalNormedRing B] [NormedSpace ℂ B]
variable [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [CompleteSpace A]
variable [IsScalarTower ℂ B B] [SMulCommClass ℂ B B] [CompleteSpace B]

/-- **Precomposition on one-point character compactifications.** Let `A,B` be nonunital complex Banach
algebras and `f : A → B` a continuous nonunital complex algebra homomorphism. Precomposition defines
a continuous map from the one-point compactification of `Δ(B)` to that of `Δ(A)`, using infinity for
the zero character. -/
def onePointCharacterPrecomposition (f : A →ₙₐ[ℂ] B) (hf : Continuous f) :
    C(OnePoint (characterSpace ℂ B), OnePoint (characterSpace ℂ A)) where
  toFun p := (onePointCharacterSpaceHomeomorph (A := A)).symm
    (characterWithZeroPrecomposition f hf (onePointCharacterSpaceHomeomorph (A := B) p))
  continuous_toFun := (onePointCharacterSpaceHomeomorph (A := A)).symm.continuous.comp
    ((characterWithZeroPrecomposition f hf).continuous.comp
      (onePointCharacterSpaceHomeomorph (A := B)).continuous)

/-- **Character precomposition fixes infinity.** Let `A,B` be nonunital complex Banach algebras and `f :
A → B` a continuous nonunital complex algebra homomorphism. The map on one-point character
compactifications induced by `f` sends infinity to infinity. -/
@[simp]
theorem onePointCharacterPrecomposition_infty (f : A →ₙₐ[ℂ] B) (hf : Continuous f) :
    onePointCharacterPrecomposition f hf ∞ = ∞ := by
  change (onePointCharacterSpaceHomeomorph (A := A)).symm
    (characterWithZeroPrecomposition f hf (onePointCharacterSpaceHomeomorph (A := B) ∞)) = ∞
  rw [onePointCharacterSpaceHomeomorph_infty, characterWithZeroPrecomposition_zero,
    onePointCharacterSpaceHomeomorph_symm_zero]

end OnePointPrecomposition

end WeakDual

end
