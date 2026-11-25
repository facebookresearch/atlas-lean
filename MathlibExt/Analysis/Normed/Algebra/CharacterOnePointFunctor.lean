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

public import MathlibExt.Analysis.Normed.Algebra.CharacterOnePoint
public import MathlibExt.Topology.Compactification.OnePoint.PartialProperMap

/-!
# Literal pointed character-map laws needed by the original nonunital category

The actual nonunital precomposition maps preserve identity and reverse
composition. Their one-point maps have the original finite/zero values and
the exact actual distinguished point. These strict laws construct the
source's contravariant pointed-character functor; no inverse functor or
Gelfand/category equivalence theorem is used as DATA.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Topology
open scoped OnePoint

namespace WeakDual

universe uA uB uC

variable {A : Type uA} {B : Type uB} {C : Type uC}
variable [NonUnitalNormedRing A] [NormedSpace ℂ A]
variable [NonUnitalNormedRing B] [NormedSpace ℂ B]
variable [NonUnitalNormedRing C] [NormedSpace ℂ C]

/-- **Identity precomposition on characters with zero.** For a nonunital normed ring `A` with a complex
normed vector-space structure, precomposition with its identity algebra homomorphism is the identity
continuous map of `Δ(A) ∪ {0}` in pointwise topology. -/
theorem characterWithZeroPrecomposition_id :
    characterWithZeroPrecomposition (NonUnitalAlgHom.id ℂ A) continuous_id =
      ContinuousMap.id (characterSpaceWithZero A) := by
  ext φ
  apply DFunLike.ext
  intro a
  rfl

/-- **Character precomposition reverses composition.** For nonunital normed rings `A,B,C` with complex
normed vector-space structures and continuous nonunital complex algebra homomorphisms `f : A → B`,
`g : B → C`, precomposition with `g ∘ f` on characters with zero equals precomposition with `g`
followed by precomposition with `f`. -/
theorem characterWithZeroPrecomposition_comp
    (f : A →ₙₐ[ℂ] B) (g : B →ₙₐ[ℂ] C) (hf : Continuous f) (hg : Continuous g) :
    characterWithZeroPrecomposition (g.comp f) (hg.comp hf) =
      (characterWithZeroPrecomposition f hf).comp (characterWithZeroPrecomposition g hg) := by
  ext φ
  apply DFunLike.ext
  intro a
  rfl

section OnePoint

variable [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [CompleteSpace A]
variable [IsScalarTower ℂ B B] [SMulCommClass ℂ B B] [CompleteSpace B]
variable [IsScalarTower ℂ C C] [SMulCommClass ℂ C C] [CompleteSpace C]

/-- **Pointed map of character compactifications.** A continuous nonunital complex algebra homomorphism
`f : A → B` between nonunital complex Banach algebras induces a continuous map from the one-point
character compactification of `B` to that of `A` which fixes infinity. -/
def pointedCharacterMap (f : A →ₙₐ[ℂ] B) (hf : Continuous f) :
    PointedOnePointMap (characterSpace ℂ B) (characterSpace ℂ A) :=
  ⟨onePointCharacterPrecomposition f hf, onePointCharacterPrecomposition_infty f hf⟩

/-- **Identity map of a character compactification.** For a nonunital complex Banach algebra `A`,
precomposition with the identity homomorphism is the identity continuous map of the one-point
compactification of its nonzero character space. -/
theorem onePointCharacterPrecomposition_id :
    onePointCharacterPrecomposition (NonUnitalAlgHom.id ℂ A) continuous_id =
      ContinuousMap.id (OnePoint (characterSpace ℂ A)) := by
  apply ContinuousMap.ext
  intro p
  change (onePointCharacterSpaceHomeomorph (A := A)).symm
    (characterWithZeroPrecomposition (NonUnitalAlgHom.id ℂ A) continuous_id
      (onePointCharacterSpaceHomeomorph p)) = p
  rw [characterWithZeroPrecomposition_id]
  exact (onePointCharacterSpaceHomeomorph (A := A)).symm_apply_apply p

/-- **Composition on one-point character compactifications.** For nonunital complex Banach algebras
`A,B,C` and continuous nonunital complex algebra homomorphisms `f : A → B`, `g : B → C`, the
compactified character map of `g ∘ f` is the character map of `g` followed by that of `f`. -/
theorem onePointCharacterPrecomposition_comp
    (f : A →ₙₐ[ℂ] B) (g : B →ₙₐ[ℂ] C) (hf : Continuous f) (hg : Continuous g) :
    onePointCharacterPrecomposition (g.comp f) (hg.comp hf) =
      (onePointCharacterPrecomposition f hf).comp (onePointCharacterPrecomposition g hg) := by
  apply ContinuousMap.ext
  intro p
  apply (onePointCharacterSpaceHomeomorph (A := A)).injective
  change onePointCharacterSpaceHomeomorph
    ((onePointCharacterSpaceHomeomorph (A := A)).symm
      (characterWithZeroPrecomposition (g.comp f) (hg.comp hf)
        (onePointCharacterSpaceHomeomorph p))) =
    onePointCharacterSpaceHomeomorph
      ((onePointCharacterSpaceHomeomorph (A := A)).symm
        (characterWithZeroPrecomposition f hf
          (onePointCharacterSpaceHomeomorph
            ((onePointCharacterSpaceHomeomorph (A := B)).symm
              (characterWithZeroPrecomposition g hg (onePointCharacterSpaceHomeomorph p))))))
  simp only [Homeomorph.apply_symm_apply]
  apply Subtype.ext
  apply DFunLike.ext
  intro a
  rfl

end OnePoint

end WeakDual

end
