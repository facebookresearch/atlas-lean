/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.EtaleSpacePresentations

/-! # Tests for étale equivalence relations and their quotient sheaves

The API checks cover typeclass inference for the atlas, the projections of the comparison map
`R ⟶ U ×_{U/R} U` and both directions of the universal property. The trivial relation on a scheme
`U` (with `R = U` and `s = t = 𝟙 U`) is an étale equivalence relation, and its quotient is the
represented sheaf of `U`: the atlas map is an isomorphism, with inverse given by descent. The
kernel pair of an étale morphism gives an étale equivalence relation through the bridge with
internal equivalence relations.
-/

@[expose] public noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.EtaleSpacePresentations

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.EtaleSpacePresentations

universe u

section API

variable (P : EtaleEquivalencePresentation.{u}) (F : FppfSheaf.{u})

example : Epi (atlas P) := inferInstance

example : relationComparison P ≫ pullback.fst (atlas P) (atlas P) = represented.map P.source := by
  simp

example : relationComparison P ≫ pullback.snd (atlas P) (atlas P) = represented.map P.target := by
  simp

example (g : quotientSheaf P ⟶ F) : (descentHomEquiv P F g).1 = atlas P ≫ g := rfl

example (g : quotientSheaf P ⟶ F) : (descentHomEquiv P F).symm (descentHomEquiv P F g) = g :=
  (descentHomEquiv P F).symm_apply_apply g

example (a : MapDescentData P F) : descentHomEquiv P F ((descentHomEquiv P F).symm a) = a :=
  (descentHomEquiv P F).apply_symm_apply a

example (a : MapDescentData P F) : atlas P ≫ descend P a = a.1 := by simp

example (a : MapDescentData P F) (g : quotientSheaf P ⟶ F) (hg : atlas P ≫ g = a.1) :
    g = descend P a :=
  descend_unique P a g hg

example (V : Scheme.{u}) (a : P.U ⟶ V) (ha : P.source ≫ a = P.target ≫ a) :
    atlas P ≫ descendSchemeMap P V a ha = represented.map a := by
  simp

end API

/-- The trivial étale equivalence relation on a scheme: `R = U` and `s = t = 𝟙 U`. -/
def trivialPresentation (U : Scheme.{u}) : EtaleEquivalencePresentation.{u} where
  U := U
  R := U
  source := 𝟙 U
  target := 𝟙 U
  source_etale := inferInstance
  target_etale := inferInstance
  relation_mono := ⟨fun g h hgh => by simpa using congrArg (· ≫ prod.fst) hgh⟩
  equivalence _ :=
    { refl := fun x => ⟨x, Category.comp_id x, Category.comp_id x⟩
      symm := fun ⟨a, h₁, h₂⟩ => ⟨a, h₂, h₁⟩
      trans := fun ⟨a, h₁, h₂⟩ ⟨b, h₃, h₄⟩ =>
        ⟨a, h₁, by rw [Category.comp_id] at h₂ h₃ h₄ ⊢; rw [h₂, ← h₃, h₄]⟩ }

/-- The map `U/R ⟶ U` descended from the identity of `U`, for the trivial relation. -/
def trivialRetraction (U : Scheme.{u}) :
    quotientSheaf (trivialPresentation U) ⟶ represented.obj (trivialPresentation U).U :=
  descendSchemeMap (trivialPresentation U) (trivialPresentation U).U (𝟙 _) rfl

theorem atlas_trivialRetraction (U : Scheme.{u}) :
    atlas (trivialPresentation U) ≫ trivialRetraction U = 𝟙 _ :=
  (atlas_descendSchemeMap _ _ _ _).trans (represented.map_id _)

/-- For the trivial relation, the atlas `U ⟶ U/R` is an isomorphism of fppf sheaves. -/
example (U : Scheme.{u}) : IsIso (atlas (trivialPresentation U)) := by
  refine ⟨⟨trivialRetraction U, atlas_trivialRetraction U, ?_⟩⟩
  apply (cancel_epi (atlas (trivialPresentation U))).mp
  rw [← Category.assoc, atlas_trivialRetraction, Category.id_comp, Category.comp_id]

/-- The trivial relation is an internal equivalence relation of schemes. -/
example (U : Scheme.{u}) : IsEquivalenceRelation (𝟙 U) (𝟙 U) :=
  (trivialPresentation U).isEquivalenceRelation

/-- The kernel pair of an étale morphism is an étale equivalence relation. -/
example {U V : Scheme.{u}} (f : U ⟶ V) [Etale f] : EtaleEquivalencePresentation.{u} :=
  have : IsEquivalenceRelation (pullback.fst f f) (pullback.snd f f) :=
    (IsKernelPair.equivalenceRelation f _ _ (pullbackIsPullback _ _)
      (IsPullback.of_hasPullback f f)).isEquivalenceRelation
  EtaleEquivalencePresentation.ofIsEquivalenceRelation (pullback.fst f f) (pullback.snd f f)

end MathlibExtTest.AlgebraicGeometry.EtaleSpacePresentations
