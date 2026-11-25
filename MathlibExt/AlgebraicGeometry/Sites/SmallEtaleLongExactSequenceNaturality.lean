/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module
public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleLongExactSequence

/-! # Functoriality of the canonical étale long exact sequence

Every component is the actual cohomology map of the same original sequence
morphism. The sequence functor supplies all squares and both functor laws.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory
universe u w
namespace AlgebraicGeometry.Scheme.DerivedSections

/-- The canonical sequence functor in each adjacent pair of degrees. -/
def smallEtaleLongSequenceFunctor (X : Scheme.{u}) (n : ℕ) :
    ShortExactSequence (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) ⥤
      ComposableArrows AddCommGrpCat.{max u w} 5 :=
  Sheaf.H.longSequenceFunctor n (n + 1) rfl

/-- The six components are the original sheaf-morphism cohomology maps. -/
def SmallEtaleLongSequenceComponents (X : Scheme.{u}) (n : ℕ)
    {S T : ShortExactSequence (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w})}
    (α : S ⟶ T) : Prop :=
  let m : smallEtaleLongSequence.{u, w} S.property n ⟶
      smallEtaleLongSequence.{u, w} T.property n :=
    (smallEtaleLongSequenceFunctor.{u, w} X n).map α
  m.app 0 = AddCommGrpCat.ofHom (Sheaf.H.map.{max u w, max u w, u, u + 1} α.hom.τ₁ n) ∧
  m.app 1 = AddCommGrpCat.ofHom (Sheaf.H.map.{max u w, max u w, u, u + 1} α.hom.τ₂ n) ∧
  m.app 2 = AddCommGrpCat.ofHom (Sheaf.H.map.{max u w, max u w, u, u + 1} α.hom.τ₃ n) ∧
  m.app 3 = AddCommGrpCat.ofHom (Sheaf.H.map.{max u w, max u w, u, u + 1} α.hom.τ₁ (n + 1)) ∧
  m.app 4 = AddCommGrpCat.ofHom (Sheaf.H.map.{max u w, max u w, u, u + 1} α.hom.τ₂ (n + 1)) ∧
  m.app 5 = AddCommGrpCat.ofHom (Sheaf.H.map.{max u w, max u w, u, u + 1} α.hom.τ₃ (n + 1))

/-- The stock sequence morphism has those same literal six components. -/
theorem smallEtaleLongSequenceFunctor_components (X : Scheme.{u}) (n : ℕ)
    {S T : ShortExactSequence (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w})}
    (α : S ⟶ T) : SmallEtaleLongSequenceComponents.{u, w} X n α :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Actual components, all commuting squares, and identity/composition laws. -/
theorem original_small_etale_long_exact_sequence_functoriality (X : Scheme.{u}) (n : ℕ) :
    let C := ShortExactSequence (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w})
    let F := smallEtaleLongSequenceFunctor.{u, w} X n
    (∀ S : C, F.obj S = smallEtaleLongSequence.{u, w} S.property n) ∧
    (∀ (S T : C) (α : S ⟶ T), SmallEtaleLongSequenceComponents.{u, w} X n α) ∧
    (∀ (S T : C) (α : S ⟶ T) (i j : Fin 6) (h : i ≤ j),
      (F.obj S).map (homOfLE h) ≫ (F.map α).app j =
        (F.map α).app i ≫ (F.obj T).map (homOfLE h)) ∧
    (∀ S : C, F.map (𝟙 S) = 𝟙 (F.obj S)) ∧
    ∀ (S T U : C) (α : S ⟶ T) (β : T ⟶ U), F.map (α ≫ β) = F.map α ≫ F.map β := by
  intro C F
  exact ⟨fun _ => rfl, fun _ _ α => smallEtaleLongSequenceFunctor_components.{u, w} X n α,
    fun _ _ α _ _ h => (F.map α).naturality (homOfLE h),
    F.map_id, fun _ _ _ α β => F.map_comp α β⟩

end AlgebraicGeometry.Scheme.DerivedSections
