/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module
public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleLongExactSequence

/-!
# Functoriality of small étale cohomology windows

A morphism of short exact common-universe sheaf sequences acts on the cohomology windows by
its three component cohomology maps in degree `n` and again in degree `n + 1`. These maps
commute with every arrow of the window, including its connecting map, and preserve identity
and composition.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory
universe u w
namespace AlgebraicGeometry.Scheme.DerivedSections

/-- Cohomology window functor of short exact sheaf sequences.

For fixed natural degree `n`, the small étale six-term cohomology windows define a functor on
short exact sheaf sequences. -/
def smallEtaleLongSequenceFunctor (X : Scheme.{u}) (n : ℕ) :
    ShortExactSequence (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) ⥤
      ComposableArrows AddCommGrpCat.{max u w} 5 :=
  Sheaf.H.longSequenceFunctor n (n + 1) rfl

/-- Six cohomology component formulas for a window morphism.

The six components of a sequence morphism are the cohomology maps of its first, second, and
third sheaf components in degree `n`, followed by the same three maps in degree `n + 1`. -/
def SmallEtaleLongSequenceComponents (X : Scheme.{u}) (n : ℕ)
    {S T : ShortExactSequence (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w})}
    (α : S ⟶ T) : Prop :=
  let C := Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}
  let A := AddCommGrpCat.{max u w}
  let _ : HasExt.{max u w} C := smallEtaleHasExt.{u, w} X
  let H₀ : C ⥤ A := Sheaf.functorH.{max u w, max u w, u, u + 1} X.smallEtaleTopology n
  let H₁ : C ⥤ A := Sheaf.functorH.{max u w, max u w, u, u + 1} X.smallEtaleTopology (n + 1)
  let m : smallEtaleLongSequence.{u, w} S.property n ⟶
      smallEtaleLongSequence.{u, w} T.property n :=
    (smallEtaleLongSequenceFunctor.{u, w} X n).map α
  m.app 0 = H₀.map α.hom.τ₁ ∧
  m.app 1 = H₀.map α.hom.τ₂ ∧
  m.app 2 = H₀.map α.hom.τ₃ ∧
  m.app 3 = H₁.map α.hom.τ₁ ∧
  m.app 4 = H₁.map α.hom.τ₂ ∧
  m.app 5 = H₁.map α.hom.τ₃

/-- Cohomology window functor has the displayed component maps.

Every morphism image under the window functor satisfies its six cohomology component formulas. -/
theorem smallEtaleLongSequenceFunctor_components (X : Scheme.{u}) (n : ℕ)
    {S T : ShortExactSequence (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w})}
    (α : S ⟶ T) : SmallEtaleLongSequenceComponents.{u, w} X n α :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Cohomology window maps satisfy naturality and functor laws.

The window functor has the given object and component formulas, commutes with every window
arrow, and preserves identity sequence maps and composition. -/
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
