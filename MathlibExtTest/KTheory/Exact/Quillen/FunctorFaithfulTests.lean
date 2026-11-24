/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.KTheory.Exact.Quillen.FunctorFaithful

/-!
# Original Quillen quotient equality through fully faithful exact functors

The source and target are arbitrary exact categories with independent object
and morphism universes. The actual mapped quotient equality reflects to an
original span isomorphism. The same certificate also consumes the original
strict Q-map composition law.
-/

public section
noncomputable section

open CategoryTheory Limits CategoryTheory.ExactCategory AlgebraicKTheory

universe uA vA uB vB uC vC

namespace QuillenFunctorFaithfulTests

variable {A : Type uA} [Category.{vA} A] [Preadditive A]
  [HasZeroObject A] [HasBinaryBiproducts A] [ExactCategory A]
  {B : Type uB} [Category.{vB} B] [Preadditive B]
  [HasZeroObject B] [HasBinaryBiproducts B] [ExactCategory B]
  {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
  (F : A ⥤ B) [F.Additive] [F.Full] [F.Faithful] [F.IsExact]

/-- Equality of the two actual mapped quotient spans yields a whole original
span isomorphism, without an abelian target or exactness-reflection premise. -/
theorem originalSpanIsoOfMappedQuotientEquality {X Y : A} (S T : QuillenSpan X Y)
    (h : QuillenQ.mkHom (X := (⟨F.obj X⟩ : QuillenQ B)) (Y := ⟨F.obj Y⟩)
        (QuillenSpan.map F S) =
      QuillenQ.mkHom (X := (⟨F.obj X⟩ : QuillenQ B)) (Y := ⟨F.obj Y⟩)
        (QuillenSpan.map F T)) :
    Nonempty (S ≅ T) := by
  let : (QuillenQ.map F).Faithful := QuillenQ.map_faithful F
  have hMapped :
      (QuillenQ.map F).map (QuillenQ.mkHom (X := (⟨X⟩ : QuillenQ A)) (Y := ⟨Y⟩) S) =
      (QuillenQ.map F).map (QuillenQ.mkHom (X := (⟨X⟩ : QuillenQ A)) (Y := ⟨Y⟩) T) := by
    rw [QuillenQ.map_mk, QuillenQ.map_mk]
    exact h
  exact QuillenQ.mkHom_eq_iff.mp ((QuillenQ.map F).map_injective hMapped)

/-- The original composite Q functor reflects arrows using the strict
composition law and the derived exact-functor certificate. -/
theorem compositeQuotientEquality (G : B ⥤ C)
    [G.Additive] [G.Full] [G.Faithful] [G.IsExact]
    {X Y : QuillenQ A} (f g : X ⟶ Y)
    (h : (QuillenQ.map F ⋙ QuillenQ.map G).map f =
      (QuillenQ.map F ⋙ QuillenQ.map G).map g) : f = g := by
  rw [← QuillenQ.map_comp F G] at h
  let : (QuillenQ.map (F ⋙ G)).Faithful := QuillenQ.map_faithful (F ⋙ G)
  exact (QuillenQ.map (F ⋙ G)).map_injective h

end QuillenFunctorFaithfulTests
