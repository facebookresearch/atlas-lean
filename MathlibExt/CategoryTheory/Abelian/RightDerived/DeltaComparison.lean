/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Authors: @toskua, Avocado

module

public import MathlibExt.CategoryTheory.Abelian.RightDerived.DeltaPrecomposition
public import MathlibExt.CategoryTheory.Abelian.DeltaFunctor.Transport

/-!
# Isomorphisms of cohomological delta-functors

Natural isomorphisms in each degree that commute with the connecting
maps define an isomorphism of cohomological delta-functors between
preadditive categories. In abelian categories, the right-derived
precomposition comparison for an exact injective-preserving source
change gives such an isomorphism.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false


section
universe uA vA uD vD
namespace CategoryTheory.CohomologicalDeltaFunctor
variable {A : Type uA} [Category.{vA} A] [Preadditive A]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]

theorem isoInvSquare {C : Type*} [Category C] {X Y X' Y' : C}
    (e : X ≅ Y) (f : X' ≅ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (h : a ≫ f.hom = e.hom ≫ b) : b ≫ f.inv = e.inv ≫ a := by
  apply (cancel_mono f.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- Let `A,D` be preadditive categories and `S,T` cohomological
delta-functors from `A` to `D`. Natural degree isomorphisms
`e_n : S^n ≅ T^n` satisfying `δ_S,n ≫ e_(n+1),X₁ = e_n,X₃ ≫ δ_T,n`
for every short exact sequence define an isomorphism `S ≅ T`. -/
def isoOfComponents (S T : CohomologicalDeltaFunctor A D)
    (e : ∀ n, S.T n ≅ T.T n)
    (h : ∀ n (Z : ShortComplex.ShortExactSequences A),
      (S.connecting n).app Z ≫ (e (n + 1)).hom.app Z.obj.X₁ =
        (e n).hom.app Z.obj.X₃ ≫ (T.connecting n).app Z) : S ≅ T where
  hom := homMk A D (fun n => (e n).hom) h
  inv := homMk A D (fun n => (e n).inv) (fun n Z =>
    isoInvSquare ((e n).app Z.obj.X₃) ((e (n + 1)).app Z.obj.X₁)
      ((S.connecting n).app Z) ((T.connecting n).app Z) (h n Z))
  hom_inv_id := by
    apply hom_ext
    intro n
    change (e n).hom ≫ (e n).inv = 𝟙 _
    exact (e n).hom_inv_id
  inv_hom_id := by
    apply hom_ext
    intro n
    change (e n).inv ≫ (e n).hom = 𝟙 _
    exact (e n).inv_hom_id

@[simp] theorem isoOfComponents_hom_app (S T : CohomologicalDeltaFunctor A D)
    (e : ∀ n, S.T n ≅ T.T n)
    (h : ∀ n (Z : ShortComplex.ShortExactSequences A),
      (S.connecting n).app Z ≫ (e (n + 1)).hom.app Z.obj.X₁ =
        (e n).hom.app Z.obj.X₃ ≫ (T.connecting n).app Z) (n : ℕ) :
    Hom.app (isoOfComponents S T e h).hom n = (e n).hom := rfl

end CategoryTheory.CohomologicalDeltaFunctor
end

section

universe u w
open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Functor.RightDerived

universe uC vC uM vM uA vA
variable {C : Type uC} [Category.{vC} C] [Abelian C] [HasInjectiveResolutions C]
variable {M : Type uM} [Category.{vM} M] [Abelian M] [HasInjectiveResolutions M]
variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable (E : C ⥤ M) [E.Additive] [E.PreservesInjectiveObjects] [E.PreservesHomology]
variable [PreservesFiniteLimits E] [PreservesFiniteColimits E]
variable (B : M ⥤ A) [B.Additive] [PreservesFiniteLimits B]

/-- Let `C,M,A` be abelian, with injective resolutions in `C,M`,
`E : C → M` additive and preserving injectives, homology, finite limits,
and finite colimits, and `B : M → A` additive and preserving finite
limits. For additive `P : C → A` and `α : P ≅ E ⋙ B`, the
right-derived comparison gives an isomorphism from the delta-functor
of `P` to that of `B` precomposed with `E`. -/
def precompDeltaIsoOfIso {P : C ⥤ A} [P.Additive]
    (α : P ≅ E ⋙ B) : Functor.rightDerivedDeltaFunctor P ≅
      CohomologicalDeltaFunctor.precompose E (precompShortExact E)
        (Functor.rightDerivedDeltaFunctor B) :=
  CohomologicalDeltaFunctor.isoOfComponents _ _
    (fun n => Functor.rightDerivedPrecompIsoOfIso E B α n)
    (fun n S => DeltaFunctor.System.comm (precompDeltaHomOfIso E B α).hom n S)

omit [PreservesFiniteLimits B] in
theorem precompDeltaIsoOfIso_hom_app {P : C ⥤ A} [P.Additive]
    (α : P ≅ E ⋙ B) (n : ℕ) :
    CohomologicalDeltaFunctor.Hom.app (precompDeltaIsoOfIso E B α).hom n =
      (Functor.rightDerivedPrecompIsoOfIso E B α n).hom := rfl

end CategoryTheory.Functor.RightDerived

end
