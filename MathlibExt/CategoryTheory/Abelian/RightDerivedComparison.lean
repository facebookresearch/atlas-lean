/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from AxiomMath/Stacks, revision
c496df0d9beea9deaeabcea8492605f9a0a2313b,
StacksFrontier/CategoryTheory/Abelian/RightDerivedPostcompose.lean.
The public source has no individual author or copyright notice.
Licensed under Apache 2.0. Modification notice: retain the complete
natural derived-functor comparisons as a standalone MathlibExt module;
no Stacks package or unresolved theorem is imported.
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# Postcomposing a right derived functor with an exact functor

Let `F : A ⥤ B` be an additive functor out of an abelian category with injective resolutions
and let `E : B ⥤ B'` be an additive functor which preserves homology (for instance an exact
functor).  This file constructs the natural isomorphism

`(F ⋙ E).rightDerived n ≅ F.rightDerived n ⋙ E`

of functors `A ⥤ B'`, together with the two intermediate comparisons it is built from.

The objectwise form of this statement is folklore and appears in the Stacks formalization as
`rightDerived_comp_iso_of_preservesHomology`; what is supplied here is the *natural* version,
which is what is needed whenever the comparison has to be transported along a cocone — for
instance when checking that a right derived functor commutes with a colimit.

## Main definitions

* `CategoryTheory.Functor.mapHomologicalComplexHomologyIso`: `E` commutes with the homology
  functors on homological complexes.
* `CategoryTheory.Functor.mapHomotopyCategoryHomologyIso`: the same on homotopy categories,
  obtained by lifting the previous isomorphism through the quotient functor.
* `CategoryTheory.Functor.rightDerivedCompIso`: the natural isomorphism
  `(F ⋙ E).rightDerived n ≅ F.rightDerived n ⋙ E`.
* `CategoryTheory.Functor.rightDerivedIsoOfNatIso`: a natural isomorphism of additive functors
  induces one of their right derived functors.
* `CategoryTheory.Functor.rightDerivedCompIsoOfPreservesLeftHomology`: the same comparison
  under the weaker hypothesis that `E` preserve the left homology of the degree-`n` short
  complexes of the chosen resolutions, which only holds on part of the source and is therefore
  stated after restricting along a functor `P` onto the objects where it does.

## Implementation notes

`HomotopyCategory.homologyFunctor` and `HomotopyCategory.homologyFunctorFactors` are
`irreducible` in Mathlib, so the homotopy-category comparison is assembled from
`HomotopyCategory.homologyFunctorFactors` and `Functor.mapHomotopyCategoryFactors` rather
than by unfolding; the lift through the quotient is `CategoryTheory.Quotient.natIsoLift`.

At the level of homological complexes no work is needed beyond `ShortComplex`: the functors
`E.mapHomologicalComplex c ⋙ HomologicalComplex.shortComplexFunctor B' c i` and
`HomologicalComplex.shortComplexFunctor B c i ⋙ E.mapShortComplex` are definitionally equal,
and `HomologicalComplex.homologyFunctorIso` is `Iso.refl`, so the whole comparison is
`ShortComplex.homologyFunctorIso` whiskered on the left.

`rightDerivedCompIsoOfPreservesLeftHomology` cannot be assembled that way: with homology
preserved only at the short complexes of the chosen resolutions there is no comparison of the
homology functors to whisker, so it is built component by component out of
`ShortComplex.mapHomologyIso`, with `ShortComplex.mapHomologyIso_inv_naturality` for the
naturality square. The two right derived functors are unfolded to the homology of the image of
the chosen resolution, which is where those components live.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {A : Type*} [Category* A] [Abelian A] [HasInjectiveResolutions A]
  {B : Type*} [Category* B] [Abelian B] {B' : Type*} [Category* B'] [Abelian B']

/-- A functor preserving homology commutes with the homology functors on homological
complexes: `E.mapHomologicalComplex c ⋙ homologyFunctor B' c i ≅ homologyFunctor B c i ⋙ E`.

Both sides are, definitionally, `HomologicalComplex.shortComplexFunctor` followed by a
comparison of short-complex homology, so this is `ShortComplex.homologyFunctorIso E`
whiskered on the left. -/
def mapHomologicalComplexHomologyIso (E : B ⥤ B') [E.Additive] [E.PreservesHomology]
    {ι : Type*} (c : ComplexShape ι) (i : ι) :
    E.mapHomologicalComplex c ⋙ HomologicalComplex.homologyFunctor B' c i ≅
      HomologicalComplex.homologyFunctor B c i ⋙ E :=
  Functor.isoWhiskerLeft (HomologicalComplex.shortComplexFunctor B c i)
    (ShortComplex.homologyFunctorIso E)

/-- A functor preserving homology commutes with the homology functors on homotopy
categories.  The isomorphism is lifted through the quotient functor from
`mapHomologicalComplexHomologyIso`. -/
def mapHomotopyCategoryHomologyIso (E : B ⥤ B') [E.Additive] [E.PreservesHomology]
    {ι : Type*} (c : ComplexShape ι) (i : ι) :
    E.mapHomotopyCategory c ⋙ HomotopyCategory.homologyFunctor B' c i ≅
      HomotopyCategory.homologyFunctor B c i ⋙ E :=
  Quotient.natIsoLift _
    (Functor.isoWhiskerRight (E.mapHomotopyCategoryFactors c)
        (HomotopyCategory.homologyFunctor B' c i) ≪≫
      Functor.isoWhiskerLeft (E.mapHomologicalComplex c)
        (HomotopyCategory.homologyFunctorFactors B' c i) ≪≫
      mapHomologicalComplexHomologyIso E c i ≪≫
      (Functor.isoWhiskerRight (HomotopyCategory.homologyFunctorFactors B c i) E).symm)

/-- **An exact functor may be pulled out of a right derived functor.**  If `E` is additive and
preserves homology then `(F ⋙ E).rightDerived n ≅ F.rightDerived n ⋙ E`, naturally in the
object of `A`.

Both right derived functors are the chosen injective resolution followed by a functor on
homotopy categories and then homology; the comparison is `Functor.mapHomotopyCategoryCompIso`
followed by `mapHomotopyCategoryHomologyIso`. -/
def rightDerivedCompIso (F : A ⥤ B) [F.Additive] (E : B ⥤ B') [E.Additive]
    [E.PreservesHomology] (n : ℕ) :
    (F ⋙ E).rightDerived n ≅ F.rightDerived n ⋙ E :=
  Functor.isoWhiskerLeft (injectiveResolutions A)
    (Functor.isoWhiskerRight (F.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ E)) _).symm
        (HomotopyCategory.homologyFunctor B' _ n) ≪≫
      Functor.isoWhiskerLeft (F.mapHomotopyCategory _) (mapHomotopyCategoryHomologyIso E _ n))

/-- A natural isomorphism of additive functors induces one of their right derived functors. -/
def rightDerivedIsoOfNatIso {F G : A ⥤ B} [F.Additive] [G.Additive] (e : F ≅ G) (n : ℕ) :
    F.rightDerived n ≅ G.rightDerived n where
  hom := NatTrans.rightDerived e.hom n
  inv := NatTrans.rightDerived e.inv n
  hom_inv_id := by rw [← NatTrans.rightDerived_comp, e.hom_inv_id, NatTrans.rightDerived_id]
  inv_hom_id := by rw [← NatTrans.rightDerived_comp, e.inv_hom_id, NatTrans.rightDerived_id]

/-- **An exact functor may be pulled out of a right derived functor wherever it is exact on
the resolution used.**  For `P : D ⥤ A` and additive `F : A ⥤ B`, `E : B ⥤ B'`, if `E`
preserves the left homology of the degree-`n` short complex of `F` applied to the chosen
injective resolution of `P.obj X` for every `X : D`, then
`P ⋙ F.rightDerived n ⋙ E ≅ P ⋙ (F ⋙ E).rightDerived n`.

This is the form of `rightDerivedCompIso` available when `E` is exact only on the objects
reached by `P`; the degree-`n` right derived functor of `F` at `P.obj X` is the degree-`n`
homology of `F` applied to that resolution, so preserving its left homology is all that the
comparison uses. -/
def rightDerivedCompIsoOfPreservesLeftHomology {D : Type*} [Category* D] (P : D ⥤ A)
    (F : A ⥤ B) [F.Additive] (E : B ⥤ B') [E.Additive] (n : ℕ)
    (hE : ∀ X : D, E.PreservesLeftHomologyOf
      (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution (P.obj X)).cocomplex).sc n)) :
    P ⋙ F.rightDerived n ⋙ E ≅ P ⋙ (F ⋙ E).rightDerived n := by
  refine NatIso.ofComponents (fun X ↦ ?_) ?_
  · have := hE X
    unfold Functor.rightDerived Functor.rightDerivedToHomotopyCategory
      HomotopyCategory.homologyFunctor
    exact ((((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (injectiveResolution (P.obj X)).cocomplex).sc n).mapHomologyIso E).symm
  · intro X Y φ
    obtain ⟨ψ, hψ⟩ := (HomotopyCategory.quotient A (ComplexShape.up ℕ)).map_surjective
      ((injectiveResolutions A).map (P.map φ))
    have := hE X
    have := hE Y
    unfold Functor.rightDerived Functor.rightDerivedToHomotopyCategory
    simp only [Functor.comp_map]
    rw [← hψ]
    unfold HomotopyCategory.homologyFunctor
    dsimp [Functor.comp_map, Functor.mapHomotopyCategory, HomologicalComplex.homologyFunctor]
    exact ShortComplex.mapHomologyIso_inv_naturality
      ((HomologicalComplex.shortComplexFunctor B (ComplexShape.up ℕ) n).map
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map ψ)) E

/-- The image of an injective resolution under an additive functor which preserves homology and
injective objects is an injective resolution of the image. -/
noncomputable def mapInjectiveResolution {A' B'' : Type*} [Category* A'] [Category* B'']
    [Abelian A'] [Abelian B''] (G : A' ⥤ B'') [G.Additive] [G.PreservesHomology]
    [G.PreservesInjectiveObjects] {F : A'} (R : InjectiveResolution F) :
    InjectiveResolution (G.obj F) where
  cocomplex := (G.mapHomologicalComplex (.up ℕ)).obj R.cocomplex
  injective n := G.injective_obj_of_injective (R.injective n)
  ι := (HomologicalComplex.singleMapHomologicalComplex G (.up ℕ) 0).inv.app F ≫
    (G.mapHomologicalComplex (.up ℕ)).map R.ι

/-- **Precomposing with an exact functor which preserves injective objects.** For additive
functors `G : A ⥤ B` and `H : B ⥤ C` with `G` preserving homology and injective objects, the
right derived functors of `G ⋙ H` are those of `H` evaluated on `G`: an injective resolution of
`F` is carried by `G` to an injective resolution of `G F`. -/
noncomputable def rightDerivedCompIsoOfPreservesInjectiveObjects
    {A' B'' C : Type*} [Category* A'] [Category* B''] [Category* C]
    [Abelian A'] [Abelian B''] [Abelian C]
    [HasInjectiveResolutions A'] [HasInjectiveResolutions B'']
    (G : A' ⥤ B'') (H : B'' ⥤ C) [G.Additive] [H.Additive]
    [G.PreservesHomology] [G.PreservesInjectiveObjects] (F : A') (q : ℕ) :
    ((G ⋙ H).rightDerived q).obj F ≅ (H.rightDerived q).obj (G.obj F) := by
  let R := injectiveResolution F
  exact R.isoRightDerivedObj (G ⋙ H) q ≪≫
    (HomologicalComplex.homologyFunctor C (.up ℕ) q).mapIso
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ H)) (.up ℕ)).app R.cocomplex) ≪≫
    ((mapInjectiveResolution G R).isoRightDerivedObj H q).symm

end CategoryTheory.Functor

end
