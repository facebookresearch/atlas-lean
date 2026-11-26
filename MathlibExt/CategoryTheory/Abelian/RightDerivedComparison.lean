/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`StacksFrontier/CategoryTheory/Abelian/RightDerivedPostcompose.lean`
(AxiomMath/Stacks, https://github.com/AxiomMath/Stacks, revision
c496df0d9beea9deaeabcea8492605f9a0a2313b):
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The source files carry no per-file copyright notice or author list.
Modified: the natural derived-functor comparisons are kept as a standalone module;
no Stacks package is imported.
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import MathlibExt.Algebra.Homology.HomologicalComplex.MapHomologyIso
public import MathlibExt.CategoryTheory.Abelian.Injective.MapResolution
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/- The homotopy-category comparison is lifted through the quotient using homologyFunctorFactors, mapHomotopyCategoryFactors, and Quotient.natIsoLift. The partial left-homology comparison is assembled from ShortComplex.mapHomologyIso and its inverse naturality law rather than a global homology-functor isomorphism. -/

/-!
# Homology-preserving postcomposition of right-derived functors

Let `A,B,B′` be abelian, with injective resolutions in `A`, and
`F : A → B` additive. For additive homology-preserving `E : B → B′`,
there is a natural isomorphism `R^n(F ⋙ E) ≅ R^nF ⋙ E`.
Homology preservation also gives a comparison on homotopy categories.
A natural isomorphism of additive functors induces one of their
derived families.

For a functor `P : D → A`, it suffices to preserve left homology
only at the degree-`n` short complexes of `F` applied to the chosen
injective resolutions of `P(X)`: this gives
`P ⋙ R^nF ⋙ E ≅ P ⋙ R^n(F ⋙ E)` on `D`.
An additive homology- and injective-preserving source functor gives
the complementary precomposition comparison on derived objects.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {A : Type*} [Category* A] [Abelian A] [HasInjectiveResolutions A]
  {B : Type*} [Category* B] [Abelian B] {B' : Type*} [Category* B'] [Abelian B']

/-- Let `B,B′` be abelian and `E : B → B′` additive and preserving
homology. For any complex shape `c` and index `i`, mapping by `E`
then taking homology on the homotopy category is naturally isomorphic
to taking homology first then applying `E`. -/
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

/-- Let `A,B,B′` be abelian, with injective resolutions in `A`,
`F : A → B` additive, and `E : B → B′` additive and preserving
homology. There is a natural isomorphism
`R^n(F ⋙ E) ≅ R^nF ⋙ E` in every degree `n`. -/
def rightDerivedCompIso (F : A ⥤ B) [F.Additive] (E : B ⥤ B') [E.Additive]
    [E.PreservesHomology] (n : ℕ) :
    (F ⋙ E).rightDerived n ≅ F.rightDerived n ⋙ E :=
  Functor.isoWhiskerLeft (injectiveResolutions A)
    (Functor.isoWhiskerRight (F.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ E)) _).symm
        (HomotopyCategory.homologyFunctor B' _ n) ≪≫
      Functor.isoWhiskerLeft (F.mapHomotopyCategory _) (mapHomotopyCategoryHomologyIso E _ n))

/-- Let `A,B` be abelian, with injective resolutions in `A`, and
`F,G : A → B` additive. A natural isomorphism `e : F ≅ G` induces
a natural isomorphism `R^nF ≅ R^nG` in every degree `n`. -/
def rightDerivedIsoOfNatIso {F G : A ⥤ B} [F.Additive] [G.Additive] (e : F ≅ G) (n : ℕ) :
    F.rightDerived n ≅ G.rightDerived n where
  hom := NatTrans.rightDerived e.hom n
  inv := NatTrans.rightDerived e.inv n
  hom_inv_id := by rw [← NatTrans.rightDerived_comp, e.hom_inv_id, NatTrans.rightDerived_id]
  inv_hom_id := by rw [← NatTrans.rightDerived_comp, e.inv_hom_id, NatTrans.rightDerived_id]

/-- Let `A,B,B′` be abelian, with injective resolutions in `A`,
`D` a category, `P : D → A`, and `F : A → B`, `E : B → B′` additive.
If `E` preserves left homology of each degree-`n` short complex in
`F(I(P(X)))`, where `I(P(X))` is the chosen injective resolution,
then `P ⋙ R^nF ⋙ E ≅ P ⋙ R^n(F ⋙ E)` naturally on `D`. -/
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

/-- Let `A′,B″,C` be abelian, with injective resolutions in `A′,B″`,
`G : A′ → B″`, `H : B″ → C` additive, and `G` preserving homology
and injective objects. For `X : A′`, mapping an injective resolution
by `G` gives the comparison
`R^q(G ⋙ H)(X) ≅ R^qH(G(X))`. -/
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
