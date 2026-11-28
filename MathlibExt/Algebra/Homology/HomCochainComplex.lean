/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

public import MathlibExt.Algebra.Homology.HomologyMapSquare

/-!
# Contravariant Hom cochains of natural-index chain complexes

In a preadditive category `C`, the Hom cochain complex of a chain complex `K` and a
coefficient object `G` has degree-`n` group `Hom_C(K_n,G)`, with differential given by
precomposition with `K.d (n+1) n`. It is contravariant in `K`, covariant in `G`, and additive.
The coefficient functor also gives its cohomology groups as functors of `G`.

Chain homotopies and homotopy equivalences induce the corresponding Hom cochain homotopies and
cohomology isomorphisms, with the chain direction reversed. An additive fully faithful functor
identifies these Hom cochains by applying its morphism map in every degree. The object and
morphism universes are independent; the two compared categories share their object level and
share their morphism level, so the comparison lands in the same additive-group category.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace HomologicalComplex

variable (C : Type u) [Category.{v} C] [Preadditive C]

/-- Contravariant Hom cochain functor with a fixed coefficient.

For `G : C`, take a natural-index chain complex `K` to the cochain complex with degree-`n`
additive group `K.X n ⟶ G`. A chain map acts by precomposition, reversing its direction. -/
noncomputable def homCochainComplexFunctor (G : C) :
    (ChainComplex C ℕ)ᵒᵖ ⥤ CochainComplex AddCommGrpCat.{v} ℕ :=
  HomologicalComplex.opFunctor C (ComplexShape.down ℕ) ⋙
    (preadditiveYoneda.obj G).mapHomologicalComplex (ComplexShape.up ℕ)

/-- Fixed-coefficient Hom cochain functor is additive.

The contravariant Hom cochain functor preserves addition of chain maps. -/
noncomputable instance homCochainComplexFunctor_additive (G : C) :
    (homCochainComplexFunctor (C := C) G).Additive := by
  change (HomologicalComplex.opFunctor C (ComplexShape.down ℕ) ⋙
    (preadditiveYoneda.obj G).mapHomologicalComplex ((ComplexShape.down ℕ).symm)).Additive
  infer_instance

/-- Contravariant Hom cochains preserve limits in the opposite chain category.

For a category `J : Type v` with morphisms in universe `v`, assume `Cᵒᵖ` has limits of shape
`J`. Then the fixed-coefficient Hom cochain functor preserves limits of that shape from
`(ChainComplex C ℕ)ᵒᵖ`. -/
noncomputable instance homCochainComplexFunctor_preservesLimitsOfShape
    {J : Type v} [Category.{v} J] [HasLimitsOfShape J Cᵒᵖ] (G : C) :
    PreservesLimitsOfShape J (homCochainComplexFunctor C G) := by
  have hOp : PreservesLimitsOfShape J (HomologicalComplex.opFunctor C (ComplexShape.down ℕ)) :=
    inferInstance
  have hMap : PreservesLimitsOfShape J
      ((preadditiveYoneda.obj G).mapHomologicalComplex (ComplexShape.up ℕ)) :=
    inferInstance
  exact @CategoryTheory.Limits.comp_preservesLimitsOfShape _ _ _ _ _ _ _ _
    (HomologicalComplex.opFunctor C (ComplexShape.down ℕ))
    ((preadditiveYoneda.obj G).mapHomologicalComplex (ComplexShape.up ℕ))
    hOp hMap

/-- Hom cochain bifunctor with covariant coefficients.

The assignment `G ↦ homCochainComplexFunctor C G` is a functor in the coefficient object. Its
two-variable Hom construction is covariant in `G` and contravariant in the chain complex. -/
noncomputable def homCochainComplexBifunctor :
    C ⥤ ((ChainComplex C ℕ)ᵒᵖ ⥤ CochainComplex AddCommGrpCat.{v} ℕ) where
  obj G := homCochainComplexFunctor C G
  map f := Functor.whiskerLeft
    (HomologicalComplex.opFunctor C (ComplexShape.down ℕ))
    (NatTrans.mapHomologicalComplex
      (preadditiveYoneda.map f) (ComplexShape.up ℕ))

/-- Degree object of the fixed-coefficient Hom cochain complex.

In degree `n`, the Hom cochain complex of `K` and `G` has additive group `K.X n ⟶ G`. -/
@[simp]
lemma homCochainComplexFunctor_obj_X (G : C)
    (K : ChainComplex C ℕ) (n : ℕ) :
    ((homCochainComplexFunctor C G).obj (Opposite.op K)).X n =
      AddCommGrpCat.of (K.X n ⟶ G) := rfl

/-- Hom cochain cohomology as a coefficient functor.

For a chain complex `K` and natural degree `n`, take the degree-`n` cohomology of its Hom
cochain complex to define a functor `C ⥤ AddCommGrpCat` in the coefficient object. -/
noncomputable def homCochainComplexHomologyFunctor (K : ChainComplex C ℕ) (n : ℕ) :
    C ⥤ AddCommGrpCat.{v} :=
  homCochainComplexBifunctor C ⋙
    (evaluation _ _).obj (Opposite.op K) ⋙
    homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) n

end HomologicalComplex

namespace Homotopy

open HomologicalComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {K L : ChainComplex C ℕ} {f g : K ⟶ L}

/-- Chain homotopy induces a contravariant Hom cochain homotopy.

A homotopy between chain maps `f, g : K ⟶ L` induces a homotopy between their Hom cochain maps
from `Hom(L,G)` to `Hom(K,G)`. -/
noncomputable def mapHomCochainComplex (h : Homotopy f g) (G : C) :
    Homotopy
      ((HomologicalComplex.homCochainComplexFunctor C G).map f.op)
      ((HomologicalComplex.homCochainComplexFunctor C G).map g.op) :=
  (preadditiveYoneda.obj G).mapHomotopy h.op

/-- Homotopic chain maps induce equal Hom cohomology maps.

If `f` and `g` are homotopic and the two Hom cochain complexes have homology in degree `n`,
then their contravariant Hom maps induce the same degree-`n` cohomology map. -/
lemma homCochainComplex_homologyMap_eq (h : Homotopy f g) (G : C) (n : ℕ)
    [((HomologicalComplex.homCochainComplexFunctor C G).obj
      (Opposite.op L)).HasHomology n]
    [((HomologicalComplex.homCochainComplexFunctor C G).obj
      (Opposite.op K)).HasHomology n] :
    homologyMap
        ((HomologicalComplex.homCochainComplexFunctor C G).map f.op) n =
      homologyMap
        ((HomologicalComplex.homCochainComplexFunctor C G).map g.op) n :=
  (h.mapHomCochainComplex G).homologyMap_eq n

end Homotopy

namespace HomologicalComplex

variable {C D : Type u} [Category.{v} C] [Category.{v} D] [Preadditive C] [Preadditive D]

/-- Fully faithful additive functor identifies Hom cochains objectwise.

For an additive fully faithful functor `F : C ⥤ D`, with `C` and `D` sharing their object
and morphism universe levels, the Hom cochain complex of `K` and `G` is
isomorphic to that of the image complex and `F.obj G`. Its degree maps apply `F.map` to Hom
morphisms. -/
noncomputable def homCochainComplexObjIsoOfFullyFaithful
    (F : C ⥤ D) [F.Additive] (hF : F.FullyFaithful) (G : C) (K : ChainComplex C ℕ) :
    (homCochainComplexFunctor C G).obj (Opposite.op K) ≅
      (homCochainComplexFunctor D (F.obj G)).obj
        (Opposite.op ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K)) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n =>
      (AddEquiv.ofBijective (F.mapAddHom (X := K.X n) (Y := G))
        (hF.map_bijective (X := K.X n) (Y := G))).toAddCommGrpIso)
    (fun i j hij => by
      ext f
      let f' : K.X i ⟶ G := f
      change F.map (K.d j i) ≫ F.map f' = F.map (K.d j i ≫ f')
      rw [← F.map_comp])

/-- Fully faithful Hom cochain comparison is natural in the chain complex.

For additive fully faithful `F`, the fixed-coefficient Hom functor in `C` is naturally
isomorphic to mapping chain complexes through `F` and taking Hom cochains into `F.obj G` in
`D`. -/
noncomputable def homCochainComplexFunctorIsoOfFullyFaithful
    (F : C ⥤ D) [F.Additive] (hF : F.FullyFaithful) (G : C) :
    homCochainComplexFunctor (C := C) G ≅
      (F.mapHomologicalComplex (ComplexShape.down ℕ)).op ⋙
        homCochainComplexFunctor D (F.obj G) :=
  NatIso.ofComponents
    (fun K => homCochainComplexObjIsoOfFullyFaithful F hF G K.unop)
    (fun {K L} f => by
      ext n g
      let g' : (Opposite.unop K).X n ⟶ G := g
      change F.map (f.unop.f n ≫ g') = F.map (f.unop.f n) ≫ F.map g'
      rw [F.map_comp])

/-- Fully faithful Hom cochain coordinate applies the functor to a morphism.

At chain complex `K` and degree `n`, the forward comparison sends `f : K.X n ⟶ G` to `F.map
f`. -/
@[simp]
lemma homCochainComplexFunctorIsoOfFullyFaithful_hom_app_f_apply
    (F : C ⥤ D) [F.Additive] (hF : F.FullyFaithful) (G : C)
    (K : ChainComplex C ℕ) (n : ℕ) (f : K.X n ⟶ G) :
    ((homCochainComplexFunctorIsoOfFullyFaithful F hF G).hom.app (Opposite.op K)).f n f =
      F.map f := rfl

/-- Fully faithful comparison is natural in both Hom cochain inputs.

The Hom cochain bifunctor in `C` is naturally isomorphic to the corresponding construction in
`D` after mapping both the coefficient and the chain complex through an additive fully
faithful `F`. -/
noncomputable def homCochainComplexBifunctorIsoOfFullyFaithful
    (F : Functor C D) [F.Additive] (hF : F.FullyFaithful) :
    homCochainComplexBifunctor C ≅
      F ⋙ homCochainComplexBifunctor D ⋙
        (Functor.whiskeringLeft
          (ChainComplex C ℕ)ᵒᵖ (ChainComplex D ℕ)ᵒᵖ
          (CochainComplex AddCommGrpCat.{v} ℕ)).obj
            (F.mapHomologicalComplex (ComplexShape.down ℕ)).op :=
  NatIso.ofComponents
    (fun G ↦ homCochainComplexFunctorIsoOfFullyFaithful F hF G)
    (fun {G G'} f ↦ by
      ext K n g
      let g' : K.unop.X n ⟶ G := g
      change F.map (g' ≫ f) = F.map g' ≫ F.map f
      rw [F.map_comp])

end HomologicalComplex
namespace HomologicalComplex.HomotopyEquiv

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {K L : ChainComplex C ℕ}

/-- Chain homotopy equivalence gives the reversed Hom cochain equivalence.

A homotopy equivalence `K ≃ L` induces a homotopy equivalence from the Hom cochains of `L` to
those of `K`, using precomposition with its forward and inverse chain maps. -/
public noncomputable def mapHomCochainComplex (e : HomotopyEquiv K L) (G : C) :
    HomotopyEquiv ((homCochainComplexFunctor C G).obj (Opposite.op L))
      ((homCochainComplexFunctor C G).obj (Opposite.op K)) where
  hom := (homCochainComplexFunctor C G).map e.hom.op
  inv := (homCochainComplexFunctor C G).map e.inv.op
  homotopyHomInvId := by
    have h := e.homotopyInvHomId.mapHomCochainComplex (G := G)
    simpa [Functor.map_comp, Functor.map_id] using h
  homotopyInvHomId := by
    have h := e.homotopyHomInvId.mapHomCochainComplex (G := G)
    simpa [Functor.map_comp, Functor.map_id] using h

/-- Chain homotopy equivalence gives natural Hom cohomology isomorphisms.

For a homotopy equivalence `K ≃ L` and natural degree `n`, the coefficient functors `H^n
Hom(L,-)` and `H^n Hom(K,-)` are naturally isomorphic. -/
public noncomputable def homCochainComplexHomologyNatIso {K L : ChainComplex C ℕ}
    (e : HomotopyEquiv K L) (n : ℕ) :
    homCochainComplexHomologyFunctor (C := C) L n ≅
      homCochainComplexHomologyFunctor (C := C) K n :=
  NatIso.ofComponents
    (fun G => (mapHomCochainComplex e G).toHomologyIso n)
    (fun {G G'} f => by
      change
        homologyMap (((homCochainComplexBifunctor C).map f).app
            (Opposite.op L)) n ≫
            homologyMap (((homCochainComplexBifunctor C).obj G').map e.hom.op) n =
          homologyMap (((homCochainComplexBifunctor C).obj G).map e.hom.op) n ≫
            homologyMap (((homCochainComplexBifunctor C).map f).app
                (Opposite.op K)) n
      exact homologyMap_square
        ((((homCochainComplexBifunctor C).map f).naturality e.hom.op).symm) n)

end HomologicalComplex.HomotopyEquiv
