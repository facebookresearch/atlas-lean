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

public import MathlibExt.Algebra.Homology.FirstQuadrantTotal
public import MathlibExt.Algebra.Homology.TotalComplexMap

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v₁ u₁ v₂ u₂

namespace HomologicalComplex₂

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasFiniteCoproducts C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D] [HasFiniteCoproducts D]
variable (F : C ⥤ D) [F.Additive] [PreservesFiniteCoproducts F]

noncomputable abbrev firstQuadrantMapTotalXIso
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ)) (n : ℕ) :
    F.obj ((K.total (ComplexShape.down ℕ)).X n) ≅
      ((mapBicomplex F K).total (ComplexShape.down ℕ)).X n :=
  mapTotalXIso F (ComplexShape.down ℕ) K n

@[reassoc (attr := simp)]
theorem map_ιTotal_comp_firstQuadrantMapTotalXIso_hom
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ))
    (p q n : ℕ) (h : p + q = n) :
    F.map (K.ιTotal (ComplexShape.down ℕ) p q n h) ≫
        (firstQuadrantMapTotalXIso F K n).hom =
      (mapBicomplex F K).ιTotal (ComplexShape.down ℕ) p q n h :=
  map_ιTotal_comp_mapTotalXIso_hom F (ComplexShape.down ℕ) K p q n h

@[reassoc (attr := simp)]
theorem mapped_ιTotal_comp_firstQuadrantMapTotalXIso_inv
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ))
    (p q n : ℕ) (h : p + q = n) :
    (mapBicomplex F K).ιTotal (ComplexShape.down ℕ) p q n h ≫
        (firstQuadrantMapTotalXIso F K n).inv =
      F.map (K.ιTotal (ComplexShape.down ℕ) p q n h) :=
  mapped_ιTotal_comp_mapTotalXIso_inv F (ComplexShape.down ℕ) K p q n h

@[reassoc (attr := simp)]
theorem map_ιTotalOrZero_comp_firstQuadrantMapTotalXIso_hom
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ))
    (p q n : ℕ) :
    F.map (K.ιTotalOrZero (ComplexShape.down ℕ) p q n) ≫
        (firstQuadrantMapTotalXIso F K n).hom =
      (mapBicomplex F K).ιTotalOrZero (ComplexShape.down ℕ) p q n :=
  map_ιTotalOrZero_comp_mapTotalXIso_hom F (ComplexShape.down ℕ) K p q n

@[reassoc (attr := simp)]
theorem map_d₁_comp_firstQuadrantMapTotalXIso_hom
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ))
    (p q n : ℕ) :
    F.map (K.d₁ (ComplexShape.down ℕ) p q n) ≫
        (firstQuadrantMapTotalXIso F K n).hom =
      (mapBicomplex F K).d₁ (ComplexShape.down ℕ) p q n :=
  map_d₁_comp_mapTotalXIso_hom F (ComplexShape.down ℕ) K p q n

@[reassoc (attr := simp)]
theorem map_d₂_comp_firstQuadrantMapTotalXIso_hom
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ))
    (p q n : ℕ) :
    F.map (K.d₂ (ComplexShape.down ℕ) p q n) ≫
        (firstQuadrantMapTotalXIso F K n).hom =
      (mapBicomplex F K).d₂ (ComplexShape.down ℕ) p q n :=
  map_d₂_comp_mapTotalXIso_hom F (ComplexShape.down ℕ) K p q n

theorem firstQuadrantMapTotalXIso_hom_d
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ)) (i j : ℕ) :
    (firstQuadrantMapTotalXIso F K i).hom ≫
        ((mapBicomplex F K).total (ComplexShape.down ℕ)).d i j =
      F.map ((K.total (ComplexShape.down ℕ)).d i j) ≫
        (firstQuadrantMapTotalXIso F K j).hom :=
  mapTotalXIso_hom_d F (ComplexShape.down ℕ) K i j

@[simps! hom_f inv_f]
noncomputable abbrev firstQuadrantMapTotalIso
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ)) :
    (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (K.total (ComplexShape.down ℕ)) ≅
      (mapBicomplex F K).total (ComplexShape.down ℕ) :=
  mapTotalIso F (ComplexShape.down ℕ) K

theorem firstQuadrantMapTotalIso_hom_naturality
    {K L : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ)} (f : K ⟶ L) :
    (F.mapHomologicalComplex (ComplexShape.down ℕ)).map
          (HomologicalComplex₂.total.map f (ComplexShape.down ℕ)) ≫
        (firstQuadrantMapTotalIso F L).hom =
      (firstQuadrantMapTotalIso F K).hom ≫
        HomologicalComplex₂.total.map ((mapBicomplexFunctor F).map f)
          (ComplexShape.down ℕ) :=
  mapTotalIso_hom_naturality F (ComplexShape.down ℕ) f

abbrev firstQuadrantMapAfterTotalFunctor :
    HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ) ⥤
      HomologicalComplex D (ComplexShape.down ℕ) :=
  mapAfterTotalFunctor F (ComplexShape.down ℕ)

abbrev firstQuadrantTotalAfterMapFunctor :
    HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ) ⥤
      HomologicalComplex D (ComplexShape.down ℕ) :=
  totalAfterMapFunctor F (ComplexShape.down ℕ)

noncomputable abbrev firstQuadrantMapTotalNatIso :
    firstQuadrantMapAfterTotalFunctor F ≅ firstQuadrantTotalAfterMapFunctor F :=
  mapTotalNatIso F (ComplexShape.down ℕ)

end HomologicalComplex₂

end

end
