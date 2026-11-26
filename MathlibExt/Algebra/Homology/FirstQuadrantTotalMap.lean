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

/-!
# Additive functors commute with first-quadrant totalization

Let C,D be preadditive categories with finite coproducts and F:C→D an additive functor
preserving finite coproducts. For a bicomplex K of shape (down ℕ,down ℕ), each total degree n is
the finite coproduct of K_{p,q} over p+q=n. Coproduct preservation therefore gives
e_{K,n}:F((Tot K)_n)≅(Tot(FK))_n, with the canonical equations on forward and inverse summand
inclusions.

The comparison also intertwines the horizontal and vertical differential contributions,
including the vertical sign (-1)^p, and hence the full total differential. These term
comparisons assemble into a chain isomorphism F(Tot K)≅Tot(FK), natural in every bicomplex map.
They give a natural isomorphism between mapping after totalization and totalizing after mapping
both bicomplex coordinates. Source and target object and morphism universes are independent.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v₁ u₁ v₂ u₂

namespace HomologicalComplex₂

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasFiniteCoproducts C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D] [HasFiniteCoproducts D]
variable (F : C ⥤ D) [F.Additive] [PreservesFiniteCoproducts F]

/-- Let C,D be preadditive categories with finite coproducts, in independent object and morphism
universes, and F:C→D an additive functor preserving finite coproducts. For a bicomplex K of
shape (down ℕ,down ℕ) and n∈ℕ, this is the canonical isomorphism e_{K,n}:F((Tot
K)_n)≅(Tot(FK))_n. It identifies F of the finite coproduct over p+q=n with the coproduct of
F(K_{p,q}), using F's finite-coproduct preservation. -/
noncomputable abbrev firstQuadrantMapTotalXIso
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ)) (n : ℕ) :
    F.obj ((K.total (ComplexShape.down ℕ)).X n) ≅
      ((mapBicomplex F K).total (ComplexShape.down ℕ)).X n :=
  mapTotalXIso F (ComplexShape.down ℕ) K n

/-- Let C,D be preadditive categories with finite coproducts, in independent object and morphism
universes, and F:C→D an additive functor preserving finite coproducts. For a first-quadrant
bicomplex K and p,q,n∈ℕ with p+q=n, let ι^K_{p,q}:K_{p,q}→(Tot K)_n and
ι^{FK}_{p,q}:F(K_{p,q})→(Tot(FK))_n be total-summand inclusions. Then
F(ι^K_{p,q})≫e_{K,n}.hom=ι^{FK}_{p,q}. -/
@[reassoc (attr := simp)]
theorem map_ιTotal_comp_firstQuadrantMapTotalXIso_hom
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ))
    (p q n : ℕ) (h : p + q = n) :
    F.map (K.ιTotal (ComplexShape.down ℕ) p q n h) ≫
        (firstQuadrantMapTotalXIso F K n).hom =
      (mapBicomplex F K).ιTotal (ComplexShape.down ℕ) p q n h :=
  map_ιTotal_comp_mapTotalXIso_hom F (ComplexShape.down ℕ) K p q n h

/-- Let C,D be preadditive categories with finite coproducts, in independent object and morphism
universes, and F:C→D an additive functor preserving finite coproducts. For a first-quadrant
bicomplex K and p,q,n∈ℕ with p+q=n, the inverse term comparison satisfies
ι^{FK}_{p,q}≫e_{K,n}.inv=F(ι^K_{p,q}). Both sides map F(K_{p,q}) into F((Tot K)_n). -/
@[reassoc (attr := simp)]
theorem mapped_ιTotal_comp_firstQuadrantMapTotalXIso_inv
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ))
    (p q n : ℕ) (h : p + q = n) :
    (mapBicomplex F K).ιTotal (ComplexShape.down ℕ) p q n h ≫
        (firstQuadrantMapTotalXIso F K n).inv =
      F.map (K.ιTotal (ComplexShape.down ℕ) p q n h) :=
  mapped_ιTotal_comp_mapTotalXIso_inv F (ComplexShape.down ℕ) K p q n h

/-- Let C,D be preadditive categories with finite coproducts, in independent object and morphism
universes, and F:C→D an additive functor preserving finite coproducts. For a first-quadrant
bicomplex K and arbitrary p,q,n∈ℕ, define ι^0_{p,q,n}:K_{p,q}→(Tot K)_n to be the summand
inclusion when p+q=n and zero otherwise. Then F(ι^0_{p,q,n})≫e_{K,n}.hom is the corresponding
inclusion-or-zero map for FK. Additivity of F supplies the zero case. -/
@[reassoc (attr := simp)]
theorem map_ιTotalOrZero_comp_firstQuadrantMapTotalXIso_hom
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ))
    (p q n : ℕ) :
    F.map (K.ιTotalOrZero (ComplexShape.down ℕ) p q n) ≫
        (firstQuadrantMapTotalXIso F K n).hom =
      (mapBicomplex F K).ιTotalOrZero (ComplexShape.down ℕ) p q n :=
  map_ιTotalOrZero_comp_mapTotalXIso_hom F (ComplexShape.down ℕ) K p q n

/-- Let C,D be preadditive categories with finite coproducts, in independent object and morphism
universes, and F:C→D an additive functor preserving finite coproducts. For a first-quadrant
bicomplex K and p,q,n∈ℕ, let d₁^K:K_{p,q}→(Tot K)_n be the horizontal differential followed by
the inclusion of (p−1,q) when p>0 and (p−1)+q=n, and zero otherwise. Then
F(d₁^K)≫e_{K,n}.hom=d₁^{FK}. The horizontal totalization sign is one. -/
@[reassoc (attr := simp)]
theorem map_d₁_comp_firstQuadrantMapTotalXIso_hom
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ))
    (p q n : ℕ) :
    F.map (K.d₁ (ComplexShape.down ℕ) p q n) ≫
        (firstQuadrantMapTotalXIso F K n).hom =
      (mapBicomplex F K).d₁ (ComplexShape.down ℕ) p q n :=
  map_d₁_comp_mapTotalXIso_hom F (ComplexShape.down ℕ) K p q n

/-- Let C,D be preadditive categories with finite coproducts, in independent object and morphism
universes, and F:C→D an additive functor preserving finite coproducts. For a first-quadrant
bicomplex K and p,q,n∈ℕ, let d₂^K:K_{p,q}→(Tot K)_n be (-1)^p times the vertical differential
followed by the inclusion of (p,q−1) when q>0 and p+(q−1)=n, and zero otherwise. Then
F(d₂^K)≫e_{K,n}.hom=d₂^{FK}. Additivity preserves the integer vertical sign. -/
@[reassoc (attr := simp)]
theorem map_d₂_comp_firstQuadrantMapTotalXIso_hom
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ))
    (p q n : ℕ) :
    F.map (K.d₂ (ComplexShape.down ℕ) p q n) ≫
        (firstQuadrantMapTotalXIso F K n).hom =
      (mapBicomplex F K).d₂ (ComplexShape.down ℕ) p q n :=
  map_d₂_comp_mapTotalXIso_hom F (ComplexShape.down ℕ) K p q n

/-- Let C,D be preadditive categories with finite coproducts, in independent object and morphism
universes, and F:C→D an additive functor preserving finite coproducts. For a first-quadrant
bicomplex K and i,j∈ℕ, let e_{K,i},e_{K,j} be the term comparisons. Then
e_{K,i}.hom≫d^{Tot(FK)}_{i,j}=F(d^{Tot K}_{i,j})≫e_{K,j}.hom. The equality includes the zero
differential pairs outside the shape down ℕ and combines the horizontal and signed vertical
contributions on each total summand. -/
theorem firstQuadrantMapTotalXIso_hom_d
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ)) (i j : ℕ) :
    (firstQuadrantMapTotalXIso F K i).hom ≫
        ((mapBicomplex F K).total (ComplexShape.down ℕ)).d i j =
      F.map ((K.total (ComplexShape.down ℕ)).d i j) ≫
        (firstQuadrantMapTotalXIso F K j).hom :=
  mapTotalXIso_hom_d F (ComplexShape.down ℕ) K i j

/-- Let C,D be preadditive categories with finite coproducts, in independent object and morphism
universes, and F:C→D an additive functor preserving finite coproducts. For a bicomplex K of
shape (down ℕ,down ℕ), the term comparisons e_{K,n} give this chain isomorphism F(Tot
K)≅Tot(FK), where F is applied termwise to the source total and to both coordinates of K in the
target. Its degree-n forward and inverse maps are e_{K,n}.hom and e_{K,n}.inv. -/
@[simps! hom_f inv_f]
noncomputable abbrev firstQuadrantMapTotalIso
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ)) :
    (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (K.total (ComplexShape.down ℕ)) ≅
      (mapBicomplex F K).total (ComplexShape.down ℕ) :=
  mapTotalIso F (ComplexShape.down ℕ) K

/-- Let C,D be preadditive categories with finite coproducts, in independent object and morphism
universes, and F:C→D an additive functor preserving finite coproducts. For a bicomplex morphism
f:K→L of shape (down ℕ,down ℕ), let e_K:F(Tot K)≅Tot(FK) and e_L be the comparison isomorphisms.
Then F(Tot f)≫e_L.hom=e_K.hom≫Tot(Ff), as maps F(Tot K)→Tot(FL). The functor F is applied
termwise to chain and bicomplex maps. -/
theorem firstQuadrantMapTotalIso_hom_naturality
    {K L : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ)} (f : K ⟶ L) :
    (F.mapHomologicalComplex (ComplexShape.down ℕ)).map
          (HomologicalComplex₂.total.map f (ComplexShape.down ℕ)) ≫
        (firstQuadrantMapTotalIso F L).hom =
      (firstQuadrantMapTotalIso F K).hom ≫
        HomologicalComplex₂.total.map ((mapBicomplexFunctor F).map f)
          (ComplexShape.down ℕ) :=
  mapTotalIso_hom_naturality F (ComplexShape.down ℕ) f

/-- Let C,D be preadditive categories with finite coproducts, in independent object and morphism
universes, and F:C→D an additive functor preserving finite coproducts. This functor sends a
bicomplex K of shape (down ℕ,down ℕ) to F(Tot K), with F applied termwise to the total chain
complex, and sends a morphism f to F(Tot f). Its target is the category of D-valued chain
complexes of shape down ℕ. -/
abbrev firstQuadrantMapAfterTotalFunctor :
    HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ) ⥤
      HomologicalComplex D (ComplexShape.down ℕ) :=
  mapAfterTotalFunctor F (ComplexShape.down ℕ)

/-- Let C,D be preadditive categories with finite coproducts, in independent object and morphism
universes, and F:C→D an additive functor preserving finite coproducts. This functor sends a
bicomplex K of shape (down ℕ,down ℕ) to Tot(FK), where F is applied to each entry and each
horizontal and vertical differential, and sends f to Tot(Ff). Its target is the category of
D-valued chain complexes of shape down ℕ. -/
abbrev firstQuadrantTotalAfterMapFunctor :
    HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ) ⥤
      HomologicalComplex D (ComplexShape.down ℕ) :=
  totalAfterMapFunctor F (ComplexShape.down ℕ)

/-- Let C,D be preadditive categories with finite coproducts, in independent object and morphism
universes, and F:C→D an additive functor preserving finite coproducts. The chain comparisons
e_K:F(Tot K)≅Tot(FK) form this natural isomorphism from the functor that maps after totalization
to the functor that totalizes after mapping both bicomplex coordinates. For every f:K→L, its
naturality equation is F(Tot f)≫e_L.hom=e_K.hom≫Tot(Ff). -/
noncomputable abbrev firstQuadrantMapTotalNatIso :
    firstQuadrantMapAfterTotalFunctor F ≅ firstQuadrantTotalAfterMapFunctor F :=
  mapTotalNatIso F (ComplexShape.down ℕ)

end HomologicalComplex₂

end

end
