/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Author: @toskua -/

module

public import
  MathlibExt.Algebra.Homology.FirstQuadrantCompleteFiltrationSpectralNaturality
public import MathlibExt.Algebra.Homology.FirstQuadrantSecondPage
public import MathlibExt.Algebra.Homology.SpectralObjectPageMapNaturality

/-!
# Bicomplex maps on first-quadrant spectral-sequence pages

Let C be an abelian category and f : K → L a map of bicomplexes of shape (down ℕ,down ℕ). The
map of their complete horizontal filtrations induces a chain map on every fixed page r≥1,
whose differential has bidegree (−r,r−1). A bicomplex isomorphism gives an isomorphism on each
page and each page-two term.

For p,q ∈ ℕ, page two is expressed using the filtration indices p−2 ≤ p−1 ≤ p ≤ p+1 and
cochain degrees ℓ−1,ℓ,ℓ+1, where ℓ=−p−q. Its object is the homology of the connecting-map
short complex between the three consecutive relative cone homologies. The page-two map is
conjugate, through this presentation, to the induced map on that homology.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L M : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

local notation "data" =>
  CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological

@[simp]
private theorem horizontalCompleteFilteredTotalComplexMapOfBicomplex_id
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (i : EInt) :
    horizontalCompleteFilteredTotalComplexMapOfBicomplex (𝟙 K) i = 𝟙 _ := by
  have h := congrArg (fun k => k.natTrans.app i)
    (horizontalCompleteTotalFilteredObjectFunctor.map_id K)
  exact h

@[reassoc, simp]
private theorem horizontalCompleteFilteredTotalComplexMapOfBicomplex_comp
    (f : K ⟶ L) (g : L ⟶ M) (i : EInt) :
    horizontalCompleteFilteredTotalComplexMapOfBicomplex (f ≫ g) i =
      horizontalCompleteFilteredTotalComplexMapOfBicomplex f i ≫
        horizontalCompleteFilteredTotalComplexMapOfBicomplex g i := by
  have h := congrArg (fun k => k.natTrans.app i)
    (horizontalCompleteTotalFilteredObjectFunctor.map_comp f g)
  exact h

@[simp]
private theorem horizontalCompleteFiltrationCochainDiagramNatTrans_id
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) :
    horizontalCompleteFiltrationCochainDiagramNatTrans (𝟙 K) = 𝟙 _ := by
  apply NatTrans.ext
  funext i
  rw [horizontalCompleteFiltrationCochainDiagramNatTrans_app,
    horizontalCompleteFilteredTotalComplexMapOfBicomplex_id]
  exact (ComplexShape.embeddingDownNat.extendFunctor C).map_id _

@[reassoc, simp]
private theorem horizontalCompleteFiltrationCochainDiagramNatTrans_comp
    (f : K ⟶ L) (g : L ⟶ M) :
    horizontalCompleteFiltrationCochainDiagramNatTrans (f ≫ g) =
      horizontalCompleteFiltrationCochainDiagramNatTrans f ≫
        horizontalCompleteFiltrationCochainDiagramNatTrans g := by
  apply NatTrans.ext
  funext i
  change HomologicalComplex.extendMap
      (horizontalCompleteFilteredTotalComplexMapOfBicomplex (f ≫ g) i)
        ComplexShape.embeddingDownNat =
    HomologicalComplex.extendMap
        (horizontalCompleteFilteredTotalComplexMapOfBicomplex f i)
          ComplexShape.embeddingDownNat ≫
      HomologicalComplex.extendMap
        (horizontalCompleteFilteredTotalComplexMapOfBicomplex g i)
          ComplexShape.embeddingDownNat
  rw [horizontalCompleteFilteredTotalComplexMapOfBicomplex_comp]
  exact (ComplexShape.embeddingDownNat.extendFunctor C).map_comp _ _

@[simp]
private theorem horizontalCompleteFiltrationMappingConeNatTrans_id
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) :
    horizontalCompleteFiltrationMappingConeNatTrans (𝟙 K) = 𝟙 _ := by
  apply NatTrans.ext
  funext D
  let η := horizontalCompleteFiltrationCochainDiagramNatTrans (𝟙 K)
  have hη : η = 𝟙 _ :=
    horizontalCompleteFiltrationCochainDiagramNatTrans_id K
  let φ := (horizontalCompleteFiltrationCochainDiagram K).map (D.map' 0 1)
  change CochainComplex.mappingCone.map φ φ
      (η.app (D.obj 0)) (η.app (D.obj 1))
        (η.naturality (D.map' 0 1)) = 𝟙 (CochainComplex.mappingCone φ)
  rw [show η = 𝟙 _ from hη]
  exact CochainComplex.mappingCone.map_id φ

@[reassoc, simp]
private theorem horizontalCompleteFiltrationMappingConeNatTrans_comp
    (f : K ⟶ L) (g : L ⟶ M) :
    horizontalCompleteFiltrationMappingConeNatTrans (f ≫ g) =
      horizontalCompleteFiltrationMappingConeNatTrans f ≫
        horizontalCompleteFiltrationMappingConeNatTrans g := by
  apply NatTrans.ext
  funext D
  let ηfg := horizontalCompleteFiltrationCochainDiagramNatTrans (f ≫ g)
  let ηf := horizontalCompleteFiltrationCochainDiagramNatTrans f
  let ηg := horizontalCompleteFiltrationCochainDiagramNatTrans g
  have hη : ηfg = ηf ≫ ηg :=
    horizontalCompleteFiltrationCochainDiagramNatTrans_comp f g
  let φK := (horizontalCompleteFiltrationCochainDiagram K).map (D.map' 0 1)
  let φL := (horizontalCompleteFiltrationCochainDiagram L).map (D.map' 0 1)
  let φM := (horizontalCompleteFiltrationCochainDiagram M).map (D.map' 0 1)
  change CochainComplex.mappingCone.map φK φM
      (ηfg.app (D.obj 0)) (ηfg.app (D.obj 1))
        (ηfg.naturality (D.map' 0 1)) =
    CochainComplex.mappingCone.map φK φL
        (ηf.app (D.obj 0)) (ηf.app (D.obj 1))
          (ηf.naturality (D.map' 0 1)) ≫
      CochainComplex.mappingCone.map φL φM
        (ηg.app (D.obj 0)) (ηg.app (D.obj 1))
          (ηg.naturality (D.map' 0 1))
  rw [show ηfg = ηf ≫ ηg from hη]
  exact CochainComplex.mappingCone.map_comp φK φL φM
    (ηf.app (D.obj 0)) (ηf.app (D.obj 1))
      (ηf.naturality (D.map' 0 1))
    (ηg.app (D.obj 0)) (ηg.app (D.obj 1))
      (ηg.naturality (D.map' 0 1))

@[simp]
private theorem horizontalCompleteFiltrationTriangulatedSpectralObjectMap_id
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) :
    horizontalCompleteFiltrationTriangulatedSpectralObjectMap (𝟙 K) = 𝟙 _ := by
  apply CategoryTheory.Triangulated.SpectralObject.hom_ext
  dsimp [horizontalCompleteFiltrationTriangulatedSpectralObjectMap]
  rw [horizontalCompleteFiltrationMappingConeNatTrans_id]
  simp
  rfl

@[reassoc, simp]
private theorem horizontalCompleteFiltrationTriangulatedSpectralObjectMap_comp
    (f : K ⟶ L) (g : L ⟶ M) :
    horizontalCompleteFiltrationTriangulatedSpectralObjectMap (f ≫ g) =
      horizontalCompleteFiltrationTriangulatedSpectralObjectMap f ≫
        horizontalCompleteFiltrationTriangulatedSpectralObjectMap g := by
  apply CategoryTheory.Triangulated.SpectralObject.hom_ext
  dsimp [horizontalCompleteFiltrationTriangulatedSpectralObjectMap]
  rw [horizontalCompleteFiltrationMappingConeNatTrans_comp]
  simp

@[simp]
private theorem horizontalCompleteFiltrationSpectralObjectMap_id
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) :
    horizontalCompleteFiltrationSpectralObjectMap (𝟙 K) = 𝟙 _ := by
  dsimp [horizontalCompleteFiltrationSpectralObjectMap]
  rw [horizontalCompleteFiltrationTriangulatedSpectralObjectMap_id]
  exact
    (CategoryTheory.Triangulated.SpectralObject.mapHomologicalFunctorFunctor
      (HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) 0) EInt).map_id _

@[reassoc, simp]
private theorem horizontalCompleteFiltrationSpectralObjectMap_comp
    (f : K ⟶ L) (g : L ⟶ M) :
    horizontalCompleteFiltrationSpectralObjectMap (f ≫ g) =
      horizontalCompleteFiltrationSpectralObjectMap f ≫
        horizontalCompleteFiltrationSpectralObjectMap g := by
  dsimp [horizontalCompleteFiltrationSpectralObjectMap]
  rw [horizontalCompleteFiltrationTriangulatedSpectralObjectMap_comp]
  exact
    (CategoryTheory.Triangulated.SpectralObject.mapHomologicalFunctorFunctor
      (HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) 0) EInt).map_comp _ _

unseal CategoryTheory.Abelian.SpectralObject.spectralSequence in
/-- Let C be an abelian category, f : K → L a map of bicomplexes of shape (down ℕ,down ℕ), and r ∈
ℤ with 1 ≤ r. The morphism of complete horizontal filtration spectral objects induced by f
gives a homological-complex map E^r(K) → E^r(L). These pages have index set ℕ×ℕ and
differential bidegree (−r,r−1). Its component at a bidegree is the corresponding
spectral-object page map, and it commutes with the fixed-page differentials. -/
noncomputable def horizontalPageMapOfBicomplex
    (f : K ⟶ L) (r : ℤ) (hr : 1 ≤ r) :
    (horizontalFirstQuadrantSpectralSequence K).page r hr ⟶
      (horizontalFirstQuadrantSpectralSequence L).page r hr :=
  CategoryTheory.Abelian.SpectralObject.Hom.pageMap
    (horizontalCompleteFiltrationSpectralObjectMap f) data r hr

unseal CategoryTheory.Abelian.SpectralObject.spectralSequence in
/-- Let C be an abelian category, f : K → L a bicomplex map of shape (down ℕ,down ℕ), r ∈ ℤ with
r≥1, and (p,q) ∈ ℕ×ℕ. The (p,q)-component of the map E^r(K) → E^r(L) equals the
spectral-object pageMapComponent induced by f. In its canonical presentation, this is the map
on homology of the connecting-map short complex at filtration indices p−r ≤ p−1 ≤ p ≤ p+r−1
and consecutive cochain degrees −p−q−1,−p−q,−p−q+1, transported through the two page-object
isomorphisms. The stage maps in this short complex are induced by the complete horizontal
filtration map of f. -/
@[simp]
theorem horizontalPageMapOfBicomplex_f
    (f : K ⟶ L) (r : ℤ) (hr : 1 ≤ r) (pq : ℕ × ℕ) :
    (horizontalPageMapOfBicomplex f r hr).f pq =
      CategoryTheory.Abelian.SpectralObject.Hom.pageMapComponent
        (horizontalCompleteFiltrationSpectralObjectMap f) data r hr pq :=
  rfl

unseal CategoryTheory.Abelian.SpectralObject.spectralSequence in
@[simp]
theorem horizontalPageMapOfBicomplex_id
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (r : ℤ) (hr : 1 ≤ r) :
    horizontalPageMapOfBicomplex (𝟙 K) r hr = 𝟙 _ := by
  dsimp [horizontalPageMapOfBicomplex]
  rw [horizontalCompleteFiltrationSpectralObjectMap_id,
    CategoryTheory.Abelian.SpectralObject.Hom.pageMap_id]
  rfl

unseal CategoryTheory.Abelian.SpectralObject.spectralSequence in
@[reassoc, simp]
theorem horizontalPageMapOfBicomplex_comp
    (f : K ⟶ L) (g : L ⟶ M) (r : ℤ) (hr : 1 ≤ r) :
    horizontalPageMapOfBicomplex (f ≫ g) r hr =
      horizontalPageMapOfBicomplex f r hr ≫
        horizontalPageMapOfBicomplex g r hr := by
  dsimp [horizontalPageMapOfBicomplex]
  rw [horizontalCompleteFiltrationSpectralObjectMap_comp,
    CategoryTheory.Abelian.SpectralObject.Hom.pageMap_comp]

/-- Let C be an abelian category, f : K → L an invertible bicomplex morphism of shape (down ℕ,down
ℕ), and r ∈ ℤ with 1 ≤ r. The induced map E^r(K) → E^r(L) is an isomorphism of page complexes.
Its inverse is the fixed-page map induced by f⁻¹, with the same page index r and spectral
differential shape of bidegree (−r,r−1). -/
noncomputable instance isIso_horizontalPageMapOfBicomplex
    (f : K ⟶ L) [IsIso f] (r : ℤ) (hr : 1 ≤ r) :
    IsIso (horizontalPageMapOfBicomplex f r hr) :=
  ⟨⟨horizontalPageMapOfBicomplex (inv f) r hr, by
      rw [← horizontalPageMapOfBicomplex_comp, IsIso.hom_inv_id,
        horizontalPageMapOfBicomplex_id], by
      rw [← horizontalPageMapOfBicomplex_comp, IsIso.inv_hom_id,
        horizontalPageMapOfBicomplex_id]⟩⟩

/-- Let C be an abelian category, f : K → L a bicomplex map of shape (down ℕ,down ℕ), and p,q ∈ ℕ.
Define E²_{p,q}(K) → E²_{p,q}(L) to be the (p,q)-component of the fixed-page map at r=2. It is
induced by the map of complete horizontal filtration spectral objects and uses the page-two
differential shape of bidegree (−2,1). -/
noncomputable def horizontalSecondPageMapOfBicomplex
    (f : K ⟶ L) (p q : ℕ) :
    ((horizontalFirstQuadrantSpectralSequence K).page 2).X (p, q) ⟶
      ((horizontalFirstQuadrantSpectralSequence L).page 2).X (p, q) :=
  (horizontalPageMapOfBicomplex f 2 (by omega)).f (p, q)

@[simp]
theorem horizontalSecondPageMapOfBicomplex_id
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (p q : ℕ) :
    horizontalSecondPageMapOfBicomplex (𝟙 K) p q = 𝟙 _ := by
  have h := congrArg (fun k => k.f (p, q))
    (horizontalPageMapOfBicomplex_id K 2 (by omega))
  exact h

@[reassoc, simp]
theorem horizontalSecondPageMapOfBicomplex_comp
    (f : K ⟶ L) (g : L ⟶ M) (p q : ℕ) :
    horizontalSecondPageMapOfBicomplex (f ≫ g) p q =
      horizontalSecondPageMapOfBicomplex f p q ≫
        horizontalSecondPageMapOfBicomplex g p q := by
  have h := congrArg (fun k => k.f (p, q))
    (horizontalPageMapOfBicomplex_comp f g 2 (by omega))
  exact h

/-- Let C be an abelian category, f : K → L an invertible bicomplex morphism of shape (down ℕ,down
ℕ), and p,q ∈ ℕ. The induced component E²_{p,q}(K) → E²_{p,q}(L) is an isomorphism in C. Its
inverse is the corresponding second-page component induced by f⁻¹. -/
noncomputable instance isIso_horizontalSecondPageMapOfBicomplex
    (f : K ⟶ L) [IsIso f] (p q : ℕ) :
    IsIso (horizontalSecondPageMapOfBicomplex f p q) := by
  dsimp only [horizontalSecondPageMapOfBicomplex]
  infer_instance

/-- For a column p ∈ ℕ, the lower filtration index in the page-two presentation is the finite
integer (p:ℤ)−2 embedded in EInt = ℤ ∪ {⊥,⊤}. The subtraction is in ℤ, so the value is −2 at
p=0 and −1 at p=1. It is the first index in the chain p−2 ≤ p−1 ≤ p ≤ p+1. -/
abbrev horizontalSecondPageLowerIndex (p : ℕ) : EInt :=
  @WithBotTop.coe ℤ ((p : ℤ) - 2)

/-- For a column p ∈ ℕ, the upper filtration index in the page-two presentation is the finite
integer (p:ℤ)+2−1 = p+1 embedded in EInt. It is the last index in the chain p−2 ≤ p−1 ≤ p ≤
p+1 used to present the page-two term. -/
abbrev horizontalSecondPageUpperIndex (p : ℕ) : EInt :=
  @WithBotTop.coe ℤ ((p : ℤ) + 2 - 1)

/-- Let C be an abelian category, K a bicomplex of shape (down ℕ,down ℕ), and p,q ∈ ℕ. Write F_i
for the complete horizontal chain stage placed in cochain degrees by n ↦ −n, and set ℓ=−p−q.
The page term E²_{p,q}(K) is canonically isomorphic to the homology of H^{ℓ−1}(Cone(F_p →
F_{p+1})) → H^ℓ(Cone(F_{p−1} → F_p)) → H^{ℓ+1}(Cone(F_{p−2} → F_{p−1})). Both arrows are the
spectral connecting maps of the cone composition triangles. This is the spectral-object E
presentation with integer filtration indices p−2,p−1,p,p+1 and consecutive cochain degrees
ℓ−1,ℓ,ℓ+1. -/
noncomputable def horizontalSecondPageXIso
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (p q : ℕ) :
    ((horizontalFirstQuadrantSpectralSequence K).page 2).X (p, q) ≅
      (horizontalCompleteFiltrationSpectralObject K).E
        (homOfLE ((data).le₀₁' 2 (by omega) (p, q) rfl rfl))
        (homOfLE ((data).le₁₂' (p, q) rfl rfl))
        (homOfLE ((data).le₂₃' 2 (by omega) (p, q) rfl rfl))
        (-(p : ℤ) - (q : ℤ) - 1)
        (-(p : ℤ) - (q : ℤ))
        (-(p : ℤ) - (q : ℤ) + 1) :=
  (horizontalCompleteFiltrationSpectralObject K).spectralSequencePageXIso
    data 2 (by omega) (p, q)
    (horizontalSecondPageLowerIndex p)
    (horizontalFirstPageLowerIndex p)
    (horizontalFirstPageUpperIndex p)
    (horizontalSecondPageUpperIndex p)
    rfl rfl rfl rfl
    (-(p : ℤ) - (q : ℤ) - 1)
    (-(p : ℤ) - (q : ℤ))
    (-(p : ℤ) - (q : ℤ) + 1) rfl (by omega) rfl

/-- Let C be an abelian category, f : K → L a bicomplex map of shape (down ℕ,down ℕ), and p,q ∈ ℕ.
Set ℓ=−p−q and form, for each bicomplex, the short complex H^{ℓ−1}(Cone(F_p → F_{p+1})) →
H^ℓ(Cone(F_{p−1} → F_p)) → H^{ℓ+1}(Cone(F_{p−2} → F_{p−1})), with spectral connecting arrows
and F_i the complete horizontal cochain stages. The stage maps induced by f give a morphism of
these short complexes. Define the page-two EMap to be its induced map on homology, using the
same four filtration indices and three cochain degrees. -/
noncomputable def horizontalSecondPageEMapOfBicomplex
    (f : K ⟶ L) (p q : ℕ) :=
  CategoryTheory.Abelian.SpectralObject.Hom.EMap
    (horizontalCompleteFiltrationSpectralObjectMap f)
    (homOfLE ((data).le₀₁' 2 (by omega) (p, q) rfl rfl))
    (homOfLE ((data).le₁₂' (p, q) rfl rfl))
    (homOfLE ((data).le₂₃' 2 (by omega) (p, q) rfl rfl))
    (-(p : ℤ) - (q : ℤ) - 1)
    (-(p : ℤ) - (q : ℤ))
    (-(p : ℤ) - (q : ℤ) + 1) (by omega) rfl

unseal CategoryTheory.Abelian.SpectralObject.spectralSequence in
/-- Let C be an abelian category, f : K → L a bicomplex map of shape (down ℕ,down ℕ), and p,q ∈ ℕ.
Let e_K and e_L identify E²_{p,q} with the homology of the spectral connecting-map short
complex at filtration indices p−2 ≤ p−1 ≤ p ≤ p+1 and cochain degrees −p−q−1,−p−q,−p−q+1. If a
is the homology map of that short complex induced by f, then the second-page component is
e_K.hom ≫ a ≫ e_L.inv. This fixes both the presentation and the direction of the conjugation. -/
theorem horizontalSecondPageMapOfBicomplex_eq
    (f : K ⟶ L) (p q : ℕ) :
    horizontalSecondPageMapOfBicomplex f p q =
      (horizontalSecondPageXIso K p q).hom ≫
        horizontalSecondPageEMapOfBicomplex f p q ≫
        (horizontalSecondPageXIso L p q).inv := by
  apply (cancel_mono (horizontalSecondPageXIso L p q).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  dsimp only [horizontalSecondPageMapOfBicomplex]
  rw [horizontalPageMapOfBicomplex_f]
  dsimp only [horizontalSecondPageXIso,
    horizontalSecondPageEMapOfBicomplex]
  exact
    CategoryTheory.Abelian.SpectralObject.Hom.pageMapComponent_pageXIso_hom
      (horizontalCompleteFiltrationSpectralObjectMap f) data 2 (by omega)
      (p, q) (horizontalSecondPageLowerIndex p)
      (horizontalFirstPageLowerIndex p) (horizontalFirstPageUpperIndex p)
      (horizontalSecondPageUpperIndex p) rfl rfl rfl rfl
      (-(p : ℤ) - (q : ℤ) - 1) (-(p : ℤ) - (q : ℤ))
      (-(p : ℤ) - (q : ℤ) + 1) rfl (by omega) rfl

end HomologicalComplex₂

end
