/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Author: @toskua -/

module

public import MathlibExt.Algebra.Homology.FirstQuadrantCompleteFiltrationRestrictionHomology
public import MathlibExt.Algebra.Homology.FirstQuadrantHomologyFiltration

/-!
# Naturality and finite-stage comparison of homology image filtrations

Let C be an abelian category, f : K → L a morphism of bicomplexes of shape (down ℕ,down ℕ),
and G_i the horizontal stage at i ∈ ℕ. The square between H_n(G_i(K)) → H_n(Tot(K)) and
H_n(G_i(L)) → H_n(Tot(L)) gives a canonical map of their images.

The finite image filtration is isomorphic to the restriction of the complete EInt-indexed
image filtration along i ↦ (i : ℤ). These comparisons are defined both in the overcategory of
total homology and in its category of monic subobjects, and preserve the image inclusions.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

/-- Let C be an abelian category, f : K → L a morphism of bicomplexes of shape (down ℕ,down ℕ),
and n,i ∈ ℕ. Write h_i^K : H_n(G_i(K)) → H_n(Tot(K)) and h_i^L for the horizontal-stage maps.
The arrows H_n(G_i(f)) and H_n(Tot(f)) define a morphism h_i^K → h_i^L in Arrow(C), since
H_n(G_i(f)) ≫ h_i^L = h_i^K ≫ H_n(Tot(f)). This is the specified commutative square from which
the filtration image map is formed. -/
noncomputable def horizontalFiniteHomologyToTotalSquareOfBicomplex
    (f : K ⟶ L) (n i : ℕ) :
    Arrow.mk (HomologicalComplex.homologyMap
      (horizontalFilteredTotalComplexToTotal K i) n) ⟶
      Arrow.mk (HomologicalComplex.homologyMap
        (horizontalFilteredTotalComplexToTotal L i) n) :=
  Arrow.homMk
    (HomologicalComplex.homologyMap
      (horizontalFilteredTotalComplexMapOfBicomplex f i) n)
    (HomologicalComplex.homologyMap
      (total.map f (ComplexShape.down ℕ)) n)
    (NatTrans.congr_app
      ((horizontalTotalFiltrationHomologyDiagramToTotal n).naturality f) i)

/-- Let C be an abelian category, f : K → L a morphism of bicomplexes of shape (down ℕ,down ℕ),
and n,i ∈ ℕ. Applying the categorical image-map construction to the stage-to-total homology
square defines im(H_n(G_i(K)) → H_n(Tot(K))) → im(H_n(G_i(L)) → H_n(Tot(L))). Its source and
target are the stage-i subobjects of the total-homology image filtrations; its defining square
uses H_n(G_i(f)) on the stage and H_n(Tot(f)) on the total. -/
noncomputable def horizontalFiniteHomologyImageMapOfBicomplex
    (f : K ⟶ L) (n i : ℕ) :
    image (HomologicalComplex.homologyMap
      (horizontalFilteredTotalComplexToTotal K i) n) ⟶
      image (HomologicalComplex.homologyMap
        (horizontalFilteredTotalComplexToTotal L i) n) :=
  image.map (horizontalFiniteHomologyToTotalSquareOfBicomplex f n i)

/-- Let C be an abelian category, f : K → L a bicomplex map of shape (down ℕ,down ℕ), and n,i ∈ ℕ.
Let a_i be the induced map between the images of H_n(G_i) → H_n(Tot), and let ι_i^K and ι_i^L
be their canonical image inclusions. Then a_i ≫ ι_i^L = ι_i^K ≫ H_n(Tot(f)). Thus the map on
filtration images is compatible with the underlying map on total homology. -/
@[reassoc (attr := simp)]
theorem horizontalFiniteHomologyImageMapOfBicomplex_ι
    (f : K ⟶ L) (n i : ℕ) :
    horizontalFiniteHomologyImageMapOfBicomplex f n i ≫
        image.ι (HomologicalComplex.homologyMap
          (horizontalFilteredTotalComplexToTotal L i) n) =
      image.ι (HomologicalComplex.homologyMap
          (horizontalFilteredTotalComplexToTotal K i) n) ≫
        HomologicalComplex.homologyMap
          (total.map f (ComplexShape.down ℕ)) n :=
  image.map_ι (horizontalFiniteHomologyToTotalSquareOfBicomplex f n i)

/-- Let C be an abelian category, K a bicomplex of shape (down ℕ,down ℕ), and n ∈ ℕ. The arrows
H_n(G_i(K)) → H_n(Tot(K)) for finite horizontal stages i ∈ ℕ define a diagram ℕ →
Over(H_n(Tot(K))). For i ≤ j the morphism in the overcategory is H_n(G_i → G_j), with its
commutativity equation given by the compatibility of stage inclusions into the total complex. -/
noncomputable def horizontalFiniteHomologyOverDiagram
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (n : ℕ) :
    ℕ ⥤ Over ((K.total (ComplexShape.down ℕ)).homology n) :=
  ((horizontalTotalFiltrationHomologyDiagramFunctor n).obj K).toOver _
    (fun i => ((horizontalTotalFiltrationHomologyDiagramToTotal n).app K).app i)
    (fun {_ _} f => by
      have h :=
        ((horizontalTotalFiltrationHomologyDiagramToTotal n).app K).naturality f
      have hmap : ((horizontalTotalHomologyNatConstDiagramFunctor n).obj K).map f =
          𝟙 _ := by
        change HomologicalComplex.homologyMap
          (𝟙 (K.total (ComplexShape.down ℕ))) n = 𝟙 _
        exact (HomologicalComplex.homologyFunctor C
          (ComplexShape.down ℕ) n).map_id
            (K.total (ComplexShape.down ℕ))
      rw [hmap, Category.comp_id] at h
      exact h)

/-- Let C be an abelian category, K a bicomplex of shape (down ℕ,down ℕ), and n ∈ ℕ. For i ∈ ℕ
define F_iH_n(Tot(K)) = im(H_n(G_i(K)) → H_n(Tot(K))), where G_i retains horizontal columns at
most i. Applying the image functor to the finite stage-homology diagram over H_n(Tot(K)) gives
an ℕ-indexed filtration, with the canonical monic image inclusion at each stage. -/
noncomputable def horizontalFiniteTotalHomologyFiltration
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (n : ℕ) :
    CategoryTheory.Filtration
      ((K.total (ComplexShape.down ℕ)).homology n) ℕ where
  toMonoOver := horizontalFiniteHomologyOverDiagram K n ⋙ MonoOver.image

@[simp]
theorem horizontalFiniteTotalHomologyFiltration_obj
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (n i : ℕ) :
    (horizontalFiniteTotalHomologyFiltration K n).obj i =
      image (HomologicalComplex.homologyMap
        (horizontalFilteredTotalComplexToTotal K i) n) :=
  rfl

@[simp]
theorem horizontalFiniteTotalHomologyFiltration_ι_app
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (n i : ℕ) :
    (horizontalFiniteTotalHomologyFiltration K n).ι.app i =
      image.ι (HomologicalComplex.homologyMap
        (horizontalFilteredTotalComplexToTotal K i) n) :=
  rfl

/-- Let C be an abelian category, K a bicomplex of shape (down ℕ,down ℕ), and n ∈ ℕ. Restrict the
complete stage-homology diagram EInt → Over(H_n(Tot(K))) along the functor ℕ → EInt sending i
to the finite integer (i : ℤ). The resulting ℕ-indexed overcategory diagram has stage
H_n(G_{(i:ℤ)}(K)) → H_n(Tot(K)) and the complete-filtration transition maps. -/
noncomputable def horizontalCompleteHomologyNatRestrictionOverDiagram
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (n : ℕ) :
    ℕ ⥤ Over ((K.total (ComplexShape.down ℕ)).homology n) :=
  horizontalFiltrationNatToEIntFunctor ⋙
    horizontalCompleteHomologyOverDiagram K n

/-- Let C be an abelian category, K a bicomplex of shape (down ℕ,down ℕ), and n ∈ ℕ. The
restriction of the complete stage-homology overcategory diagram to i ∈ ℕ is naturally
isomorphic to the finite stage-homology diagram over H_n(Tot(K)). At i the isomorphism is
induced on H_n by the canonical identification of the complete stage at the finite integer i
with the horizontal stage G_i. Its component commutes with the arrows to total homology, so
the comparison is an isomorphism in Over(H_n(Tot(K))). -/
noncomputable def horizontalCompleteFiniteHomologyOverNatIso
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (n : ℕ) :
    horizontalCompleteHomologyNatRestrictionOverDiagram K n ≅
      horizontalFiniteHomologyOverDiagram K n :=
  NatIso.ofComponents
    (fun i => Over.isoMk
      ((horizontalCompleteTotalFiltrationNatRestrictionHomologyNatIso
        (C := C) n).app K |>.app i)
      (by
        have h := congrArg (fun α => (α.app K).app i)
          (horizontalCompleteTotalFiltrationNatRestrictionHomologyNatIso_hom_comp_toTotal
            (C := C) n)
        exact h))
    (by
      intro i j f
      apply CostructuredArrow.hom_ext
      exact ((horizontalCompleteTotalFiltrationNatRestrictionHomologyNatIso
        (C := C) n).hom.app K).naturality f)

/-- Let C be an abelian category, K a bicomplex of shape (down ℕ,down ℕ), and n ∈ ℕ. Taking images
of the complete-to-finite stage-homology comparison gives a natural isomorphism between the
natural-index restriction of the complete image-filtration diagram and the finite
image-filtration diagram in MonoOver(H_n(Tot(K))). Each component identifies the two chosen
image objects and commutes with their monomorphisms into the fixed total-homology object. -/
noncomputable def horizontalCompleteFiniteHomologyImageMonoOverNatIso
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (n : ℕ) :
    horizontalFiltrationNatToEIntFunctor ⋙
        (horizontalTotalHomologyFiltration K n).toMonoOver ≅
      (horizontalFiniteTotalHomologyFiltration K n).toMonoOver :=
  (Functor.associator horizontalFiltrationNatToEIntFunctor
      (horizontalCompleteHomologyOverDiagram K n)
      MonoOver.image).symm ≪≫
    Functor.isoWhiskerRight
      (horizontalCompleteFiniteHomologyOverNatIso K n)
      MonoOver.image

/-- Let C be an abelian category, K a bicomplex of shape (down ℕ,down ℕ), and n ∈ ℕ. Restrict the
complete total-homology image filtration along i ∈ ℕ ↦ (i : ℤ) ∈ EInt and forget the
overcategory structure. Its C-valued diagram is naturally isomorphic to the finite
image-filtration diagram. At each i this is the image comparison induced by H_n(G_{(i:ℤ)}(K))
≅ H_n(G_i(K)), with both stages mapped to H_n(Tot(K)). -/
noncomputable def horizontalCompleteFiniteHomologyFiltrationDiagramIso
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (n : ℕ) :
    horizontalFiltrationNatToEIntFunctor ⋙
        (horizontalTotalHomologyFiltration K n).diagram ≅
      (horizontalFiniteTotalHomologyFiltration K n).diagram :=
  (Functor.associator horizontalFiltrationNatToEIntFunctor
      (horizontalTotalHomologyFiltration K n).toMonoOver
      (MonoOver.forget _ ⋙ Over.forget _)).symm ≪≫
    Functor.isoWhiskerRight
      (horizontalCompleteFiniteHomologyImageMonoOverNatIso K n)
      (MonoOver.forget _ ⋙ Over.forget _)

@[simp]
theorem horizontalCompleteFiniteHomologyFiltrationDiagramIso_hom_app
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (n i : ℕ) :
    (horizontalCompleteFiniteHomologyFiltrationDiagramIso K n).hom.app i =
      ((horizontalCompleteFiniteHomologyImageMonoOverNatIso K n).hom.app i).hom.left := by
  simp [horizontalCompleteFiniteHomologyFiltrationDiagramIso]

/-- Let C be an abelian category, K a bicomplex of shape (down ℕ,down ℕ), and n,i ∈ ℕ. Let e_i :
F_{(i:ℤ)}^complete H_n(Tot(K)) ≅ F_i^finite H_n(Tot(K)) be the complete-to-finite filtration
comparison. Then e_i.hom ≫ ι_i^finite = ι_{(i:ℤ)}^complete, where both ι maps are the
canonical monomorphisms into H_n(Tot(K)). This fixes the orientation of the comparison as a
map from the restricted complete image to the finite image. -/
@[reassoc (attr := simp)]
theorem horizontalCompleteFiniteHomologyFiltrationDiagramIso_hom_ι
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (n i : ℕ) :
    (horizontalCompleteFiniteHomologyFiltrationDiagramIso K n).hom.app i ≫
        (horizontalFiniteTotalHomologyFiltration K n).ι.app i =
      (horizontalTotalHomologyFiltration K n).ι.app
        (((i : ℤ) : EInt)) := by
  rw [horizontalCompleteFiniteHomologyFiltrationDiagramIso_hom_app,
    horizontalFiniteTotalHomologyFiltration_ι_app,
    horizontalTotalHomologyFiltration_ι_app]
  exact MonoOver.w
    ((horizontalCompleteFiniteHomologyImageMonoOverNatIso K n).hom.app i)

end HomologicalComplex₂

end
