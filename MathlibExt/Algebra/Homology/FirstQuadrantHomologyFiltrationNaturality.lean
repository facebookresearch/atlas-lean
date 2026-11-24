/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.FirstQuadrantCompleteFiltrationRestrictionHomology
public import MathlibExt.Algebra.Homology.FirstQuadrantHomologyFiltration

/-!
# Naturality of the image filtration on total homology

Maps of first-quadrant bicomplexes induce canonical maps between the images
of finite-stage homology in total homology.  These maps are obtained from the
canonical image map of the corresponding commutative square.  The finite
image filtration is also canonically identified with the natural-index
restriction of the existing complete total-homology filtration.

Associated-graded and cokernel maps are deliberately deferred.
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

/-- The commutative square between finite-stage homology-to-total maps
induced by a bicomplex map. -/
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

/-- The map between finite-stage homology images induced by a bicomplex
map. -/
noncomputable def horizontalFiniteHomologyImageMapOfBicomplex
    (f : K ⟶ L) (n i : ℕ) :
    image (HomologicalComplex.homologyMap
      (horizontalFilteredTotalComplexToTotal K i) n) ⟶
      image (HomologicalComplex.homologyMap
        (horizontalFilteredTotalComplexToTotal L i) n) :=
  image.map (horizontalFiniteHomologyToTotalSquareOfBicomplex f n i)

/-- The image map commutes with the monic inclusions into total homology. -/
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

/-- Finite-stage homology maps, as a diagram over total homology. -/
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

/-- The finite image filtration on total homology. -/
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

/-- Restriction of the complete homology-over diagram to natural indices. -/
noncomputable def horizontalCompleteHomologyNatRestrictionOverDiagram
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (n : ℕ) :
    ℕ ⥤ Over ((K.total (ComplexShape.down ℕ)).homology n) :=
  horizontalFiltrationNatToEIntFunctor ⋙
    horizontalCompleteHomologyOverDiagram K n

/-- Before taking images, the restricted complete homology arrows are
naturally isomorphic over total homology to the finite homology arrows. -/
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

/-- After taking canonical images, the restricted complete homology
filtration and the finite homology filtration are naturally isomorphic as
`MonoOver`-valued diagrams. -/
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

/-- The natural-index restriction of the existing complete total-homology
filtration diagram is naturally isomorphic to the finite homology-image
filtration diagram. -/
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

/-- The complete/finite image comparison preserves the monic inclusions
into total homology. -/
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
