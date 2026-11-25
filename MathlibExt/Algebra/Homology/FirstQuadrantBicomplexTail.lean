/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
Copyright (c) 2026 @junekim623, Muse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @junekim623, Muse, @toskua

Bicomplex lift of the inner-tail cutoff short exact sequence.

Lifts the inner-tail short complex to first-quadrant bicomplexes and proves it
short exact degreewise.
-/

module

public import MathlibExt.Algebra.Homology.FirstQuadrantTailQuotient
@[expose] public section

open CategoryTheory

namespace FirstQuadrantTail

variable {C : Type*} [Category C] [Abelian C]

/-- The cutoff-layer endofunctor on inner complexes: project to degree `r`,
then include as a complex supported only in degree `r`.
Its object is definitionally `cutoffLayer r K`
(see `cutoffLayerFunctor_obj`). -/
noncomputable def cutoffLayerFunctor (r : ℕ) :
    HomologicalComplex C (ComplexShape.up' (1 : ℕ)) ⥤
      HomologicalComplex C (ComplexShape.up' (1 : ℕ)) :=
  HomologicalComplex.eval C (ComplexShape.up' (1 : ℕ)) r ⋙
    HomologicalComplex.single C (ComplexShape.up' (1 : ℕ)) r

instance cutoffLayerFunctor_preservesZeroMorphisms (r : ℕ) :
    (cutoffLayerFunctor (C := C) r).PreservesZeroMorphisms where
  map_zero X Y := by
    simp only [cutoffLayerFunctor]
    exact Functor.map_zero _ _ _

/-- The object of `cutoffLayerFunctor r` is definitionally `cutoffLayer r K`. -/
@[simp]
lemma cutoffLayerFunctor_obj (r : ℕ)
    (K : HomologicalComplex C (ComplexShape.up' (1 : ℕ))) :
    (cutoffLayerFunctor (C := C) r).obj K = cutoffLayer (C := C) r K :=
  rfl

@[simp]
lemma cutoffLayerFunctor_map (r : ℕ)
    {K L : HomologicalComplex C (ComplexShape.up' (1 : ℕ))} (φ : K ⟶ L) :
    (cutoffLayerFunctor (C := C) r).map φ =
      (HomologicalComplex.single C (ComplexShape.up' (1 : ℕ)) r).map (φ.f r) :=
  rfl

/-- The inner tail-quotient map as a natural transformation. -/
noncomputable def tailQuotientNatTrans (r : ℕ) :
    innerTail (C := C) r ⟶ cutoffLayerFunctor (C := C) r where
  app K := tailQuotient (C := C) K r
  naturality _ _ φ :=
    HomologicalComplex.hom_ext _ _ fun q =>
      tailQuotient_naturality (C := C) φ r q

@[simp]
lemma tailQuotientNatTrans_app (r : ℕ)
    (K : HomologicalComplex C (ComplexShape.up' (1 : ℕ))) :
    (tailQuotientNatTrans (C := C) r).app K = tailQuotient (C := C) K r :=
  rfl

/-- Outer cutoff-layer endofunctor on bicomplexes. -/
noncomputable def outerCutoffFunctor (r : ℕ) :
    HomologicalComplex₂ C (ComplexShape.up' (1 : ℕ)) (ComplexShape.up' (1 : ℕ)) ⥤
      HomologicalComplex₂ C (ComplexShape.up' (1 : ℕ))
        (ComplexShape.up' (1 : ℕ)) :=
  (cutoffLayerFunctor (C := C) r).mapHomologicalComplex (ComplexShape.up' (1 : ℕ))

/-- The outer cutoff-layer bicomplex associated to `K`. -/
noncomputable def outerCutoff
    (K : HomologicalComplex₂ C (ComplexShape.up' (1 : ℕ))
      (ComplexShape.up' (1 : ℕ))) (r : ℕ) :
    HomologicalComplex₂ C (ComplexShape.up' (1 : ℕ)) (ComplexShape.up' (1 : ℕ)) :=
  (outerCutoffFunctor (C := C) r).obj K

@[simp]
lemma outerCutoff_X
    (K : HomologicalComplex₂ C (ComplexShape.up' (1 : ℕ))
      (ComplexShape.up' (1 : ℕ))) (r p : ℕ) :
    (outerCutoff (C := C) K r).X p = cutoffLayer (C := C) r (K.X p) :=
  rfl

/-- Bicomplex-level quotient natural transformation. -/
noncomputable def bicomplexQuotient (r : ℕ) :
    (innerTail (C := C) r).mapHomologicalComplex (ComplexShape.up' (1 : ℕ)) ⟶
      outerCutoffFunctor (C := C) r :=
  NatTrans.mapHomologicalComplex (tailQuotientNatTrans (C := C) r)
    (ComplexShape.up' (1 : ℕ))

/-- Quotient map out of the tail bicomplex. -/
noncomputable def quotientBicomplexMap
    (K : HomologicalComplex₂ C (ComplexShape.up' (1 : ℕ))
      (ComplexShape.up' (1 : ℕ))) (r : ℕ) :
    ((innerTail (C := C) r).mapHomologicalComplex
      (ComplexShape.up' (1 : ℕ))).obj K ⟶
      (outerCutoffFunctor (C := C) r).obj K :=
  (bicomplexQuotient (C := C) r).app K

@[simp]
lemma quotientBicomplexMap_f
    (K : HomologicalComplex₂ C (ComplexShape.up' (1 : ℕ))
      (ComplexShape.up' (1 : ℕ))) (r p : ℕ) :
    (quotientBicomplexMap (C := C) K r).f p =
      tailQuotient (C := C) (K.X p) r :=
  rfl

@[simp]
lemma quotientBicomplexMap_f_f
    (K : HomologicalComplex₂ C (ComplexShape.up' (1 : ℕ))
      (ComplexShape.up' (1 : ℕ))) (r p q : ℕ) :
    ((quotientBicomplexMap (C := C) K r).f p).f q =
      quotientF (C := C) (K.X p) r q :=
  rfl

/-- The bicomplex tail inclusion followed by the quotient vanishes. -/
lemma bicomplexTailCut_zero
    (K : HomologicalComplex₂ C (ComplexShape.up' (1 : ℕ))
      (ComplexShape.up' (1 : ℕ))) (r : ℕ) :
    tailInclusion (C := C) K r ≫ quotientBicomplexMap (C := C) K r = 0 := by
  refine HomologicalComplex.hom_ext _ _ fun p => ?_
  simp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f,
    tailInclusion_f, quotientBicomplexMap_f]
  exact tailCut_zero (C := C) (K.X p) r

/-- The bicomplex short complex `tail (r + 1) ⟶ tail r ⟶ cutoff r`. -/
noncomputable def bicomplexTailCutShort
    (K : HomologicalComplex₂ C (ComplexShape.up' (1 : ℕ))
      (ComplexShape.up' (1 : ℕ))) (r : ℕ) :
    ShortComplex (HomologicalComplex₂ C (ComplexShape.up' (1 : ℕ))
      (ComplexShape.up' (1 : ℕ))) :=
  ShortComplex.mk (tailInclusion (C := C) K r)
    (quotientBicomplexMap (C := C) K r)
    (bicomplexTailCut_zero (C := C) K r)

@[simp]
lemma bicomplexTailCutShort_f
    (K : HomologicalComplex₂ C (ComplexShape.up' (1 : ℕ))
      (ComplexShape.up' (1 : ℕ))) (r : ℕ) :
    (bicomplexTailCutShort (C := C) K r).f = tailInclusion (C := C) K r :=
  rfl

@[simp]
lemma bicomplexTailCutShort_g
    (K : HomologicalComplex₂ C (ComplexShape.up' (1 : ℕ))
      (ComplexShape.up' (1 : ℕ))) (r : ℕ) :
    (bicomplexTailCutShort (C := C) K r).g =
      quotientBicomplexMap (C := C) K r :=
  rfl

/-- Degreewise, the bicomplex short complex is the production inner one. -/
@[simp]
lemma bicomplexTailCutShort_map_eval
    (K : HomologicalComplex₂ C (ComplexShape.up' (1 : ℕ))
      (ComplexShape.up' (1 : ℕ))) (r p : ℕ) :
    (bicomplexTailCutShort (C := C) K r).map
        (HomologicalComplex.eval
          (HomologicalComplex C (ComplexShape.up' (1 : ℕ)))
          (ComplexShape.up' (1 : ℕ)) p) =
      tailCutShort (C := C) (K.X p) r :=
  rfl

/-- The bicomplex tail-cutoff short complex is short exact. -/
theorem bicomplexTailCut_shortExact
    (K : HomologicalComplex₂ C (ComplexShape.up' (1 : ℕ))
      (ComplexShape.up' (1 : ℕ))) (r : ℕ) :
    (bicomplexTailCutShort (C := C) K r).ShortExact := by
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  intro p
  rw [bicomplexTailCutShort_map_eval]
  exact tailCut_shortExact (C := C) (K.X p) r

end FirstQuadrantTail

end
