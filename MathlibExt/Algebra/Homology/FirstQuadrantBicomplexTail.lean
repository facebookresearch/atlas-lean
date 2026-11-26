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
/-!
# Bicomplex lift of the inner tail-cutoff sequence

Let C be an abelian category and K a bicomplex with both shapes up′(1) on ℕ. The inner tail
beginning at r retains the inner cochain degrees at least r. Its quotient by the inner tail
beginning at r+1 is the cutoff layer supported in inner degree r.

Evaluation at inner degree r followed by the single-degree complex functor defines the
cutoff-layer functor. Applying it to each outer cochain term gives the cutoff-layer bicomplex.
The tail quotient lifts naturally in the outer direction, and tail(r+1)→tail r→cutoff r is short
exact after every outer-degree evaluation, hence short exact as a bicomplex sequence. The outer
index is retained throughout; this is an inner-degree cutoff.
-/

@[expose] public section

open CategoryTheory

namespace FirstQuadrantTail

variable {C : Type*} [Category C] [Abelian C]

/-- Let C be an abelian category in arbitrary universes. All inner and outer complexes have the
cochain shape up′(1) on ℕ. For r : ℕ, cutoffLayerFunctor evaluates an inner complex at degree r
and places that object in a cochain complex supported only in degree r. On a map φ it uses φ.f r
in that single degree. -/
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

/-- Let C be an abelian category in arbitrary universes. All inner and outer complexes have the
cochain shape up′(1) on ℕ. For an inner cochain complex K and r : ℕ, (cutoffLayerFunctor r).obj
K equals cutoffLayer r K, with K.X r in degree r and zero elsewhere. -/
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

/-- Let C be an abelian category in arbitrary universes. All inner and outer complexes have the
cochain shape up′(1) on ℕ. For r : ℕ, the maps tailQuotient K r form a natural transformation
from innerTail r to cutoffLayerFunctor r. They retain the degree-r layer and kill all other
target degrees. -/
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

/-- Let C be an abelian category in arbitrary universes. All inner and outer complexes have the
cochain shape up′(1) on ℕ. Apply cutoffLayerFunctor r to every outer cochain term. The resulting
bicomplex endofunctor retains inner degree r in every outer degree, with the outer differential
induced by the degree-r components. -/
noncomputable def outerCutoffFunctor (r : ℕ) :
    HomologicalComplex₂ C (ComplexShape.up' (1 : ℕ)) (ComplexShape.up' (1 : ℕ)) ⥤
      HomologicalComplex₂ C (ComplexShape.up' (1 : ℕ))
        (ComplexShape.up' (1 : ℕ)) :=
  (cutoffLayerFunctor (C := C) r).mapHomologicalComplex (ComplexShape.up' (1 : ℕ))

/-- Let C be an abelian category in arbitrary universes. All inner and outer complexes have the
cochain shape up′(1) on ℕ. For a bicomplex K and r : ℕ, outerCutoff K r is obtained by replacing
each inner complex K.X p by its degree-r cutoff layer, while retaining the outer cochain
indexing. -/
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

/-- Let C be an abelian category in arbitrary universes. All inner and outer complexes have the
cochain shape up′(1) on ℕ. The inner tail quotient natural transformation lifts to a bicomplex
natural transformation from the bicomplex of tails starting at r to outerCutoffFunctor r. Its
outer-degree-p component is tailQuotient(K.X p,r). -/
noncomputable def bicomplexQuotient (r : ℕ) :
    (innerTail (C := C) r).mapHomologicalComplex (ComplexShape.up' (1 : ℕ)) ⟶
      outerCutoffFunctor (C := C) r :=
  NatTrans.mapHomologicalComplex (tailQuotientNatTrans (C := C) r)
    (ComplexShape.up' (1 : ℕ))

/-- Let C be an abelian category in arbitrary universes. All inner and outer complexes have the
cochain shape up′(1) on ℕ. For K and r : ℕ, quotientBicomplexMap K r maps the bicomplex whose
outer terms are innerTail r(K.X p) to outerCutoff K r, by the inner tail quotient in every outer
degree. -/
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

/-- Let C be an abelian category in arbitrary universes. All inner and outer complexes have the
cochain shape up′(1) on ℕ. For a bicomplex K and r : ℕ, tailInclusion:tail(r+1)→tail r followed
by quotientBicomplexMap:tail r→cutoff r is the zero bicomplex map. -/
lemma bicomplexTailCut_zero
    (K : HomologicalComplex₂ C (ComplexShape.up' (1 : ℕ))
      (ComplexShape.up' (1 : ℕ))) (r : ℕ) :
    tailInclusion (C := C) K r ≫ quotientBicomplexMap (C := C) K r = 0 := by
  refine HomologicalComplex.hom_ext _ _ fun p => ?_
  simp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f,
    tailInclusion_f, quotientBicomplexMap_f]
  exact tailCut_zero (C := C) (K.X p) r

/-- Let C be an abelian category in arbitrary universes. All inner and outer complexes have the
cochain shape up′(1) on ℕ. For K and r : ℕ, bicomplexTailCutShort is the short complex
tail(r+1)→tail r→cutoff r, with first arrow tailInclusion and second arrow quotientBicomplexMap. -/
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

/-- Let C be an abelian category in arbitrary universes. All inner and outer complexes have the
cochain shape up′(1) on ℕ. Evaluating bicomplexTailCutShort K r at outer degree p gives
tailCutShort(K.X p,r), the inner short complex tail(r+1)(K.X p)→tail r(K.X p)→cutoff r(K.X p). -/
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

/-- Let C be an abelian category in arbitrary universes. All inner and outer complexes have the
cochain shape up′(1) on ℕ. For any bicomplex K and r : ℕ, tail(r+1)→tail r→cutoff r is short
exact. In every outer degree p it is the short exact inner tail-cutoff sequence of K.X p. -/
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
