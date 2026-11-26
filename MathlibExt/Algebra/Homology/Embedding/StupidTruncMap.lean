/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


/-
Author: @toskua
Copyright (c) 2026 @junekim623, Muse. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: @junekim623, Muse, @toskua

Component formulas for the generic stupid-truncation map.
-/

module

public import MathlibExt.Algebra.Homology.Embedding.StupidTruncInclusion

/-!
# Components of maps between stupid truncations

Stupid truncation restricts a complex to the image of a shape embedding
and extends by zero outside that image. Its induced maps agree with the
original degree maps through the canonical component identifications and
vanish at all omitted degrees.
-/

@[expose] public section

open CategoryTheory Category Limits ZeroObject

namespace HomologicalComplex

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Let C be a category with zero morphisms and a zero object. Let e:c→c' be a shape embedding
preserving and reflecting relations, and let φ:K→L be a morphism of c'-complexes. For a degree
q=e(i) in the image, let θ_K:(K.stupidTrunc e)_q≅K_q and θ_L:(L.stupidTrunc e)_q≅L_q be the
canonical component isomorphisms. The truncated map has component θ_K.hom ≫ φ_q ≫ θ_L.inv.
-/
lemma stupidTruncMap_f_eq {K L : HomologicalComplex C c'}
    {emb : c.Embedding c'} [emb.IsRelIff]
    (φ : K ⟶ L) {i : ι} {q : ι'} (hi : emb.f i = q) :
    (stupidTruncMap φ emb).f q =
      (K.stupidTruncXIso emb hi).hom ≫ φ.f q ≫ (L.stupidTruncXIso emb hi).inv := by
  apply (cancel_mono (L.stupidTruncXIso emb hi).hom).1
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
    stupidTruncMap_stupidTruncXIso_hom φ emb hi

/--
Let C be a category with zero morphisms and a zero object. Let e:c→c' be a shape embedding
preserving and reflecting relations, and let φ:K→L be a morphism of c'-complexes. At a degree
q outside the image of e, both truncated terms are zero objects and the induced component
(stupidTruncMap φ e).f q is the zero morphism.
-/
lemma stupidTruncMap_f_eq_zero {K L : HomologicalComplex C c'}
    {emb : c.Embedding c'} [emb.IsRelIff]
    (φ : K ⟶ L) {q : ι'} (hq : ∀ i, emb.f i ≠ q) :
    (stupidTruncMap φ emb).f q = 0 := by
  unfold stupidTruncMap
  exact extendMap_f_eq_zero _ emb q hq

end HomologicalComplex

end
