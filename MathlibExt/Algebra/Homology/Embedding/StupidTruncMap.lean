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

@[expose] public section

open CategoryTheory Category Limits ZeroObject

namespace HomologicalComplex

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Components of `stupidTruncMap` on image degrees. -/
lemma stupidTruncMap_f_eq {K L : HomologicalComplex C c'}
    {emb : c.Embedding c'} [emb.IsRelIff]
    (φ : K ⟶ L) {i : ι} {q : ι'} (hi : emb.f i = q) :
    (stupidTruncMap φ emb).f q =
      (K.stupidTruncXIso emb hi).hom ≫ φ.f q ≫ (L.stupidTruncXIso emb hi).inv := by
  apply (cancel_mono (L.stupidTruncXIso emb hi).hom).1
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
    stupidTruncMap_stupidTruncXIso_hom φ emb hi

/-- Components of `stupidTruncMap` off image degrees vanish. -/
lemma stupidTruncMap_f_eq_zero {K L : HomologicalComplex C c'}
    {emb : c.Embedding c'} [emb.IsRelIff]
    (φ : K ⟶ L) {q : ι'} (hq : ∀ i, emb.f i ≠ q) :
    (stupidTruncMap φ emb).f q = 0 := by
  unfold stupidTruncMap
  exact extendMap_f_eq_zero _ emb q hq

end HomologicalComplex

end
