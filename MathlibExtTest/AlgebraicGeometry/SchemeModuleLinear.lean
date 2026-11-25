/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.SchemeModuleLinear

@[expose] public section

namespace MathlibExt.AlgebraicGeometry.SchemeModuleLinear

open CategoryTheory Opposite
open _root_.AlgebraicGeometry

universe u

variable (R : Type u) [CommRing R] (X : Over (Spec (.of R)))

-- The base scalars act on sections over `U` through the structure map, restricted to `U`.
example (U : X.left.Opensᵒᵖ) (r : R) :
    baseRingToSections R X U r =
      (X.left.ringCatSheaf.obj.map U.unop.leTop.op).hom
        ((forget₂ CommRingCat RingCat).map
          ((Scheme.ΓSpecIso (.of R)).inv ≫ X.hom.appTop) |>.hom r) :=
  rfl

-- With the canonical linear structure installed locally, `r • f` is `f` precomposed with
-- multiplication by the image of `r` on every open.
example (r : R) {M N : X.left.Modules} (f : M ⟶ N) (U : X.left.Opensᵒᵖ)
    (x : M.val.obj U) :
    letI := modulesLinear R X
    ((r • f).val.app U).hom x = (f.val.app U).hom (baseRingToSections R X U r • x) :=
  rfl

-- The scalar `1` acts as the identity and the action is multiplicative.
example : baseRingToCenter R X 1 = 1 := map_one _

example (r s : R) :
    baseRingToCenter R X (r * s) = baseRingToCenter R X r * baseRingToCenter R X s :=
  map_mul _ r s

end MathlibExt.AlgebraicGeometry.SchemeModuleLinear
