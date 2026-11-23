/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.Curve.GluedPic0

@[expose] public section

noncomputable section

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable (S : Finset (Place K F × Place K F))

-- `exactSource` consumers with the original binders.
example : ↥(GluingData.admissible S) →+ GluedPic0 K F S :=
  GluedPic0.mk S

example : Function.Surjective (GluedPic0.mk S) :=
  GluedPic0.mk_surjective S

example (x : ↥(GluingData.admissible S)) :
    GluedPic0.mk S x = 0 ↔ GluingData.IsGluedPrincipal S (x : GluingData K F S) :=
  GluedPic0.mk_eq_zero_iff S x

example (x : ↥(GluingData.admissible S)) :
    GluedPic0.toPic0Pair S (GluedPic0.mk S x) =
      (Pic0.mk ⟨(x : GluingData K F S).1, x.2.1⟩,
        Pic0.mk ⟨(x : GluingData K F S).2.1, x.2.2.1⟩) :=
  GluedPic0.toPic0Pair_mk S x

example (w : ↥S → Additive Kˣ) :
    GluedPic0.toPic0Pair S (GluedPic0.nodeUnit S w) = 0 :=
  GluedPic0.toPic0Pair_nodeUnit S w

-- Boundary: constant node units are glued principal, hence vanish.
example (c : Kˣ) : GluedPic0.nodeUnit S (fun _ => Additive.ofMul c) = 0 :=
  GluedPic0.nodeUnit_const S c

example (v : Place K F) : v.HasValue (1 : F) 1 :=
  v.hasValue_one

example (v : Place K F) (c : K) : v.HasValue (algebraMap K F c) c :=
  v.hasValue_algebraMap c

end AlgebraicCurve
