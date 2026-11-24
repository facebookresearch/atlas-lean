/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

import MathlibExt.Algebra.Category.FGProjectiveCat.IdempotentImage

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe u v

variable {R : Type u} [CommRing R] {e : R}

-- Ring and module worlds remain independent in the actual image and decomposition.
example (he : IsIdempotentElem e) (P : FGProjectiveCat.{v} R) :
    P ≅ FGProjectiveCat.idempotentImage he P ⊞
      FGProjectiveCat.idempotentImage he.one_sub P :=
  FGProjectiveCat.idempotentDecompositionIso he P

example (he : IsIdempotentElem e) (P : FGProjectiveCat.{v} R)
    (x : FGProjectiveCat.idempotentImage he P) : e • x.val = x.val :=
  FGProjectiveCat.idempotentImage_fixed he P x

example (P : FGProjectiveCat.{v} R) :
    P ≅ FGProjectiveCat.idempotentImage (IsIdempotentElem.zero : IsIdempotentElem (0 : R)) P ⊞
      FGProjectiveCat.idempotentImage IsIdempotentElem.zero.one_sub P :=
  FGProjectiveCat.idempotentDecompositionIso IsIdempotentElem.zero P

-- The quotient kills the whole original scalar-extension object in either support factor.
example (he : IsIdempotentElem e) (P : FGProjectiveCat.{v} R) :
    IsZero ((FGProjectiveCat.baseChange (Ideal.Quotient.mk (Ideal.span {e}))).obj
      (FGProjectiveCat.idempotentImage he P)) :=
  FGProjectiveCat.idempotentImage_quotient_isZero he P

example (he : IsIdempotentElem e) (P : FGProjectiveCat.{v} R) :
    (FGProjectiveCat.baseChange (Ideal.Quotient.mk (Ideal.span {1 - e}))).obj
        (FGProjectiveCat.idempotentImage he.one_sub P) ≅
      (0 : FGProjectiveCat.{max u v} (R ⧸ Ideal.span {1 - e})) :=
  FGProjectiveCat.idempotentImageQuotientIsoZero he.one_sub P

#print axioms FGProjectiveCat.idempotentImage
#print axioms FGProjectiveCat.idempotentDecompositionIso
#print axioms FGProjectiveCat.idempotentImage_quotient_isZero
#print axioms FGProjectiveCat.idempotentImageQuotientIsoZero
