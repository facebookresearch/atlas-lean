/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.Algebra.Category.FGProjectiveCat.Prod

/-!
# Tests for finite projective modules over product rings
-/

@[expose] public section

open CategoryTheory Limits

universe u

noncomputable section

namespace FGProjectiveCatProdTests

variable {R S : Type u} [Ring R] [Ring S]

example :
    FGProjectiveCat.{u} (R × S) ⥤ FGProjectiveCat.{u} R :=
  ProdIdempotent.eComponentFunctorFGP (R := R) (S := S)

example :
    FGProjectiveCat.{u} (R × S) ⥤ FGProjectiveCat.{u} S :=
  ProdIdempotent.fComponentFunctorFGP (R := R) (S := S)

example :
    FGProjectiveCat.{u} R ⥤ FGProjectiveCat.{u} (R × S) :=
  FGProjectiveCat.prodEmbeddingFst (R := R) (S := S)

example :
    FGProjectiveCat.{u} S ⥤ FGProjectiveCat.{u} (R × S) :=
  FGProjectiveCat.prodEmbeddingSnd (R := R) (S := S)

example :
    (ProdIdempotent.eComponentFunctorFGP (R := R) (S := S)).IsExact :=
  inferInstance

example :
    (FGProjectiveCat.prodEmbeddingSnd (R := R) (S := S)).IsExact :=
  inferInstance

example (X : FGProjectiveCat.{u} (R × S)) :
    X ≅
      ((FGProjectiveCat.prodEmbeddingFst (R := R) (S := S)).obj
          ((ProdIdempotent.eComponentFunctorFGP (R := R) (S := S)).obj X) ⊞
        (FGProjectiveCat.prodEmbeddingSnd (R := R) (S := S)).obj
          ((ProdIdempotent.fComponentFunctorFGP (R := R) (S := S)).obj X)) :=
  FGProjectiveCat.Prod.decompositionIso X

-- A zero-ring factor is covered by the same arbitrary-ring construction.
example (X : FGProjectiveCat.{u} (R × PUnit)) :
    X ≅
      ((FGProjectiveCat.prodEmbeddingFst (R := R) (S := PUnit)).obj
          ((ProdIdempotent.eComponentFunctorFGP (R := R) (S := PUnit)).obj X) ⊞
        (FGProjectiveCat.prodEmbeddingSnd (R := R) (S := PUnit)).obj
          ((ProdIdempotent.fComponentFunctorFGP (R := R) (S := PUnit)).obj X)) :=
  FGProjectiveCat.Prod.decompositionIso X

section CommRing

variable {A B : Type u} [CommRing A] [CommRing B]

example :
    FGProjectiveCat.baseChange (RingHom.fst A B) ≅
      ProdIdempotent.eComponentFunctorFGP (R := A) (S := B) :=
  ProdIdempotent.baseChangeFstIsoEComponentFGP

example :
    FGProjectiveCat.baseChange (RingHom.snd A B) ≅
      ProdIdempotent.fComponentFunctorFGP (R := A) (S := B) :=
  ProdIdempotent.baseChangeSndIsoFComponentFGP

end CommRing

end FGProjectiveCatProdTests

end
