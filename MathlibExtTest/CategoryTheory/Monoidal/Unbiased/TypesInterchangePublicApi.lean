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

public import MathlibExt.CategoryTheory.Monoidal.Unbiased.Types

/-!
# `Type`-model flatten-iso interchange — public contract

Compile-time clients for the two pointwise interchange rewrites pushing
nested reindexing family maps through `flattenIso.hom` / `.inv`.
-/

@[expose] public section

open CategoryTheory

namespace MathlibExtTest.CategoryTheory.Monoidal.Unbiased.TypesInterchangePublicApi

universe w

noncomputable section

-- Interchange, hom direction: nested reindexing through `flattenIso.hom`.
example
    {X Y : FiniteFamily (FiniteFamily (Type w))} (f : X ⟶ Y)
    (t : FiniteFamily.typeTensorObj (FiniteFamily.flatten.obj X))
    (a : X.index) (b : (X.obj a).index) :
    (FiniteTensor.flattenIso (V := Type w)).hom.app Y
        (FiniteFamily.typeTensorMap (FiniteFamily.flatten.map f) t)
        (f.equiv a) ((f.hom a).equiv b)
      = (f.hom a).hom b
        ((FiniteTensor.flattenIso (V := Type w)).hom.app X t a b) :=
  FiniteFamily.typeTensorMap_flattenIso_hom_interchange f t a b

-- Interchange, inv direction: nested reindexing through `flattenIso.inv`.
example
    {X Y : FiniteFamily (FiniteFamily (Type w))} (f : X ⟶ Y)
    (s : FiniteFamily.typeTensorObj
      ((FiniteFamily.map FiniteFamily.typeTensor).obj X))
    (a : X.index) (b : (X.obj a).index) :
    (FiniteTensor.flattenIso (V := Type w)).inv.app Y
        (FiniteFamily.typeTensorMap
          ((FiniteFamily.map FiniteFamily.typeTensor).map f) s)
        ((FiniteFamily.flatten.map f).equiv ⟨a, b⟩)
      = (f.hom a).hom b
        ((FiniteTensor.flattenIso (V := Type w)).inv.app X s
          ⟨a, b⟩) :=
  FiniteFamily.typeTensorMap_flattenIso_inv_interchange f s a b

end

end MathlibExtTest.CategoryTheory.Monoidal.Unbiased.TypesInterchangePublicApi
