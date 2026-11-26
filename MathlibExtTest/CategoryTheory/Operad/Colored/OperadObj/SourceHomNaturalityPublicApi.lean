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

import MathlibExt.CategoryTheory.Operad.Colored.OperadObj.SourceHomNaturality

/-!
# `sourceHom`-naturality public-contract packet

Pins the naturality of `HomData.sourceHom` in the substitution datum,
plus its factorwise supporting lemma `HomData.factorHom_naturality`.
-/

open CategoryTheory
open CategoryTheory.Operad

universe u w v

variable {Color : Type u} {V : Type w} [Category.{v} V] [FiniteTensor V]

-- Factorwise naturality: reindexing factors along `f` commutes with `α`.
noncomputable example {O P : ColoredSymmetricCollection Color V}
    (α : O ⟶ P) {d e : ColoredSubstitutionData Color} (f : d ⟶ e) :
    (ColoredOperadObj.substitutionFactors O).map f ≫
      ColoredOperadObj.HomData.factorHom α e =
      ColoredOperadObj.HomData.factorHom α d ≫
        (ColoredOperadObj.substitutionFactors P).map f :=
  by exact ColoredOperadObj.HomData.factorHom_naturality α f

-- Tensor-level naturality of `sourceHom` in the substitution datum.
noncomputable example {O P : ColoredSymmetricCollection Color V}
    (α : O ⟶ P) {d e : ColoredSubstitutionData Color} (f : d ⟶ e) :
    (ColoredOperadObj.substitutionSource O).map f ≫
      ColoredOperadObj.HomData.sourceHom α e =
      ColoredOperadObj.HomData.sourceHom α d ≫
        (ColoredOperadObj.substitutionSource P).map f :=
  by exact ColoredOperadObj.HomData.sourceHom_naturality α f
