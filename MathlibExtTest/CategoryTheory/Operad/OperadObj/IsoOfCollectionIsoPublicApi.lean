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

public import MathlibExt.CategoryTheory.Operad.OperadObj.Hom

/-!
# Lifting collection isomorphisms to operads — public contract

Compile-time clients for constructing an operad isomorphism from a collection isomorphism and
only the forward unit and substitution compatibility laws.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Operad

namespace MathlibExtTest.CategoryTheory.Operad.OperadObj.IsoOfCollectionIsoPublicApi

universe uV vV

variable {V : Type uV} [Category.{vV} V] [FiniteTensor V]

example {O P : OperadObj V} (e : O.toCollection ≅ P.toCollection)
    (mapUnit : O.unit ≫ e.hom.app ⟨arityOne⟩ = P.unit)
    (mapSubst : ∀ X,
      O.subst.app X ≫ e.hom.app ⟨substitutionTotalObj X⟩ =
        OperadObj.HomData.sourceHom e.hom X ≫ P.subst.app X) : O ≅ P :=
  OperadObj.isoOfCollectionIso e mapUnit mapSubst

example {O P : OperadObj V} (e : O.toCollection ≅ P.toCollection)
    (mapUnit : O.unit ≫ e.hom.app ⟨arityOne⟩ = P.unit)
    (mapSubst : ∀ X,
      O.subst.app X ≫ e.hom.app ⟨substitutionTotalObj X⟩ =
        OperadObj.HomData.sourceHom e.hom X ≫ P.subst.app X) :
    (OperadObj.isoOfCollectionIso e mapUnit mapSubst).hom.toCollectionHom = e.hom :=
  OperadObj.isoOfCollectionIso_hom_toCollectionHom e mapUnit mapSubst

example {O P : OperadObj V} (e : O.toCollection ≅ P.toCollection)
    (mapUnit : O.unit ≫ e.hom.app ⟨arityOne⟩ = P.unit)
    (mapSubst : ∀ X,
      O.subst.app X ≫ e.hom.app ⟨substitutionTotalObj X⟩ =
        OperadObj.HomData.sourceHom e.hom X ≫ P.subst.app X) :
    (OperadObj.isoOfCollectionIso e mapUnit mapSubst).inv.toCollectionHom = e.inv :=
  OperadObj.isoOfCollectionIso_inv_toCollectionHom e mapUnit mapSubst

end MathlibExtTest.CategoryTheory.Operad.OperadObj.IsoOfCollectionIsoPublicApi
