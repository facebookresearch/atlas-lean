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

public import MathlibExt.CategoryTheory.Operad.Colored.OperadObj.Hom

/-!
# Naturality of `sourceHom` in the substitution datum

For a collection morphism `α : O ⟶ P` and a substitution-datum map
`f : d ⟶ e`, the source comparison `HomData.sourceHom α` is natural in
the datum: pushing forward along `f` commutes with applying `α`. This
is `FiniteFamily.mapNatTrans` naturality at
`factorFamilyFunctor.map f`, pushed through `FiniteTensor.tensor`.
-/

@[expose] public section

namespace CategoryTheory.Operad

open CategoryTheory

universe w v u

namespace ColoredOperadObj

variable {Color : Type u} {V : Type w} [Category.{v} V] [FiniteTensor V]

namespace HomData

omit [FiniteTensor V] in
/-- Naturality of `factorHom` in the substitution datum: reindexing
factors along `f` commutes with applying `α` factorwise. -/
theorem factorHom_naturality {O P : ColoredSymmetricCollection Color V}
    (α : O ⟶ P) {d e : ColoredSubstitutionData Color} (f : d ⟶ e) :
    (substitutionFactors O).map f ≫ factorHom α e =
      factorHom α d ≫ (substitutionFactors P).map f :=
  (FiniteFamily.mapNatTrans α).naturality
    (ColoredSubstitutionData.factorFamilyFunctor.map f)

/-- Naturality of `sourceHom` in the substitution datum: the tensor of
the factorwise statement. -/
theorem sourceHom_naturality {O P : ColoredSymmetricCollection Color V}
    (α : O ⟶ P) {d e : ColoredSubstitutionData Color} (f : d ⟶ e) :
    (substitutionSource O).map f ≫ sourceHom α e =
      sourceHom α d ≫ (substitutionSource P).map f := by
  unfold sourceHom
  rw [substitutionSource_map, substitutionSource_map]
  have hT := congrArg (FiniteTensor.tensor (V := V)).map
    (factorHom_naturality α f)
  rw [(FiniteTensor.tensor (V := V)).map_comp,
    (FiniteTensor.tensor (V := V)).map_comp] at hT
  exact hT

end HomData

end ColoredOperadObj

end CategoryTheory.Operad
