/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

import MathlibExt.CategoryTheory.Enriched.GradedYoneda

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped MonoidalClosed

set_option autoImplicit false

noncomputable section

universe uC uV vV

namespace MathlibExtTest.GradedYonedaTests

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {C : Type uC} [EnrichedCategory V C]
  (i : C) (F : EnrichedFunctor V C V)

-- A plain enriched index and one actual value suffice to construct the whole morphism.
example (e : 𝟙_ V ⟶ F.obj i) :
    GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) (GradedYoneda.representable i) F :=
  GradedYoneda.extend i F e

-- Its whole enriched hom naturality is available to a consumer.
example (e : 𝟙_ V ⟶ F.obj i) (x y : C) :
    MonoidalClosed.uncurry ((GradedYoneda.representable (V := V) i).map x y) ≫
        (eHomEquiv V).symm ((GradedYoneda.extend i F e).app y) =
      ((eHomEquiv V).symm ((GradedYoneda.extend i F e).app x) ⊗ₘ 𝟙 (x ⟶[V] y)) ≫
        MonoidalClosed.uncurry (F.map x y) :=
  (GradedYoneda.extend i F e).uncurriedNaturality x y

-- The bijection recovers a supplied value and a supplied genuine transformation.
example (e : 𝟙_ V ⟶ F.obj i) :
    GradedYoneda.equiv i F ((GradedYoneda.equiv i F).symm e) = e :=
  (GradedYoneda.equiv i F).apply_symm_apply e

example (t : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V))
    (GradedYoneda.representable i) F) :
    (GradedYoneda.equiv i F).symm (GradedYoneda.equiv i F t) = t :=
  (GradedYoneda.equiv i F).symm_apply_apply t

-- Values on the identity decide equality of actual full transformations.
example {s t : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V))
    (GradedYoneda.representable i) F}
    (h : eId V i ≫ (eHomEquiv V).symm (s.app i) =
      eId V i ≫ (eHomEquiv V).symm (t.app i)) : s = t :=
  GradedYoneda.hom_ext i F h

example {G : EnrichedFunctor V C V}
    (t : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) (GradedYoneda.representable i) F)
    (a : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F G) :
    GradedYoneda.equiv i G (GradedNatTrans.unitComp t a) =
      GradedYoneda.equiv i F t ≫ (eHomEquiv V).symm (a.app i) :=
  GradedYoneda.evaluate_comp i t a

end MathlibExtTest.GradedYonedaTests
