/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

import MathlibExt.CategoryTheory.Enriched.Limits.WeightedCoendTransport
import MathlibExt.CategoryTheory.Enriched.Limits.WeightedCoendIso
import MathlibExt.CategoryTheory.Enriched.Limits.WeightedCoendMapped

/-!
# Braided public weighted-coend transport clients

The weights and diagrams are arbitrary and the index categories remain plain.
There is no symmetric or separator instance. Mapped presentations retain an
independent ordinary target category and its object and Hom universes.
-/

set_option autoImplicit false
noncomputable section

universe uV vV uA uB uD vD
open CategoryTheory MonoidalCategory Limits Opposite
open scoped MonoidalClosed

namespace CategoryTheory.Enriched.WeightedCoendBraidedClients

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]

section IndexTransport

variable {B : Type uB} [EnrichedCategory V B]
  (T : EnrichedFunctor V A B)
  (W : EnrichedFunctor V Aᵒᵖ V) (W' : EnrichedFunctor V Bᵒᵖ V)
  (Q : EnrichedFunctor V A V) (Q' : EnrichedFunctor V B V)
  (w : ∀ a, W.obj (op a) ⟶ W'.obj (op (T.obj a)))
  (q : ∀ a, Q.obj a ⟶ Q'.obj (T.obj a))
  (hW : ∀ a b,
    MonoidalClosed.uncurry (W.map (op b) (op a)) ≫ w a =
      (w b ⊗ₘ T.map a b) ≫ MonoidalClosed.uncurry (W'.map (op (T.obj b)) (op (T.obj a))))
  (hQ : ∀ a b,
    MonoidalClosed.uncurry (Q.map a b) ≫ q b =
      (q a ⊗ₘ T.map a b) ≫ MonoidalClosed.uncurry (Q'.map (T.obj a) (T.obj b)))

include hW in
theorem weight_face (a b : A) :
    weightedCoend.face0 W Q a b ≫ weightedCoend.Transport.objectMap T W W' Q Q' w q a =
      weightedCoend.Transport.relationMap T W W' Q Q' w q a b ≫
        weightedCoend.face0 W' Q' (T.obj a) (T.obj b) :=
  weightedCoend.Transport.face0 T W W' Q Q' w q hW a b

include hQ in
theorem diagram_face (a b : A) :
    weightedCoend.face1 W Q a b ≫ weightedCoend.Transport.objectMap T W W' Q Q' w q b =
      weightedCoend.Transport.relationMap T W W' Q Q' w q a b ≫
        weightedCoend.face1 W' Q' (T.obj a) (T.obj b) :=
  weightedCoend.Transport.face1 T W W' Q Q' w q hQ a b

theorem generator (a : A)
    [HasCoproduct (weightedCoend.objects W Q)]
    [HasCoproduct (weightedCoend.relations W Q)]
    [HasCoequalizer (weightedCoend.leftMap W Q) (weightedCoend.rightMap W Q)]
    [HasCoproduct (weightedCoend.objects W' Q')]
    [HasCoproduct (weightedCoend.relations W' Q')]
    [HasCoequalizer (weightedCoend.leftMap W' Q') (weightedCoend.rightMap W' Q')] :
    weightedCoend.ι W Q a ≫ weightedCoend.Transport.map T W W' Q Q' w q hW hQ =
      (w a ⊗ₘ q a) ≫ weightedCoend.ι W' Q' (T.obj a) := by
  fail_if_success haveI : SymmetricCategory V := inferInstance
  exact weightedCoend.Transport.ι_map T W W' Q Q' w q hW hQ a

end IndexTransport

section ComponentIsomorphisms

variable (W W' : EnrichedFunctor V Aᵒᵖ V) (Q Q' : EnrichedFunctor V A V)
  (eW : ∀ a, W.obj (op a) ≅ W'.obj (op a))
  (eQ : ∀ a, Q.obj a ≅ Q'.obj a)
  (hW : ∀ a b,
    MonoidalClosed.uncurry (W.map (op b) (op a)) ≫ (eW a).hom =
      ((eW b).hom ⊗ₘ 𝟙 (a ⟶[V] b)) ≫
        MonoidalClosed.uncurry (W'.map (op b) (op a)))
  (hQ : ∀ a b,
    MonoidalClosed.uncurry (Q.map a b) ≫ (eQ b).hom =
      ((eQ a).hom ⊗ₘ 𝟙 (a ⟶[V] b)) ≫ MonoidalClosed.uncurry (Q'.map a b))
  [HasCoproduct (weightedCoend.objects W Q)]
  [HasCoproduct (weightedCoend.relations W Q)]
  [HasCoequalizer (weightedCoend.leftMap W Q) (weightedCoend.rightMap W Q)]
  [HasCoproduct (weightedCoend.objects W' Q')]
  [HasCoproduct (weightedCoend.relations W' Q')]
  [HasCoequalizer (weightedCoend.leftMap W' Q') (weightedCoend.rightMap W' Q')]

theorem forward_generator (a : A) :
    weightedCoend.ι W Q a ≫
        (weightedCoend.ComponentIso.iso W W' Q Q' eW eQ hW hQ).hom =
      ((eW a).hom ⊗ₘ (eQ a).hom) ≫ weightedCoend.ι W' Q' a := by
  fail_if_success haveI : SymmetricCategory V := inferInstance
  exact weightedCoend.ComponentIso.ι_iso_hom W W' Q Q' eW eQ hW hQ a

theorem inverse_generator (a : A) :
    weightedCoend.ι W' Q' a ≫
        (weightedCoend.ComponentIso.iso W W' Q Q' eW eQ hW hQ).inv =
      ((eW a).inv ⊗ₘ (eQ a).inv) ≫ weightedCoend.ι W Q a :=
  weightedCoend.ComponentIso.ι_iso_inv W W' Q Q' eW eQ hW hQ a

theorem forward_inverse :
    (weightedCoend.ComponentIso.iso W W' Q Q' eW eQ hW hQ).hom ≫
        (weightedCoend.ComponentIso.iso W W' Q Q' eW eQ hW hQ).inv =
      𝟙 (Enriched.weightedCoend W Q) :=
  (weightedCoend.ComponentIso.iso W W' Q Q' eW eQ hW hQ).hom_inv_id

theorem inverse_forward :
    (weightedCoend.ComponentIso.iso W W' Q Q' eW eQ hW hQ).inv ≫
        (weightedCoend.ComponentIso.iso W W' Q Q' eW eQ hW hQ).hom =
      𝟙 (Enriched.weightedCoend W' Q') :=
  (weightedCoend.ComponentIso.iso W W' Q Q' eW eQ hW hQ).inv_hom_id

end ComponentIsomorphisms

section MappedPresentation

variable {D : Type uD} [Category.{vD} D]
  (W : EnrichedFunctor V Aᵒᵖ V) (F : EnrichedFunctor V A V) (J : V ⥤ D)
  [HasCoproduct (weightedCoend.objects W F)]
  [HasCoproduct (weightedCoend.relations W F)]
  [HasCoequalizer (weightedCoend.leftMap W F) (weightedCoend.rightMap W F)]

theorem projected_naturality (J1 J2 : V ⥤ D) (η : J1 ⟶ J2) (a b : A) :
    J1.map (weightedCoend.face0 W F a b) ≫ η.app (weightedCoend.objects W F a) ≫
        J2.map (weightedCoend.ι W F a) =
      J1.map (weightedCoend.face1 W F a b) ≫ η.app (weightedCoend.objects W F b) ≫
        J2.map (weightedCoend.ι W F b) :=
  weightedCoend.Mapped.projectedFacesNaturality W F J1 J2 η a b

variable [HasCoproduct (weightedCoend.Mapped.mappedObjects W F J)]
  [HasCoproduct (weightedCoend.Mapped.mappedRelations W F J)]
  [PreservesColimit (Discrete.functor (weightedCoend.objects W F)) J]
  [PreservesColimit (Discrete.functor (weightedCoend.relations W F)) J]
  [PreservesColimit
    (parallelPair (weightedCoend.leftMap W F) (weightedCoend.rightMap W F)) J]
  [HasCoequalizer (weightedCoend.Mapped.mappedLeftMap W F J)
    (weightedCoend.Mapped.mappedRightMap W F J)]

theorem mapped_generator (a : A) :
    (Sigma.ι (weightedCoend.Mapped.mappedObjects W F J) a ≫
      coequalizer.π (weightedCoend.Mapped.mappedLeftMap W F J)
        (weightedCoend.Mapped.mappedRightMap W F J)) ≫
          (weightedCoend.Mapped.mappedQuotientIso W F J).hom =
      J.map (weightedCoend.ι W F a) := by
  fail_if_success haveI : SymmetricCategory V := inferInstance
  exact weightedCoend.Mapped.mappedQuotientIso_generator W F J a

end MappedPresentation

end CategoryTheory.Enriched.WeightedCoendBraidedClients
