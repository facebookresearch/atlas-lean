/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- SOURCE-ONLY PROPOSAL. Native verification is UNEXECUTED.
module

public import MathlibExt.Algebra.Category.CommAlgCat.CotangentPushout
public import MathlibExt.Algebra.Category.CommAlgCat.ScalarExtensionAdjunction
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Cotangent pushout as the original-algebra specialization of the generic adjunction.{u, v, w}

All actual tensor and scalar-restriction maps come from the generic
CommAlgCat scalar API. Native equality of the original algebra with the
algebra induced by its structural map supplies the left-functor transport.
The hom correspondence and its naturality are the native adjunction's
correspondence. No second tensor functor, hom-equivalence implementation,
or supplied adjunction.{u, v, w} is introduced. The old public client names remain.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v w

namespace CommAlgCat.CotangentPushout

variable (k : Type u) (K : Type w) [CommRing k] [CommRing K] [Algebra k K]

/-- Actual ground restriction is the original structural-map specialization. -/
abbrev restrictionFunctor :
    CommAlgCat.{max u v w} K ⥤ CommAlgCat.{max u v w} k :=
  CommAlgCat.restrictScalars (algebraMap k K)

/-- The generic adjunction.{u, v, w} transported through the earned original-algebra equality. -/
abbrev adjunction : algebraFunctor.{u, v, w} k K ⊣ restrictionFunctor.{u, v, w} k K :=
  (CommAlgCat.extendRestrictScalarsAdj.{u, w, v} (algebraMap k K)).ofNatIsoLeft
    (eqToIso (CommAlgCat.extendScalars_algebraMap.{u, w, v} (R := k) (S := K)))

/-- The original hom correspondence is the one supplied by the generic native adjunction. -/
abbrev homEquiv (P : CommAlgCat.{max u v w} k) (Q : CommAlgCat.{max u v w} K) :
    ((algebraFunctor.{u, v, w} k K).obj P ⟶ Q) ≃ (P ⟶ (restrictionFunctor.{u, v, w} k K).obj Q) :=
  (adjunction.{u, v, w} k K).homEquiv P Q

/-- Source naturality is the existing native adjunction law. -/
theorem homEquiv_left_symm
    {P P' : CommAlgCat.{max u v w} k} {Q : CommAlgCat.{max u v w} K}
    (f : P' ⟶ P) (g : P ⟶ (restrictionFunctor.{u, v, w} k K).obj Q) :
    (homEquiv.{u, v, w} k K P' Q).symm (f ≫ g) =
      (algebraFunctor.{u, v, w} k K).map f ≫ (homEquiv.{u, v, w} k K P Q).symm g :=
  (adjunction.{u, v, w} k K).homEquiv_naturality_left_symm f g

/-- Target naturality is the existing native adjunction law. -/
theorem homEquiv_right
    {P : CommAlgCat.{max u v w} k} {Q Q' : CommAlgCat.{max u v w} K}
    (f : (algebraFunctor.{u, v, w} k K).obj P ⟶ Q) (g : Q ⟶ Q') :
    homEquiv.{u, v, w} k K P Q' (f ≫ g) =
      homEquiv.{u, v, w} k K P Q f ≫ (restrictionFunctor.{u, v, w} k K).map g :=
  (adjunction.{u, v, w} k K).homEquiv_naturality_right f g

instance algebraFunctor_isLeftAdjoint : (algebraFunctor.{u, v, w} k K).IsLeftAdjoint :=
  (adjunction.{u, v, w} k K).isLeftAdjoint

end CommAlgCat.CotangentPushout

end
