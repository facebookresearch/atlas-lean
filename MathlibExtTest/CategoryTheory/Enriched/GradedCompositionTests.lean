/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.GradedComposition

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uA uB uV vV

open CategoryTheory MonoidalCategory

namespace MathlibExtTest.GradedComposition
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  {A : Type uA} [EnrichedCategory V A]
  {B : Type uB} [EnrichedCategory V B]
  {F G H K : EnrichedFunctor V A B} {Z W T : Center V}

example (f : GradedNatTrans Z F G) (g : GradedNatTrans W G H) (a : A) :
    (GradedNatTrans.tensorComp f g).app a =
      (f.app a ⊗ₘ g.app a) ≫ eComp V (F.obj a) (G.obj a) (H.obj a) :=
  GradedNatTrans.tensorComp_app f g a

example (f : GradedNatTrans Z F G) (g : GradedNatTrans W G H) (a b : A) :
    ((Z ⊗ W).2.β (a ⟶[V] b)).hom ≫
        (F.map a b ⊗ₘ (GradedNatTrans.tensorComp f g).app b) ≫
        eComp V (F.obj a) (F.obj b) (H.obj b) =
      ((GradedNatTrans.tensorComp f g).app a ⊗ₘ H.map a b) ≫
        eComp V (F.obj a) (H.obj a) (H.obj b) :=
  (GradedNatTrans.tensorComp f g).naturality a b

example (f : GradedNatTrans Z F G) (g : GradedNatTrans W G H)
    (h : GradedNatTrans T H K) (a : A) :
    (GradedNatTrans.tensorComp (GradedNatTrans.tensorComp f g) h).app a =
      (((f.app a ⊗ₘ g.app a) ≫ eComp V (F.obj a) (G.obj a) (H.obj a)) ⊗ₘ
        h.app a) ≫ eComp V (F.obj a) (H.obj a) (K.obj a) := rfl

example {Z' : Center V} (u : Z ⟶ Z') (t : GradedNatTrans Z' F G) (a : A) :
    (GradedNatTrans.regrade u t).app a = u.f ≫ t.app a :=
  GradedNatTrans.regrade_app u t a

example {Z' : Center V} (u : Z ⟶ Z') (t : GradedNatTrans Z' F G) (a b : A) :
    (Z.2.β (a ⟶[V] b)).hom ≫
        (F.map a b ⊗ₘ (u.f ≫ t.app b)) ≫
        eComp V (F.obj a) (F.obj b) (G.obj b) =
      ((u.f ≫ t.app a) ⊗ₘ G.map a b) ≫
        eComp V (F.obj a) (G.obj a) (G.obj b) :=
  (GradedNatTrans.regrade u t).naturality a b

end MathlibExtTest.GradedComposition

#print axioms CategoryTheory.GradedNatTrans.tensorComp_naturality
#print axioms CategoryTheory.GradedNatTrans.tensorComp
#print axioms CategoryTheory.GradedNatTrans.tensorComp_app
#print axioms CategoryTheory.GradedNatTrans.regrade
#print axioms CategoryTheory.GradedNatTrans.regrade_app
