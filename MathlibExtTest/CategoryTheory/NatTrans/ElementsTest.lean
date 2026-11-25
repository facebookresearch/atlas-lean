/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.NatTrans.Elements

/-!
# Tests for element equivalences induced by natural isomorphisms
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe u v w

open CategoryTheory

namespace CategoryTheory.Functor.ElementsTest

variable {C : Type u} [Category.{v} C] {F G : C ⥤ Type w}
  (i : F ≅ G)

example (z : F.Elements) :
    (Functor.Elements.equivOfIso i).symm
        (Functor.Elements.equivOfIso i z) = z :=
  (Functor.Elements.equivOfIso i).symm_apply_apply z

example (z : G.Elements) :
    Functor.Elements.equivOfIso i
        ((Functor.Elements.equivOfIso i).symm z) = z :=
  (Functor.Elements.equivOfIso i).apply_symm_apply z

example (z : F.Elements) :
    (Functor.Elements.equivOfIso i z).obj = z.obj :=
  Functor.Elements.equivOfIso_apply_obj i z

example (z : G.Elements) :
    ((Functor.Elements.equivOfIso i).symm z).obj = z.obj :=
  Functor.Elements.equivOfIso_symm_apply_obj i z

end CategoryTheory.Functor.ElementsTest
