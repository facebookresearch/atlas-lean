/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.FunEquivalenceYoneda

/-!
# Yoneda upgrade: tests

These tests exercise the public API of
`MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.FunEquivalenceYoneda`:
the swap isomorphism (§1), the probe `h`-equivalences (§2), the
Yoneda upgrade `SSet.categoricalEquivalences.functorEquivalence_of_mem`
(§3), and the core direction
`SSet.HasHoInverse.kanComplexW_core_map` (§4).
-/

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal

namespace FunEquivalenceYonedaTest

open CategoryTheory MonoidalCategory MonoidalClosed SSet

universe u

variable {X Y : SSet.{u}} {f : X ⟶ Y}

section Swap

variable (D C : SSet.{u})


example : (SSet.ihomSwap D Y C).hom ≫ (SSet.ihomSwap D Y C).inv = 𝟙 _ :=
  (SSet.ihomSwap D Y C).hom_inv_id

example (g : X ⟶ Y) :
    (ihom D).map ((pre g).app C) ≫ SSet.ihomSwapHom D X C =
      SSet.ihomSwapHom D Y C ≫ (pre g).app ((ihom D).obj C) :=
  SSet.ihomSwapHom_natural D C g

end Swap

section Probe

-- No quasicategory hypothesis on the probe `D` is needed.
variable (C D : SSet.{u}) [SSet.Quasicategory C]


example (hf : SSet.categoricalEquivalences f) :
    (SSet.hoFunctor.map ((ihom D).map ((pre f).app C))).toFunctor.IsEquivalence :=
  hf.isEquivalence_hoFun_probe C D

end Probe

section Upgrade

variable (C : SSet.{u}) [SSet.Quasicategory C]


example (hf : SSet.categoricalEquivalences f) :
    SSet.HasHoInverse ((pre f).app C) :=
  hf.functorEquivalence_of_mem C

end Upgrade

section Core

variable {A B : SSet.{u}} [SSet.Quasicategory A] [SSet.Quasicategory B]


example {F : A ⟶ B} (h : SSet.HasHoInverse F) :
    SSet.KanComplex.W (SSet.core.map F) :=
  h.kanComplexW_core_map

example {p q : A ⟶ A}
    (e : SSet.Edge (SSet.ihomVertexEquiv A A p) (SSet.ihomVertexEquiv A A q))
    (he : e.IsEquivalence) :
    Nonempty (SSet.Homotopy (SSet.core.map p) (SSet.core.map q)) :=
  SSet.homotopy_core_of_isEquivalence_edge e he

example (g : A ⟶ B) (h : B ⟶ A) :
    SSet.core.map (g ≫ h) = SSet.core.map g ≫ SSet.core.map h :=
  SSet.core.map_comp g h

end Core

section Chain

variable (C : SSet.{u}) [SSet.Quasicategory C]

/-- End-to-end: `f ∈ W` gives a weak homotopy equivalence on cores. -/
example (hf : SSet.categoricalEquivalences f) :
    SSet.KanComplex.W (SSet.core.map ((pre f).app C)) :=
  (hf.functorEquivalence_of_mem C).kanComplexW_core_map


end Chain

end FunEquivalenceYonedaTest

end MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal
