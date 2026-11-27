/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.ModelCategory.BrownLemma

/-!
# Brown's lemma for contravariant functors

A functor `F : Cᵒᵖ ⥤ D` between model categories sends weak equivalences
between cofibrant objects to weak equivalences if it sends every trivial
cofibration to a weak equivalence. The proof uses the cofibrant Brown
factorization and its section.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uC vC uD vD
open CategoryTheory HomotopicalAlgebra

namespace HomotopicalAlgebra

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {D : Type uD} [Category.{vD} D] [ModelCategory D]

/-- A functor `F : Cᵒᵖ ⥤ D` between model categories that sends the opposite of
every trivial cofibration of `C` to a weak equivalence sends the opposite of
every weak equivalence between cofibrant objects of `C` to a weak equivalence. -/
theorem sourceFunctor_weak_of_trivialCofibrations
    (F : Cᵒᵖ ⥤ D)
    (hF : ∀ {X Y : C} (i : X ⟶ Y) [Cofibration i] [WeakEquivalence i],
      WeakEquivalence (F.map i.op))
    {X Y : C} (p : X ⟶ Y) [WeakEquivalence p] [IsCofibrant X] [IsCofibrant Y] :
    WeakEquivalence (F.map p.op) := by
  let h : CofibrantBrownFactorization p := Classical.choice inferInstance
  let _ : WeakEquivalence (F.map h.i.op) := hF h.i
  let _ : WeakEquivalence (F.map h.s.op) := hF h.s
  have hps : h.p.op ≫ h.s.op = 𝟙 (Opposite.op Y) := congrArg Quiver.Hom.op h.s_p
  have hps' : F.map h.p.op ≫ F.map h.s.op = 𝟙 (F.obj (Opposite.op Y)) := by
    rw [← F.map_comp, hps, F.map_id]
  let _ : WeakEquivalence (F.map h.p.op) := weakEquivalence_of_postcomp_of_fac hps'
  have hfac : p.op = h.p.op ≫ h.i.op := congrArg Quiver.Hom.op h.fac.symm
  rw [hfac, F.map_comp]
  infer_instance

end HomotopicalAlgebra
