/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Waldhausen.K0.Basic
public import MathlibExt.CategoryTheory.Waldhausen.CofiberCobaseChange

/-!
# The original native K-zero relation for a cofibration pushout

The original quotient of the given cofibration is also the quotient of its
actual cobase change. The same original pushout descent retains both leg
equations. Both original cofiber rows then give the K-zero relation in the
given nonadditive Waldhausen category.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe u v

namespace WaldhausenKTheory.K0

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [WaldhausenCategory C]

export CategoryTheory (exists_common_cofiber_of_isPushout)

/-- The actual original cofibration pushout gives the full native K-zero relation. -/
theorem mk_add_mk_eq_of_isPushout
    {X Y Z P : C} {i : X ⟶ Y} {f : X ⟶ Z} {inY : Y ⟶ P} {inZ : Z ⟶ P}
    (hP : IsPushout i f inY inZ) (hi : IsCofibration i) :
    (K0.mk P : K0 C) + K0.mk X = K0.mk Y + K0.mk Z := by
  obtain ⟨Q, _, _, _, qY, qP, _, _, _, _, hY, hP⟩ :=
    CategoryTheory.exists_common_cofiber_of_isPushout hP hi
  have hYValue := K0.mk_eq_of_cofibrationSequence hY
  have hPValue := K0.mk_eq_of_cofibrationSequence hP
  exact (congrArg (fun x : K0 C => x + K0.mk X) hPValue).trans
    ((by simp only [add_comm, add_left_comm] :
      (K0.mk Z + K0.mk Q) + K0.mk X = (K0.mk X + K0.mk Q) + K0.mk Z).trans
        (congrArg (fun x : K0 C => x + K0.mk Z) hYValue.symm))

end WaldhausenKTheory.K0

end
