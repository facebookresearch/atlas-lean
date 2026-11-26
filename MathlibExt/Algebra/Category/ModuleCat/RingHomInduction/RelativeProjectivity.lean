/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Adjunction.RelativeProjectivity
public import MathlibExt.Algebra.Category.ModuleCat.RingHomInduction.Universes

/-!
# Relative projectivity of induced modules

The ULift of an induced carrier is projective relative to restriction of scalars. In the common
adjunction universe, the counit-splitting and retract-of-induced-object characterizations follow
from the relative projectivity theorem.
-/

@[expose] public section

open CategoryTheory
universe u v w

namespace ModuleCat.RingHomInduction

variable {k : Type u} {R : Type v} [Ring k] [Ring R] (φ : k →+* R)

/-- The ULift of an induced carrier has the full scalar-relative property. -/
theorem isRelativeProjective_original_induced (M : ModuleCat.{w} k) :
    (ModuleCat.restrictScalars.{max u v w} φ).IsRelativeProjective
      (ModuleCat.of R (ULift.{max u v} (Carrier φ M))) := by
  intro Y Z g s f
  let M' : ModuleCat.{max u v w} k := ModuleCat.of k (ULift.{max u v} M)
  let e : (ModuleCat.induceScalars.{u, v, w} φ).obj M' ≅
      ModuleCat.of R (ULift.{max u v} (Carrier φ M)) :=
    originalInductionLiftIso φ M
  exact Functor.IsRelativeProjective.of_retract
    ((ModuleCat.induceRestrictScalarsAdj.{u, v, w} φ).isRelativeProjective_obj M')
    e.symm.retract g s f

/-- The induction counit splits exactly for relatively projective modules. -/
theorem isRelativeProjective_iff_counit_isSplitEpi (P : ModuleCat.{max u v w} R) :
    (ModuleCat.restrictScalars.{max u v w} φ).IsRelativeProjective P ↔
      IsSplitEpi ((ModuleCat.induceRestrictScalarsAdj.{u, v, w} φ).counit.app P) :=
  (ModuleCat.induceRestrictScalarsAdj.{u, v, w} φ).isRelativeProjective_iff_counit_isSplitEpi P

/-- Every relative object is a retract of an induced object in the adjunction universe. -/
theorem isRelativeProjective_iff_retract_induced (P : ModuleCat.{max u v w} R) :
    (ModuleCat.restrictScalars.{max u v w} φ).IsRelativeProjective P ↔
      ∃ M : ModuleCat.{max u v w} k,
        Nonempty (Retract P ((ModuleCat.induceScalars.{u, v, w} φ).obj M)) :=
  (ModuleCat.induceRestrictScalarsAdj.{u, v, w} φ).isRelativeProjective_iff_retract_free P

end ModuleCat.RingHomInduction
