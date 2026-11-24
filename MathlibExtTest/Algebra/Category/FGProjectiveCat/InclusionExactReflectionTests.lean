/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Category.FGProjectiveCat.InclusionExactReflection

/-!
# Tests for exact reflection along `FGProjectiveCat.inclusion`

These tests consume the reflection instance and the epi-kernel projectivity
theorem while guarding that kernel projectivity remains an explicit result,
not a global instance.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v u

namespace FGProjectiveCat.InclusionExactReflection.Tests

variable (R : Type u) [Ring R] [IsNoetherianRing R]

example : CategoryTheory.Functor.ReflectsAdmissibleExact
    (inclusion (R := R) : FGProjectiveCat.{v} R ⥤ FGModuleCat.{v} R) :=
  inferInstance

/-- Admissible exactness of the mapped short complex reflects to the split
exact structure on finitely generated projective modules. -/
example (S : ShortComplex (FGProjectiveCat.{v} R))
    (hS : ExactCategory.IsAdmissibleExact (S.map (inclusion R))) :
    ExactCategory.IsAdmissibleExact S :=
  (inclusion R).reflects_admissibleExact S hS

/-- The public kernel-closure theorem supplies projectivity for the kernel of
an epi between included projectives. -/
example {P Q : FGProjectiveCat.{v} R}
    (g : (inclusion R).obj P ⟶ (inclusion R).obj Q) [Epi g] :
    Module.Projective R (kernel g : FGModuleCat.{v} R) :=
  kernel_projective_of_epi R g

/-- Kernel projectivity is deliberately not installed as a global instance. -/
example {P Q : FGProjectiveCat.{v} R}
    (g : (inclusion R).obj P ⟶ (inclusion R).obj Q) [Epi g] : True := by
  fail_if_success
    let _ := inferInstanceAs
      (Module.Projective R (kernel g : FGModuleCat.{v} R))
  trivial

end FGProjectiveCat.InclusionExactReflection.Tests

end
