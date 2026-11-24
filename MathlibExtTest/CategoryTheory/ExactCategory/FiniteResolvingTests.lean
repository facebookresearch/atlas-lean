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

public import MathlibExt.CategoryTheory.ExactCategory.FiniteResolving

/-!
# Tests for finite resolving carriers

These consumers exercise the kernel-lift carrier, the kernel/finite/projective
resolving-data hierarchy, mapped short exactness, reflected admissible
exactness, and the absence of a transitive `KTheory` dependency.  Source and
target categories use independent object and morphism universes.  The final
checks guard that resolving data and kernel lifts are not installed as global
instances.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits

universe vP uP vA uA

namespace MathlibExtTest.CategoryTheory.ExactCategory.FiniteResolvingTests

variable {P : Type uP} [Category.{vP} P] [Preadditive P]
variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable (i : P ⥤ A) [i.Additive]

/-- Kernel resolving data is explicitly proposition-valued. -/
example : Prop := CategoryTheory.Functor.KernelResolvingData i

/-- Finite resolving data is explicitly proposition-valued. -/
example : Prop := CategoryTheory.Functor.FiniteResolvingData i

/-- Projective resolving data is explicitly proposition-valued. -/
example : Prop := CategoryTheory.Functor.ProjectiveResolvingData i

/-- Finite projective resolving data is explicitly proposition-valued. -/
example : Prop := CategoryTheory.Functor.FiniteProjectiveResolvingData i

example (data : CategoryTheory.Functor.KernelResolvingData i)
    {P₁ P₂ : P} (f : P₁ ⟶ P₂) (hf : Epi (i.map f)) :
    Nonempty (CategoryTheory.Functor.KernelLift i f) :=
  data.kernelOfEpi f hf

/-- The kernel-only carrier exposes neither global resolutions nor
projectivity. -/
example (_data : CategoryTheory.Functor.KernelResolvingData i) : True := by
  fail_if_success
    let _ := _data.finiteResolution
  fail_if_success
    let _ := _data.projective_obj
  trivial

example (data : CategoryTheory.Functor.FiniteResolvingData i) (X : A) :
    Nonempty (CategoryTheory.Abelian.FiniteResolution i X) :=
  data.finiteResolution X

example (data : CategoryTheory.Functor.FiniteResolvingData i)
    {P₁ P₂ : P} (f : P₁ ⟶ P₂) (hf : Epi (i.map f)) :
    Nonempty (CategoryTheory.Functor.KernelLift i f) :=
  data.kernelOfEpi f hf

/-- Finite resolving data does not silently acquire projectivity. -/
example (_data : CategoryTheory.Functor.FiniteResolvingData i) : True := by
  fail_if_success
    let _ := _data.projective_obj
  trivial

/-- Finite data forgets naturally to its kernel-only carrier. -/
example (data : CategoryTheory.Functor.FiniteResolvingData i) :
    CategoryTheory.Functor.KernelResolvingData i :=
  data.toKernelResolvingData

example (data : CategoryTheory.Functor.ProjectiveResolvingData i)
    (P₀ : P) : Projective (i.obj P₀) :=
  data.projective_obj P₀

/-- Projective resolving data does not silently acquire global resolution
choices. -/
example (_data : CategoryTheory.Functor.ProjectiveResolvingData i) : True := by
  fail_if_success
    let _ := _data.finiteResolution
  trivial

/-- Projective data forgets naturally to its kernel-only carrier. -/
example (data : CategoryTheory.Functor.ProjectiveResolvingData i) :
    CategoryTheory.Functor.KernelResolvingData i :=
  data.toKernelResolvingData

/-- Full finite-projective data exposes both natural projections and the
source-compatible finite-resolving conversion. -/
example (data : CategoryTheory.Functor.FiniteProjectiveResolvingData i) :
    CategoryTheory.Functor.KernelResolvingData i ∧
      CategoryTheory.Functor.ProjectiveResolvingData i ∧
        CategoryTheory.Functor.FiniteResolvingData i :=
  ⟨data.toKernelResolvingData, data.toProjectiveResolvingData,
    data.toFiniteResolvingData⟩

section KernelLift

variable {i : P ⥤ A} [i.Additive]
variable {P₁ P₂ : P} {f : P₁ ⟶ P₂}
variable (lift : CategoryTheory.Functor.KernelLift i f)

example : ShortComplex P := lift.shortComplex

example [Epi (i.map f)] : (lift.shortComplex.map i).ShortExact :=
  lift.mappedShortExact

variable [HasZeroObject P] [HasBinaryBiproducts P] [ExactCategory P]
variable [i.ReflectsAdmissibleExact]

example [Epi (i.map f)] :
    ExactCategory.IsAdmissibleExact lift.shortComplex :=
  lift.isAdmissibleExact

end KernelLift

/-- Resolving choices are explicit data, never synthesized globally. -/
example {P₁ P₂ : P} (_f : P₁ ⟶ P₂) : True := by
  fail_if_success
    let _ := inferInstanceAs (CategoryTheory.Functor.KernelResolvingData i)
  fail_if_success
    let _ := inferInstanceAs (CategoryTheory.Functor.FiniteResolvingData i)
  fail_if_success
    let _ := inferInstanceAs
      (CategoryTheory.Functor.ProjectiveResolvingData i)
  fail_if_success
    let _ := inferInstanceAs
      (CategoryTheory.Functor.FiniteProjectiveResolvingData i)
  fail_if_success
    let _ := inferInstanceAs (CategoryTheory.Functor.KernelLift i _f)
  trivial

/-- error: Unknown identifier -/
#guard_msgs (error, substring := true) in
#check AlgebraicKTheory.K0.mk

/-- error: Unknown identifier -/
#guard_msgs (error, substring := true) in
#check AlgebraicKTheory.RingK0

/-- error: Unknown identifier -/
#guard_msgs (error, substring := true) in
#check AlgebraicKTheory.RingG0

end MathlibExtTest.CategoryTheory.ExactCategory.FiniteResolvingTests

end
