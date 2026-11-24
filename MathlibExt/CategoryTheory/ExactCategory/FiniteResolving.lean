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

public import MathlibExt.Algebra.Homology.FiniteResolution
public import MathlibExt.CategoryTheory.ExactCategory.Abelian
public import MathlibExt.CategoryTheory.ExactCategory.Functor
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic

/-!
# Finite resolving functors

This file packages the explicit data needed from a resolving additive functor
`i : P ⥤ A`: source representatives for kernels of mapped epimorphisms,
projectivity of mapped source objects, and finite resolutions of target
objects.  These obligations have separate carriers so downstream results can
state only the hypotheses they use.  A kernel lift records the actual source
morphism whose image is a kernel, so its short-exact consequences do not
require reconstructing that morphism.

The resolving-data structures are propositions, not typeclasses.  They make
nonfunctorial existence hypotheses explicit and do not contain comparison
maps, Euler independence, additivity, an inverse on `K₀`, or bijectivity.

## Main declarations

* `CategoryTheory.Functor.KernelLift`
* `CategoryTheory.Functor.KernelResolvingData`
* `CategoryTheory.Functor.FiniteResolvingData`
* `CategoryTheory.Functor.ProjectiveResolvingData`
* `CategoryTheory.Functor.FiniteProjectiveResolvingData`
* `CategoryTheory.Functor.KernelLift.mappedShortExact`
* `CategoryTheory.Functor.KernelLift.isAdmissibleExact`
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits

universe vP uP vA uA

namespace CategoryTheory.Functor

variable {P : Type uP} [Category.{vP} P] [Preadditive P]
variable {A : Type uA} [Category.{vA} A] [Abelian A]

/-- A source representative for the kernel of a mapped morphism.

The field `mappedIsLimit` says that the image of `ι` has the universal
property of the ambient kernel.  No kernel choice is installed globally. -/
structure KernelLift (i : P ⥤ A) [i.Additive]
    {P₁ P₂ : P} (f : P₁ ⟶ P₂) where
  /-- The source object representing the ambient kernel. -/
  K : P
  /-- The represented kernel inclusion. -/
  ι : K ⟶ P₁
  /-- The source composite is zero. -/
  zero : ι ≫ f = 0
  /-- After mapping to `A`, `ι` has the universal property of a kernel of
  `i.map f`. -/
  mappedIsLimit :
    IsLimit (KernelFork.ofι (f := i.map f) (i.map ι) (by
      rw [← i.map_comp, zero, i.map_zero]))

/-- Explicit epi-kernel closure data for an additive functor into an abelian
category.

This is an ordinary proposition rather than a typeclass: kernel
representatives are nonfunctorial mathematical input. -/
structure KernelResolvingData (i : P ⥤ A) [i.Additive] : Prop where
  /-- The kernel of every mapped epimorphism is represented in `P`. -/
  kernelOfEpi : ∀ {P₁ P₂ : P} (f : P₁ ⟶ P₂),
    Epi (i.map f) → Nonempty (KernelLift i f)

/-- Epi-kernel closure together with a finite resolution of every target
object.

The resolution and kernel choices remain explicit, proposition-valued input.
-/
structure FiniteResolvingData (i : P ⥤ A) [i.Additive] : Prop
    extends KernelResolvingData i where
  /-- Every target object admits a finite resolution by objects from `P`. -/
  finiteResolution : ∀ X : A,
    Nonempty (CategoryTheory.Abelian.FiniteResolution i X)

/-- Epi-kernel closure together with projectivity of every object after
mapping to the abelian target.

The projectivity field is structural input for resolution comparison; it is
not an Euler, inverse, or bijectivity hypothesis. -/
structure ProjectiveResolvingData (i : P ⥤ A) [i.Additive] : Prop
    extends KernelResolvingData i where
  /-- Every mapped source object is projective in the target. -/
  projective_obj : ∀ P₀ : P, Projective (i.obj P₀)

/-- Projective resolving data together with a finite resolution of every
target object.

This is the full input needed to define a global Euler inverse.  Results that
receive the resolutions explicitly should use `ProjectiveResolvingData`
instead. -/
structure FiniteProjectiveResolvingData (i : P ⥤ A) [i.Additive] : Prop
    extends ProjectiveResolvingData i where
  /-- Every target object admits a finite resolution by objects from `P`. -/
  finiteResolution : ∀ X : A,
    Nonempty (CategoryTheory.Abelian.FiniteResolution i X)

namespace FiniteProjectiveResolvingData

variable {i : P ⥤ A} [i.Additive]

/-- Forget projectivity while retaining the finite-resolution and represented
kernel data. -/
theorem toFiniteResolvingData (data : FiniteProjectiveResolvingData i) :
    FiniteResolvingData i where
  toKernelResolvingData := data.toKernelResolvingData
  finiteResolution := data.finiteResolution

end FiniteProjectiveResolvingData

namespace KernelLift

variable {i : P ⥤ A} [i.Additive]
variable {P₁ P₂ : P} {f : P₁ ⟶ P₂}

/-- The source short complex determined by a kernel lift. -/
def shortComplex (lift : KernelLift i f) : ShortComplex P :=
  ShortComplex.mk lift.ι f lift.zero

/-- The mapped kernel short complex is short exact when its final map is an
epimorphism. -/
theorem mappedShortExact (lift : KernelLift i f) [Epi (i.map f)] :
    (lift.shortComplex.map i).ShortExact := by
  have hExact : (lift.shortComplex.map i).Exact :=
    (lift.shortComplex.map i).exact_of_f_is_kernel lift.mappedIsLimit
  exact ShortComplex.ShortExact.mk' hExact
    (Fork.IsLimit.mono lift.mappedIsLimit)
    (inferInstance : Epi (i.map f))

variable [HasZeroObject P] [HasBinaryBiproducts P] [ExactCategory P]
variable [i.ReflectsAdmissibleExact]

/-- If `i` reflects admissible exactness, the source kernel short complex is
admissible exact. -/
theorem isAdmissibleExact (lift : KernelLift i f) [Epi (i.map f)] :
    ExactCategory.IsAdmissibleExact lift.shortComplex :=
  i.reflects_admissibleExact lift.shortComplex lift.mappedShortExact

end KernelLift

end CategoryTheory.Functor

end
