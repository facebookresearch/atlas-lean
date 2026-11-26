/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.FiniteResolution
public import MathlibExt.CategoryTheory.ExactCategory.Abelian
public import MathlibExt.CategoryTheory.ExactCategory.Functor
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic

/-!
# Finite resolving additive functors

Let `P` be a preadditive category, `A` an abelian category, and
`i : P → A` an additive functor. Kernel-resolving data represent the
kernel of each epimorphism between mapped source objects by a source
object and inclusion. Projective-resolving data additionally require
each `i(P₀)` to be projective in `A`; finite-resolving data require a
finite resolution of every object of `A` by mapped objects of `P`.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits

universe vP uP vA uA

namespace CategoryTheory.Functor

variable {P : Type uP} [Category.{vP} P] [Preadditive P]
variable {A : Type uA} [Category.{vA} A] [Abelian A]

/- Proof implementation note.
A source representative for the kernel of a mapped morphism.

The field `mappedIsLimit` says that the image of `ι` has the universal
property of the ambient kernel.  No kernel choice is installed globally.
-/

/-- For an additive functor `i : P → A` from a preadditive category to an
abelian category and a map `f : P₁ → P₂`, a kernel lift consists of
`K ∈ P` and `ι : K → P₁` with `ι ≫ f = 0`, such that `i(ι)` is a
kernel of `i(f)` in `A`. -/
structure KernelLift (i : P ⥤ A) [i.Additive]
    {P₁ P₂ : P} (f : P₁ ⟶ P₂) where
  /-- For a kernel lift of `f : P₁ → P₂` along an additive functor
`i : P → A` with `P` preadditive and `A` abelian, `K` is the source
object whose image represents the kernel of `i(f)`. -/
  K : P
  /-- For a kernel lift along an additive functor `i : P → A`, with `P`
preadditive and `A` abelian, the map `ι : K → P₁` becomes the kernel
inclusion of `i(f) : i(P₁) → i(P₂)` after applying `i`. -/
  ι : K ⟶ P₁
  /-- For a kernel lift of `f : P₁ → P₂` along an additive functor
`i : P → A`, the source inclusion has zero composite `ι ≫ f = 0`.
This is the short-complex relation in the preadditive source category. -/
  zero : ι ≫ f = 0
  /-- For a kernel lift along an additive functor `i : P → A`, where `A`
is abelian, `i(ι) : i(K) → i(P₁)` has the kernel universal property
for `i(f)`. Thus every map annihilated by `i(f)` factors uniquely through `i(ι)`. -/
  mappedIsLimit :
    IsLimit (KernelFork.ofι (f := i.map f) (i.map ι) (by
      rw [← i.map_comp, zero, i.map_zero]))

/-- For a preadditive category `P`, an abelian category `A`, and additive
`i : P → A`, kernel-resolving data require a kernel lift in `P` for
every source map whose image under `i` is an epimorphism in `A`. -/
structure KernelResolvingData (i : P ⥤ A) [i.Additive] : Prop where
  /-- For kernel-resolving data of additive `i : P → A`, with `A` abelian,
each map `f : P₁ → P₂` for which `i(f)` is epic admits a source object
and inclusion representing its ambient kernel. -/
  kernelOfEpi : ∀ {P₁ P₂ : P} (f : P₁ ⟶ P₂),
    Epi (i.map f) → Nonempty (KernelLift i f)

/-- For additive `i : P → A` from a preadditive category to an abelian
category, finite-resolving data combine kernel lifts for mapped
epimorphisms with a finite resolution of every target object by objects in the image of `i`. -/
structure FiniteResolvingData (i : P ⥤ A) [i.Additive] : Prop
    extends KernelResolvingData i where
  /-- For finite-resolving data of additive `i : P → A`, with `A` abelian,
every object `X ∈ A` admits a finite resolution by mapped source objects
`i(P₀), …, i(Pₙ)`. -/
  finiteResolution : ∀ X : A,
    Nonempty (CategoryTheory.Abelian.FiniteResolution i X)

/-- For additive `i : P → A`, with `P` preadditive and `A` abelian,
projective-resolving data require represented kernels of mapped
epimorphisms and projectivity of every mapped object `i(P₀)`. -/
structure ProjectiveResolvingData (i : P ⥤ A) [i.Additive] : Prop
    extends KernelResolvingData i where
  /-- For projective-resolving data of additive `i : P → A`, where `A`
is abelian, each source object `P₀` has projective image `i(P₀)`
in the target category. -/
  projective_obj : ∀ P₀ : P, Projective (i.obj P₀)

/-- For additive `i : P → A`, with `P` preadditive and `A` abelian,
finite projective-resolving data combine represented kernels of mapped
epimorphisms, projective mapped objects, and finite resolutions of
every target object by these mapped objects. -/
structure FiniteProjectiveResolvingData (i : P ⥤ A) [i.Additive] : Prop
    extends ProjectiveResolvingData i where
  /-- For finite projective-resolving data of additive `i : P → A`, each
object `X` of the abelian target has a finite resolution by objects
from `P` after applying `i`. -/
  finiteResolution : ∀ X : A,
    Nonempty (CategoryTheory.Abelian.FiniteResolution i X)

namespace FiniteProjectiveResolvingData

variable {i : P ⥤ A} [i.Additive]

/-- For additive `i : P → A`, with `P` preadditive and `A` abelian,
finite projective-resolving data give finite-resolving data: the
represented kernels and finite resolutions are retained. -/
theorem toFiniteResolvingData (data : FiniteProjectiveResolvingData i) :
    FiniteResolvingData i where
  toKernelResolvingData := data.toKernelResolvingData
  finiteResolution := data.finiteResolution

end FiniteProjectiveResolvingData

namespace KernelLift

variable {i : P ⥤ A} [i.Additive]
variable {P₁ P₂ : P} {f : P₁ ⟶ P₂}

/-- For a kernel lift of `f : P₁ → P₂` along additive `i : P → A`,
the maps `K → P₁ → P₂` form a short complex in the preadditive
source `P`, with the zero composite provided by the lift. -/
def shortComplex (lift : KernelLift i f) : ShortComplex P :=
  ShortComplex.mk lift.ι f lift.zero

/-- For additive `i : P → A` into an abelian category and a kernel lift
of `f : P₁ → P₂`, if `i(f)` is epic, the mapped sequence
`i(K) → i(P₁) → i(P₂)` is short exact. -/
theorem mappedShortExact (lift : KernelLift i f) [Epi (i.map f)] :
    (lift.shortComplex.map i).ShortExact := by
  have hExact : (lift.shortComplex.map i).Exact :=
    (lift.shortComplex.map i).exact_of_f_is_kernel lift.mappedIsLimit
  exact ShortComplex.ShortExact.mk' hExact
    (Fork.IsLimit.mono lift.mappedIsLimit)
    (inferInstance : Epi (i.map f))

variable [HasZeroObject P] [HasBinaryBiproducts P] [ExactCategory P]
variable [i.ReflectsAdmissibleExact]

/-- Let `P` be an additive exact category, `A` abelian, and `i : P → A`
additive and reflecting admissible exactness. If `i(f)` is epic and
a kernel lift represents its kernel, the source sequence `K → P₁ → P₂`
is admissible exact in `P`. -/
theorem isAdmissibleExact (lift : KernelLift i f) [Epi (i.map f)] :
    ExactCategory.IsAdmissibleExact lift.shortComplex :=
  i.reflects_admissibleExact lift.shortComplex lift.mappedShortExact

end KernelLift

end CategoryTheory.Functor

end
