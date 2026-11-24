/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Local homology of the actual kernel inclusion

Native finite-limit evaluation makes every component of a kernel inclusion
mono. At a zero defining component the inclusion is an isomorphism. The
native epi/isomorphism/mono homology criterion then supplies the actual
homology comparison when the defining middle and incoming components
vanish, with only the two indicated homologies assumed.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasFiniteLimits C]

section ArbitraryShape

variable {ι : Type w} {c : ComplexShape ι}
  {K L : HomologicalComplex C c} (f : K ⟶ L)

/-- The actual kernel-inclusion component is an isomorphism where the defining map is zero. -/
theorem isIso_kernelInclusion_f_of_zero (i : ι) (hf : f.f i = 0) :
    IsIso ((kernel.ι f).f i) := by
  let F : HomologicalComplex C c ⥤ C := eval C c i
  have hzero : F.map f = 0 := by
    change f.f i = 0
    exact hf
  letI : IsIso (kernel.ι (F.map f)) :=
    KernelFork.IsLimit.isIso_ι
      (KernelFork.ofι (kernel.ι (F.map f)) (kernel.condition (F.map f)))
      (kernelIsKernel (F.map f)) hzero
  change IsIso (F.map (kernel.ι f))
  rw [← kernelComparison_comp_ι f F]
  infer_instance

/-- Actual vanishing at the middle and incoming degrees earns kernel homology transport. -/
theorem quasiIsoAt_kernelInclusion_of_zero_components (i : ι)
    [(kernel f).HasHomology i] [K.HasHomology i]
    (hi : f.f i = 0) (hprev : f.f (c.prev i) = 0) :
    QuasiIsoAt (kernel.ι f) i := by
  letI : IsIso ((kernel.ι f).f i) := isIso_kernelInclusion_f_of_zero f i hi
  letI : IsIso ((kernel.ι f).f (c.prev i)) :=
    isIso_kernelInclusion_f_of_zero f (c.prev i) hprev
  rw [quasiIsoAt_iff]
  let : Epi (((shortComplexFunctor C c i).map (kernel.ι f)).τ₁) := by
    change Epi ((kernel.ι f).f (c.prev i))
    infer_instance
  let : IsIso (((shortComplexFunctor C c i).map (kernel.ι f)).τ₂) := by
    change IsIso ((kernel.ι f).f i)
    infer_instance
  let : Mono (((shortComplexFunctor C c i).map (kernel.ι f)).τ₃) := by
    change Mono ((kernel.ι f).f (c.next i))
    infer_instance
  exact ShortComplex.quasiIso_of_epi_of_isIso_of_mono
    ((shortComplexFunctor C c i).map (kernel.ι f))

/-- The canonical isomorphism is homology of the actual kernel inclusion itself. -/
def kernelHomologyIsoOfZeroComponents (i : ι)
    [(kernel f).HasHomology i] [K.HasHomology i]
    (hi : f.f i = 0) (hprev : f.f (c.prev i) = 0) :
    (kernel f).homology i ≅ K.homology i := by
  letI := quasiIsoAt_kernelInclusion_of_zero_components f i hi hprev
  exact _root_.isoOfQuasiIsoAt (kernel.ι f) i

/-- The actual forward homology map is retained without unfolding the public construction. -/
theorem kernelHomologyIsoOfZeroComponents_hom (i : ι)
    [(kernel f).HasHomology i] [K.HasHomology i]
    (hi : f.f i = 0) (hprev : f.f (c.prev i) = 0) :
    (kernelHomologyIsoOfZeroComponents f i hi hprev).hom =
      homologyMap (kernel.ι f) i := rfl

end ArbitraryShape

section NonnegativeCochains

variable {K L : CochainComplex C ℕ} (f : K ⟶ L)

/-- At degree zero only the degree-zero defining component must vanish. -/
def kernelHomologyZeroIso [(kernel f).HasHomology 0] [K.HasHomology 0]
    (h0 : f.f 0 = 0) : (kernel f).homology 0 ≅ K.homology 0 :=
  kernelHomologyIsoOfZeroComponents f 0 h0 (by
    erw [CochainComplex.prev_nat_zero]
    exact h0)

/-- Degree one needs zero components at degrees one and zero; outgoing inclusion is mono. -/
def kernelHomologyOneIso [(kernel f).HasHomology 1] [K.HasHomology 1]
    (h1 : f.f 1 = 0) (h0 : f.f 0 = 0) : (kernel f).homology 1 ≅ K.homology 1 :=
  kernelHomologyIsoOfZeroComponents f 1 h1 (by
    erw [CochainComplex.prev_nat_succ (0 : ℕ)]
    exact h0)

end NonnegativeCochains

end HomologicalComplex
