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
# Local homology comparisons for kernel inclusions

Let C have zero morphisms and finite limits, and let f : K → L be a morphism of complexes of
any shape c. Evaluation preserves kernels, so each component of kernel.ι f is monic, and it is
an isomorphism wherever the corresponding component of f is zero.

If f is zero in degree i and in the incoming degree c.prev i, the kernel inclusion induces an
isomorphism on degree-i homology whenever the kernel and K have that homology. For nonnegative
cochain complexes, degree zero needs only f₀ = 0, and degree one needs f₀ = f₁ = 0.
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

/-- Let C be a category with zero morphisms and finite limits, let c be any complex shape on an
index type ι, and let f : K ⟶ L be a map of complexes of shape c. For i : ι, if f.f i = 0,
then (kernel.ι f).f i : (kernel f).X i ⟶ K.X i is an isomorphism. -/
theorem isIso_kernelInclusion_f_of_zero (i : ι) (hf : f.f i = 0) :
    IsIso ((kernel.ι f).f i) := by
  let F : HomologicalComplex C c ⥤ C := eval C c i
  have hzero : F.map f = 0 := by
    change f.f i = 0
    exact hf
  let : IsIso (kernel.ι (F.map f)) :=
    KernelFork.IsLimit.isIso_ι
      (KernelFork.ofι (kernel.ι (F.map f)) (kernel.condition (F.map f)))
      (kernelIsKernel (F.map f)) hzero
  change IsIso (F.map (kernel.ι f))
  rw [← kernelComparison_comp_ι f F]
  infer_instance

/-- Let C be a category with zero morphisms and finite limits, let c be any complex shape on an
index type ι, and let f : K ⟶ L be a map of complexes of shape c. Assume kernel f and K each
have homology in degree i. If f.f i = 0 and f.f (c.prev i) = 0, then kernel.ι f is a
quasi-isomorphism at i: its map on degree-i homology is an isomorphism. The component at
c.next i is monic as a kernel inclusion. -/
theorem quasiIsoAt_kernelInclusion_of_zero_components (i : ι)
    [(kernel f).HasHomology i] [K.HasHomology i]
    (hi : f.f i = 0) (hprev : f.f (c.prev i) = 0) :
    QuasiIsoAt (kernel.ι f) i := by
  let : IsIso ((kernel.ι f).f i) := isIso_kernelInclusion_f_of_zero f i hi
  let : IsIso ((kernel.ι f).f (c.prev i)) :=
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

/-- Let C be a category with zero morphisms and finite limits, let c be any complex shape on an
index type ι, and let f : K ⟶ L be a map of complexes of shape c. If kernel f and K have
homology in degree i, and f.f i = f.f (c.prev i) = 0, define the isomorphism (kernel
f).homology i ≅ K.homology i by the homology map of kernel.ι f. -/
def kernelHomologyIsoOfZeroComponents (i : ι)
    [(kernel f).HasHomology i] [K.HasHomology i]
    (hi : f.f i = 0) (hprev : f.f (c.prev i) = 0) :
    (kernel f).homology i ≅ K.homology i := by
  let : QuasiIsoAt (kernel.ι f) i :=
    quasiIsoAt_kernelInclusion_of_zero_components f i hi hprev
  exact _root_.isoOfQuasiIsoAt (kernel.ι f) i

/-- Let C be a category with zero morphisms and finite limits, let c be any complex shape on an
index type ι, and let f : K ⟶ L be a map of complexes of shape c. Assume both degree-i
homology objects exist and f.f i = f.f (c.prev i) = 0. The forward map of
kernelHomologyIsoOfZeroComponents f i hi hprev is homologyMap (kernel.ι f) i. -/
theorem kernelHomologyIsoOfZeroComponents_hom (i : ι)
    [(kernel f).HasHomology i] [K.HasHomology i]
    (hi : f.f i = 0) (hprev : f.f (c.prev i) = 0) :
    (kernelHomologyIsoOfZeroComponents f i hi hprev).hom =
      homologyMap (kernel.ι f) i := rfl

end ArbitraryShape

section NonnegativeCochains

variable {K L : CochainComplex C ℕ} (f : K ⟶ L)

/-- Let C have zero morphisms and finite limits, and let f : K ⟶ L be a map of cochain complexes
indexed by ℕ. If kernel f and K have homology in degree 0 and f.f 0 = 0, the kernel inclusion
induces an isomorphism H⁰(kernel f) ≅ H⁰(K). The predecessor convention at degree zero is (up
ℕ).prev 0 = 0. -/
def kernelHomologyZeroIso [(kernel f).HasHomology 0] [K.HasHomology 0]
    (h0 : f.f 0 = 0) : (kernel f).homology 0 ≅ K.homology 0 :=
  kernelHomologyIsoOfZeroComponents f 0 h0 (by
    simpa only [CochainComplex.prev_nat_zero] using h0)

/-- Let C have zero morphisms and finite limits, and let f : K ⟶ L be a map of cochain complexes
indexed by ℕ. If kernel f and K have homology in degree 1 and f.f 1 = f.f 0 = 0, the kernel
inclusion induces an isomorphism H¹(kernel f) ≅ H¹(K). -/
def kernelHomologyOneIso [(kernel f).HasHomology 1] [K.HasHomology 1]
    (h1 : f.f 1 = 0) (h0 : f.f 0 = 0) : (kernel f).homology 1 ≅ K.homology 1 :=
  kernelHomologyIsoOfZeroComponents f 1 h1 (by
    simpa only [CochainComplex.prev_nat_succ] using h0)

end NonnegativeCochains

end HomologicalComplex
