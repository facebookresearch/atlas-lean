/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Abelian.DeltaFunctor.DimensionShift
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.DeltaFunctor

/-!
# First left derivation as the kernel of a mapped monomorphism

Let `C,D` be abelian, with projective resolutions in `C`, and
`F : C → D` additive and preserving finite colimits. For short exact
`X₁ → X₂ → X₃` with `L₁F(X₂)=0`, the boundary identifies
`L₁F(X₃)` with `ker(F(X₁) → F(X₂))`. Its inclusion is the boundary
followed by the degree-zero comparison `L₀F(X₁) ≅ F(X₁)`.
-/

@[expose] public section

open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasProjectiveResolutions C]
variable {D : Type u₂} [Category.{v₂} D] [Abelian D]

/-- Let `C,D` be abelian, with projective resolutions in `C`,
and `F : C → D` additive. Suppose `F` preserves finite colimits. For short exact `S : X₁ → X₂ → X₃` with `L₁F(X₂)=0`,
the degree-one boundary gives an isomorphism
`L₁F(X₃) ≅ ker(F(S.f))`. -/
noncomputable def leftDerivedOneIsoKernel (F : C ⥤ D) [F.Additive]
    [PreservesFiniteColimits F] (S : ShortComplex.ShortExactSequences C)
    (h : IsZero ((F.leftDerived 1).obj S.obj.X₂)) :
    (F.leftDerived 1).obj S.obj.X₃ ≅ Limits.kernel (F.map S.obj.f) := by
  have hT : IsZero ((F.leftDerivedDeltaFunctor.T (0 + 1)).obj S.obj.X₂) := by
    simpa only [leftDerivedDeltaFunctor_T] using h
  let f₀ := (F.leftDerived 0).map S.obj.f
  let k : KernelFork f₀ := KernelFork.ofι (kernel.ι f₀) (kernel.condition f₀)
  let g : (F.leftDerived 1).obj S.obj.X₃ ≅ Limits.kernel f₀ :=
    KernelFork.mapIsoOfIsLimit (kf' := k)
      (F.leftDerivedDeltaFunctor.connectingIsKernelOfIsZeroMiddleSucc 0 S hT)
      (kernelIsKernel f₀) (Iso.refl (Arrow.mk f₀))
  let e : F.leftDerived 0 ≅ F := F.leftDerivedZeroIsoSelf
  exact g ≪≫ kernel.mapIso f₀ (F.map S.obj.f)
    (e.app S.obj.X₁) (e.app S.obj.X₂) (e.hom.naturality S.obj.f)

/-- Let `C,D` be abelian, with projective resolutions in `C`,
and `F : C → D` additive. Suppose `F` preserves finite colimits. For short exact `S : X₁ → X₂ → X₃` with `L₁F(X₂)=0`,
the kernel isomorphism followed by `ker(F(S.f)) → F(X₁)` equals
`δ₀ : L₁F(X₃) → L₀F(X₁)` followed by `L₀F(X₁) ≅ F(X₁)`. -/
@[reassoc]
lemma leftDerivedOneIsoKernel_hom_ι (F : C ⥤ D) [F.Additive]
    [PreservesFiniteColimits F] (S : ShortComplex.ShortExactSequences C)
    (h : IsZero ((F.leftDerived 1).obj S.obj.X₂)) :
    (F.leftDerivedOneIsoKernel S h).hom ≫ kernel.ι (F.map S.obj.f) =
      LeftDerivedDelta.LDdelta F 0 S.obj S.property ≫
        F.leftDerivedZeroIsoSelf.hom.app S.obj.X₁ := by
  have hT : IsZero ((F.leftDerivedDeltaFunctor.T (0 + 1)).obj S.obj.X₂) := by
    simpa only [leftDerivedDeltaFunctor_T] using h
  let f₀ := (F.leftDerived 0).map S.obj.f
  let c : KernelFork f₀ :=
    KernelFork.ofι ((F.leftDerivedDeltaFunctor.connecting 0).app S)
      ((F.leftDerivedDeltaFunctor.exactLeft 0 S).elim (fun w _ => w))
  let k : KernelFork f₀ := KernelFork.ofι (kernel.ι f₀) (kernel.condition f₀)
  let g : (F.leftDerived 1).obj S.obj.X₃ ≅ Limits.kernel f₀ :=
    KernelFork.mapIsoOfIsLimit (kf' := k)
      (F.leftDerivedDeltaFunctor.connectingIsKernelOfIsZeroMiddleSucc 0 S hT)
      (kernelIsKernel f₀) (Iso.refl (Arrow.mk f₀))
  let e : F.leftDerived 0 ≅ F := F.leftDerivedZeroIsoSelf
  have hg : g.hom ≫ kernel.ι f₀ =
      (F.leftDerivedDeltaFunctor.connecting 0).app S := by
    have H := KernelFork.mapOfIsLimit_ι c (kf' := k)
      (kernelIsKernel f₀) (𝟙 (Arrow.mk f₀))
    change c.mapOfIsLimit (kf' := k) (kernelIsKernel f₀) (𝟙 (Arrow.mk f₀)) ≫ k.ι = c.ι
    rw [Arrow.id_left] at H
    exact H.trans (Category.comp_id c.ι)
  have hk : (kernel.mapIso f₀ (F.map S.obj.f)
      (e.app S.obj.X₁) (e.app S.obj.X₂) (e.hom.naturality S.obj.f)).hom ≫
        kernel.ι (F.map S.obj.f) = kernel.ι f₀ ≫ e.hom.app S.obj.X₁ := by
    change kernel.map f₀ (F.map S.obj.f) (e.app S.obj.X₁).hom
      (e.app S.obj.X₂).hom (e.hom.naturality S.obj.f) ≫
        kernel.ι (F.map S.obj.f) = kernel.ι f₀ ≫ e.hom.app S.obj.X₁
    exact kernel.lift_ι _ _ _
  change (g.hom ≫ (kernel.mapIso f₀ (F.map S.obj.f)
      (e.app S.obj.X₁) (e.app S.obj.X₂) (e.hom.naturality S.obj.f)).hom) ≫
        kernel.ι (F.map S.obj.f) =
      LeftDerivedDelta.LDdelta F 0 S.obj S.property ≫ e.hom.app S.obj.X₁
  rw [Category.assoc, hk, ← Category.assoc, hg]
  exact congrArg (fun a => a ≫ e.hom.app S.obj.X₁)
    (leftDerivedDeltaFunctor_connecting_app F 0 S)

end CategoryTheory.Functor
