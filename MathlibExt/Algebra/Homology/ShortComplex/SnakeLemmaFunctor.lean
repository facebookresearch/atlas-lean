/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma
@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

namespace CategoryTheory.ShortComplex.SnakeInput

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]

/-- Let C,D be abelian categories and F : C → D preserve zero morphisms, finite limits and finite
colimits. Let S consist of four short-complex rows L₀ → L₁ → L₂ → L₃, with L₀ the kernel and L₃
the cokernel of L₁ → L₂. Assume L₁,L₂ are exact, L₁'s second arrow is epi and L₂'s first arrow
is mono. Applying F to every object and map gives the corresponding snake-lemma input in D,
preserving the kernel and cokernel rows, row exactness, and the required epi and mono arrows. -/
noncomputable def mapExactFunctor (S : SnakeInput C) (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] : SnakeInput D where
  L₀ := F.mapShortComplex.obj S.L₀
  L₁ := F.mapShortComplex.obj S.L₁
  L₂ := F.mapShortComplex.obj S.L₂
  L₃ := F.mapShortComplex.obj S.L₃
  v₀₁ := F.mapShortComplex.map S.v₀₁
  v₁₂ := F.mapShortComplex.map S.v₁₂
  v₂₃ := F.mapShortComplex.map S.v₂₃
  w₀₂ := by
    apply ShortComplex.hom_ext
    · change F.map S.v₀₁.τ₁ ≫ F.map S.v₁₂.τ₁ = 0
      rw [← F.map_comp, S.w₀₂_τ₁, F.map_zero]
    · change F.map S.v₀₁.τ₂ ≫ F.map S.v₁₂.τ₂ = 0
      rw [← F.map_comp, S.w₀₂_τ₂, F.map_zero]
    · change F.map S.v₀₁.τ₃ ≫ F.map S.v₁₂.τ₃ = 0
      rw [← F.map_comp, S.w₀₂_τ₃, F.map_zero]
  w₁₃ := by
    apply ShortComplex.hom_ext
    · change F.map S.v₁₂.τ₁ ≫ F.map S.v₂₃.τ₁ = 0
      rw [← F.map_comp, S.w₁₃_τ₁, F.map_zero]
    · change F.map S.v₁₂.τ₂ ≫ F.map S.v₂₃.τ₂ = 0
      rw [← F.map_comp, S.w₁₃_τ₂, F.map_zero]
    · change F.map S.v₁₂.τ₃ ≫ F.map S.v₂₃.τ₃ = 0
      rw [← F.map_comp, S.w₁₃_τ₃, F.map_zero]
  h₀ :=
    ShortComplex.isLimitOfIsLimitπ _
      ((KernelFork.isLimitMapConeEquiv _ _).symm
        (isLimitForkMapOfIsLimit' F S.w₀₂_τ₁ S.h₀τ₁))
      ((KernelFork.isLimitMapConeEquiv _ _).symm
        (isLimitForkMapOfIsLimit' F S.w₀₂_τ₂ S.h₀τ₂))
      ((KernelFork.isLimitMapConeEquiv _ _).symm
        (isLimitForkMapOfIsLimit' F S.w₀₂_τ₃ S.h₀τ₃))
  h₃ :=
    ShortComplex.isColimitOfIsColimitπ _
      ((CokernelCofork.isColimitMapCoconeEquiv _ _).symm
        (isColimitCoforkMapOfIsColimit' F S.w₁₃_τ₁ S.h₃τ₁))
      ((CokernelCofork.isColimitMapCoconeEquiv _ _).symm
        (isColimitCoforkMapOfIsColimit' F S.w₁₃_τ₂ S.h₃τ₂))
      ((CokernelCofork.isColimitMapCoconeEquiv _ _).symm
        (isColimitCoforkMapOfIsColimit' F S.w₁₃_τ₃ S.h₃τ₃))
  L₁_exact := S.L₁_exact.map F
  L₂_exact := S.L₂_exact.map F
  epi_L₁_g := by
    have := S.epi_L₁_g
    change Epi (F.map S.L₁.g)
    infer_instance
  mono_L₂_f := by
    have := S.mono_L₂_f
    change Mono (F.map S.L₂.f)
    infer_instance

set_option backward.isDefEq.respectTransparency false in
private noncomputable def mapExactFunctorκ (S : SnakeInput C) (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] : F.obj S.P ⟶ (S.mapExactFunctor F).P :=
  pullback.lift (F.map (pullback.fst _ _)) (F.map (pullback.snd _ _)) (by
    have hcond : pullback.fst S.L₁.g S.v₀₁.τ₃ ≫ S.L₁.g =
        pullback.snd S.L₁.g S.v₀₁.τ₃ ≫ S.v₀₁.τ₃ :=
      pullback.condition
    have hmap : F.map (pullback.fst S.L₁.g S.v₀₁.τ₃) ≫ F.map S.L₁.g =
        F.map (pullback.snd S.L₁.g S.v₀₁.τ₃) ≫ F.map S.v₀₁.τ₃ := by
      rw [← F.map_comp, ← F.map_comp, hcond]
    exact hmap)

set_option backward.isDefEq.respectTransparency false in
private theorem mapExactFunctorκ_fst (S : SnakeInput C) (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] :
    mapExactFunctorκ S F ≫ pullback.fst _ _ = F.map (pullback.fst _ _) :=
  pullback.lift_fst _ _ _

set_option backward.isDefEq.respectTransparency false in
private theorem mapExactFunctorκ_snd (S : SnakeInput C) (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] :
    mapExactFunctorκ S F ≫ pullback.snd _ _ = F.map (pullback.snd _ _) :=
  pullback.lift_snd _ _ _

set_option backward.isDefEq.respectTransparency false in
private theorem mapExactFunctorκ_φ₂ (S : SnakeInput C) (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] :
    mapExactFunctorκ S F ≫ (S.mapExactFunctor F).φ₂ = F.map S.φ₂ := by
  have hfst := mapExactFunctorκ_fst S F
  have hv : (S.mapExactFunctor F).v₁₂.τ₂ = F.map S.v₁₂.τ₂ := rfl
  unfold φ₂
  rw [← Category.assoc, hfst, hv, ← F.map_comp]

set_option backward.isDefEq.respectTransparency false in
private theorem mapExactFunctorκ_φ₁ (S : SnakeInput C) (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] :
    mapExactFunctorκ S F ≫ (S.mapExactFunctor F).φ₁ = F.map S.φ₁ := by
  have := S.mono_L₂_f
  rw [← cancel_mono (F.map S.L₂.f)]
  have hLf : (S.mapExactFunctor F).L₂.f = F.map S.L₂.f := rfl
  have hφ₂ := mapExactFunctorκ_φ₂ S F
  calc (mapExactFunctorκ S F ≫ (S.mapExactFunctor F).φ₁) ≫ F.map S.L₂.f
      = mapExactFunctorκ S F ≫ ((S.mapExactFunctor F).φ₁ ≫
        (S.mapExactFunctor F).L₂.f) := by
        rw [Category.assoc, ← hLf]
    _ = mapExactFunctorκ S F ≫ (S.mapExactFunctor F).φ₂ := by
        rw [φ₁_L₂_f]
    _ = F.map S.φ₂ := hφ₂
    _ = F.map (S.φ₁ ≫ S.L₂.f) := by
        rw [φ₁_L₂_f]
    _ = F.map S.φ₁ ≫ F.map S.L₂.f := by
        rw [F.map_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Let C,D be abelian categories and F : C → D preserve zero morphisms, finite limits and finite
colimits. Let S consist of four short-complex rows L₀ → L₁ → L₂ → L₃, with L₀ the kernel and L₃
the cokernel of L₁ → L₂. Assume L₁,L₂ are exact, L₁'s second arrow is epi and L₂'s first arrow
is mono. If δ_S : (L₀)₃ → (L₃)₁ is the snake connecting morphism, then the connecting morphism
of the image diagram is F(δ_S) : F((L₀)₃) → F((L₃)₁), with the same sign convention. -/
theorem mapExactFunctor_δ (S : SnakeInput C) (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] :
    (S.mapExactFunctor F).δ = F.map S.δ := by
  have := S.epi_L₁_g
  rw [← cancel_epi (F.map (pullback.snd S.L₁.g S.v₀₁.τ₃))]
  have hsnd := mapExactFunctorκ_snd S F
  have hφ₁ := mapExactFunctorκ_φ₁ S F
  have hv : (S.mapExactFunctor F).v₂₃.τ₁ = F.map S.v₂₃.τ₁ := rfl
  calc F.map (pullback.snd S.L₁.g S.v₀₁.τ₃) ≫ (S.mapExactFunctor F).δ
      = (mapExactFunctorκ S F ≫ pullback.snd _ _) ≫
        (S.mapExactFunctor F).δ := by
        rw [hsnd]
    _ = mapExactFunctorκ S F ≫
        (pullback.snd _ _ ≫ (S.mapExactFunctor F).δ) := by
        rw [Category.assoc]
    _ = mapExactFunctorκ S F ≫
        ((S.mapExactFunctor F).φ₁ ≫ (S.mapExactFunctor F).v₂₃.τ₁) := by
        rw [snd_δ]
    _ = (mapExactFunctorκ S F ≫ (S.mapExactFunctor F).φ₁) ≫
        (S.mapExactFunctor F).v₂₃.τ₁ := by
        rw [← Category.assoc]
    _ = F.map S.φ₁ ≫ F.map S.v₂₃.τ₁ := by
        rw [hφ₁, hv]
    _ = F.map (S.φ₁ ≫ S.v₂₃.τ₁) := by
        rw [← F.map_comp]
    _ = F.map (pullback.snd S.L₁.g S.v₀₁.τ₃ ≫ S.δ) := by
        rw [← snd_δ]
    _ = F.map (pullback.snd S.L₁.g S.v₀₁.τ₃) ≫ F.map S.δ := by
        rw [F.map_comp]

end CategoryTheory.ShortComplex.SnakeInput
