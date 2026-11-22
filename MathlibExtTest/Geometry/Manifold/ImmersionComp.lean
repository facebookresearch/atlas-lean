/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Geometry.Manifold.ImmersionComp

open Manifold
open scoped ContDiff Manifold

universe u

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E E' E'' : Type u}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H H' H'' : Type*}
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
  {I : ModelWithCorners 𝕜 E H}
  {J : ModelWithCorners 𝕜 E' H'}
  {J' : ModelWithCorners 𝕜 E'' H''}
variable {M N N' : Type u}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace H' N]
  [TopologicalSpace N'] [ChartedSpace H'' N']
variable {n : ℕ∞ω} {f : M → N} {g : N → N'}
variable {E₂ E₂' E₂'' : Type u}
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
  [NormedAddCommGroup E₂'] [NormedSpace 𝕜 E₂']
  [NormedAddCommGroup E₂''] [NormedSpace 𝕜 E₂'']
  {H₂ H₂' H₂'' : Type*}
  [TopologicalSpace H₂] [TopologicalSpace H₂'] [TopologicalSpace H₂'']
  {I' : ModelWithCorners 𝕜 E₂ H₂}
  {K : ModelWithCorners 𝕜 E₂' H₂'}
  {K' : ModelWithCorners 𝕜 E₂'' H₂''}
variable {M₂ N₂ N₂' : Type u}
  [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
  [TopologicalSpace N₂] [ChartedSpace H₂' N₂]
  [TopologicalSpace N₂'] [ChartedSpace H₂'' N₂']

-- Restricting the source to an open neighborhood preserves a pointwise immersion.
example [I.Boundaryless] [J.Boundaryless] [IsManifold I n M]
    (x : M) (s : TopologicalSpace.Opens M) (hx : x ∈ s)
    (hf : IsImmersionAt I J n f x) :
    IsImmersionAt I J n (f ∘ (Subtype.val : s → M)) ⟨x, hx⟩ :=
  hf.comp (IsImmersionAt.of_opens (I := I) s hx)

-- Composing pointwise immersions makes the differential injective.
example [J.Boundaryless] [J'.Boundaryless] (x : M) (hn : n ≠ 0)
    (hf : IsImmersionAt I J n f x) (hg : IsImmersionAt J J' n g (f x)) :
    Function.Injective (mfderiv I J' (g ∘ f) x) :=
  (hg.comp hf).mfderiv_injective hn

-- Fixed complements compose after swapping the product complement factors.
example {F₁ F₂ : Type*}
    [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
    [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
    [J.Boundaryless] [J'.Boundaryless]
    (hf : IsImmersionOfComplement F₁ I J n f)
    (hg : IsImmersionOfComplement F₂ J J' n g) :
    IsImmersionOfComplement (F₂ × F₁) I J' n (g ∘ f) :=
  (hg.comp hf).trans_F (ContinuousLinearEquiv.prodComm 𝕜 F₁ F₂)

-- Products of two composed pointwise immersions remain pointwise immersions.
example [J.Boundaryless] [J'.Boundaryless] [K.Boundaryless] [K'.Boundaryless]
    [IsManifold I n M] [IsManifold J n N] [IsManifold J' n N']
    [IsManifold I' n M₂] [IsManifold K n N₂] [IsManifold K' n N₂']
    (x₁ : M) (x₂ : M₂) (f₁ : M → N) (g₁ : N → N')
    (f₂ : M₂ → N₂) (g₂ : N₂ → N₂')
    (hf₁ : IsImmersionAt I J n f₁ x₁)
    (hg₁ : IsImmersionAt J J' n g₁ (f₁ x₁))
    (hf₂ : IsImmersionAt I' K n f₂ x₂)
    (hg₂ : IsImmersionAt K K' n g₂ (f₂ x₂)) :
    IsImmersionAt (I.prod I') (J'.prod K') n
      (Prod.map (g₁ ∘ f₁) (g₂ ∘ f₂)) (x₁, x₂) := by
  have hcomp := IsImmersionAt.comp
    (I := I.prod I') (J := J.prod K) (J' := J'.prod K')
    (f := Prod.map f₁ f₂) (g := Prod.map g₁ g₂) (x := (x₁, x₂))
    (hg₁.prodMap hg₂) (hf₁.prodMap hf₂)
  rw [← Prod.map_comp_map f₁ f₂ g₁ g₂]
  exact hcomp

-- The frozen global composition theorem yields smoothness of the composite.
example [CompleteSpace E] [CompleteSpace E'] [CompleteSpace E'']
    [I.Boundaryless] [J.Boundaryless] [J'.Boundaryless]
    [IsManifold I n M] [IsManifold J n N] [IsManifold J' n N']
    (hf : IsImmersion I J n f) (hg : IsImmersion J J' n g) :
    ContMDiff I J' n (g ∘ f) :=
  (MathlibExt.Geometry.Manifold.ImmersionCompWanted.immersion_comp hf hg).contMDiff
