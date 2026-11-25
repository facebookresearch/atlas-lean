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

public import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.SplitPullback
public import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.IteratedAlgebra

/-!
# Finite iteration of split-pullback preservation

A star-homomorphic section of one cospan leg is carried through every finite
iterate of the literal asymptotic algebra.  The resulting equivalence has the
expected two coordinate maps.

This file contains only the iterated equivalence and its projection laws.
It does not define paths, gluing, n-homotopy, classes, products, or limits.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace AsymptoticAlgebra

universe uA uB uC uX uY

attribute [local instance] cStarAlgebra

private noncomputable def alphaEquiv
    {X : Type uX} {Y : Type uY}
    [NonUnitalCStarAlgebra X] [NonUnitalCStarAlgebra Y]
    (e : X ≃⋆ₐ[ℂ] Y) :
    AsymptoticAlgebra X ≃⋆ₐ[ℂ] AsymptoticAlgebra Y := by
  let f : X →⋆ₙₐ[ℂ] Y := e.toNonUnitalStarAlgHom
  let g : Y →⋆ₙₐ[ℂ] X := e.symm.toNonUnitalStarAlgHom
  have hgf : g.comp f = NonUnitalStarAlgHom.id ℂ X := by
    apply NonUnitalStarAlgHom.ext
    intro x
    exact e.symm_apply_apply x
  have hfg : f.comp g = NonUnitalStarAlgHom.id ℂ Y := by
    apply NonUnitalStarAlgHom.ext
    intro y
    exact e.apply_symm_apply y
  have hGF :
      (map g).comp (map f) =
        NonUnitalStarAlgHom.id ℂ (AsymptoticAlgebra X) := by
    calc
      (map g).comp (map f) = map (g.comp f) := (map_comp f g).symm
      _ = map (NonUnitalStarAlgHom.id ℂ X) :=
        congrArg (fun h : X →⋆ₙₐ[ℂ] X => map h) hgf
      _ = NonUnitalStarAlgHom.id ℂ (AsymptoticAlgebra X) := map_id X
  have hFG :
      (map f).comp (map g) =
        NonUnitalStarAlgHom.id ℂ (AsymptoticAlgebra Y) := by
    calc
      (map f).comp (map g) = map (f.comp g) := (map_comp g f).symm
      _ = map (NonUnitalStarAlgHom.id ℂ Y) :=
        congrArg (fun h : Y →⋆ₙₐ[ℂ] Y => map h) hfg
      _ = NonUnitalStarAlgHom.id ℂ (AsymptoticAlgebra Y) := map_id Y
  exact StarAlgEquiv.ofNonUnitalStarAlgHom (map f) (map g) hGF hFG

private theorem alphaEquiv_toNonUnitalStarAlgHom
    {X : Type uX} {Y : Type uY}
    [NonUnitalCStarAlgebra X] [NonUnitalCStarAlgebra Y]
    (e : X ≃⋆ₐ[ℂ] Y) :
    (alphaEquiv e).toNonUnitalStarAlgHom =
      map e.toNonUnitalStarAlgHom := by
  rfl

private theorem iteratedMap_rightInverse
    (n : ℕ)
    {B : Type uB} {C : Type uC}
    [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
    (g : B →⋆ₙₐ[ℂ] C) (s : C →⋆ₙₐ[ℂ] B)
    (hs : g.comp s = NonUnitalStarAlgHom.id ℂ C) :
    (IteratedAsymptoticAlgebra.map n g).comp
        (IteratedAsymptoticAlgebra.map n s) =
      NonUnitalStarAlgHom.id ℂ (IteratedAsymptoticAlgebra n C) := by
  calc
    _ = IteratedAsymptoticAlgebra.map n (g.comp s) :=
      (IteratedAsymptoticAlgebra.map_comp n s g).symm
    _ = IteratedAsymptoticAlgebra.map n
        (NonUnitalStarAlgHom.id ℂ C) :=
      congrArg
        (fun h : C →⋆ₙₐ[ℂ] C =>
          IteratedAsymptoticAlgebra.map n h) hs
    _ = _ := IteratedAsymptoticAlgebra.map_id n C

/- Transport a literal pullback when both cospan legs are propositionally
equal. Cases on the equalities transport the pullback carrier together with
its inherited C-star dictionary. -/
private noncomputable def pullbackEquivOfEq
    {A : Type uA} {B : Type uB} {C : Type uC}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    [NonUnitalCStarAlgebra C]
    (f₀ : A →⋆ₙₐ[ℂ] C) (g₀ : B →⋆ₙₐ[ℂ] C)
    (f₁ : A →⋆ₙₐ[ℂ] C) (g₁ : B →⋆ₙₐ[ℂ] C)
    (hf : f₀ = f₁) (hg : g₀ = g₁) :
    NonUnitalCStarPullback.Pullback f₀ g₀ ≃⋆ₐ[ℂ]
      NonUnitalCStarPullback.Pullback f₁ g₁ := by
  cases hf
  cases hg
  exact StarAlgEquiv.refl ℂ _

private theorem fstHom_comp_pullbackEquivOfEq
    {A : Type uA} {B : Type uB} {C : Type uC}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    [NonUnitalCStarAlgebra C]
    (f₀ : A →⋆ₙₐ[ℂ] C) (g₀ : B →⋆ₙₐ[ℂ] C)
    (f₁ : A →⋆ₙₐ[ℂ] C) (g₁ : B →⋆ₙₐ[ℂ] C)
    (hf : f₀ = f₁) (hg : g₀ = g₁) :
    (NonUnitalCStarPullback.fstHom f₁ g₁).comp
        (pullbackEquivOfEq f₀ g₀ f₁ g₁ hf hg).toNonUnitalStarAlgHom =
      NonUnitalCStarPullback.fstHom f₀ g₀ := by
  cases hf
  cases hg
  rfl

private theorem sndHom_comp_pullbackEquivOfEq
    {A : Type uA} {B : Type uB} {C : Type uC}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    [NonUnitalCStarAlgebra C]
    (f₀ : A →⋆ₙₐ[ℂ] C) (g₀ : B →⋆ₙₐ[ℂ] C)
    (f₁ : A →⋆ₙₐ[ℂ] C) (g₁ : B →⋆ₙₐ[ℂ] C)
    (hf : f₀ = f₁) (hg : g₀ = g₁) :
    (NonUnitalCStarPullback.sndHom f₁ g₁).comp
        (pullbackEquivOfEq f₀ g₀ f₁ g₁ hf hg).toNonUnitalStarAlgHom =
      NonUnitalCStarPullback.sndHom f₀ g₀ := by
  cases hf
  cases hg
  rfl

/-- Every finite alpha iterate preserves a pullback whose right leg has a
star-homomorphic section. -/
@[no_expose]
noncomputable def iteratedSplitPullbackEquiv
    (n : ℕ)
    {A : Type uA} {B : Type uB} {C : Type uC}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    [NonUnitalCStarAlgebra C]
    (f : A →⋆ₙₐ[ℂ] C) (g : B →⋆ₙₐ[ℂ] C)
    (s : C →⋆ₙₐ[ℂ] B)
    (hs : g.comp s = NonUnitalStarAlgHom.id ℂ C) :
    IteratedAsymptoticAlgebra n
        (NonUnitalCStarPullback.Pullback f g) ≃⋆ₐ[ℂ]
      NonUnitalCStarPullback.Pullback
        (IteratedAsymptoticAlgebra.map n f)
        (IteratedAsymptoticAlgebra.map n g) := by
  induction n with
  | zero =>
      exact pullbackEquivOfEq f g
        (IteratedAsymptoticAlgebra.map 0 f)
        (IteratedAsymptoticAlgebra.map 0 g)
        (IteratedAsymptoticAlgebra.map_zero_stage f).symm
        (IteratedAsymptoticAlgebra.map_zero_stage g).symm
  | succ n ih =>
      let eStep := (alphaEquiv ih).trans
        (splitPullbackEquiv
          (IteratedAsymptoticAlgebra.map n f)
          (IteratedAsymptoticAlgebra.map n g)
          (IteratedAsymptoticAlgebra.map n s)
          (iteratedMap_rightInverse n g s hs))
      exact eStep.trans <| pullbackEquivOfEq
        (map (IteratedAsymptoticAlgebra.map n f))
        (map (IteratedAsymptoticAlgebra.map n g))
        (IteratedAsymptoticAlgebra.map (n + 1) f)
        (IteratedAsymptoticAlgebra.map (n + 1) g)
        (IteratedAsymptoticAlgebra.map_succ n f).symm
        (IteratedAsymptoticAlgebra.map_succ n g).symm

private theorem iteratedSplitPullbackEquiv_zero
    {A : Type uA} {B : Type uB} {C : Type uC}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    [NonUnitalCStarAlgebra C]
    (f : A →⋆ₙₐ[ℂ] C) (g : B →⋆ₙₐ[ℂ] C)
    (s : C →⋆ₙₐ[ℂ] B)
    (hs : g.comp s = NonUnitalStarAlgHom.id ℂ C) :
    iteratedSplitPullbackEquiv 0 f g s hs =
      pullbackEquivOfEq f g
        (IteratedAsymptoticAlgebra.map 0 f)
        (IteratedAsymptoticAlgebra.map 0 g)
        (IteratedAsymptoticAlgebra.map_zero_stage f).symm
        (IteratedAsymptoticAlgebra.map_zero_stage g).symm := by
  rfl

private theorem iteratedSplitPullbackEquiv_succ
    (n : ℕ)
    {A : Type uA} {B : Type uB} {C : Type uC}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    [NonUnitalCStarAlgebra C]
    (f : A →⋆ₙₐ[ℂ] C) (g : B →⋆ₙₐ[ℂ] C)
    (s : C →⋆ₙₐ[ℂ] B)
    (hs : g.comp s = NonUnitalStarAlgHom.id ℂ C) :
    iteratedSplitPullbackEquiv (n + 1) f g s hs =
      (((alphaEquiv (iteratedSplitPullbackEquiv n f g s hs)).trans
        (splitPullbackEquiv
          (IteratedAsymptoticAlgebra.map n f)
          (IteratedAsymptoticAlgebra.map n g)
          (IteratedAsymptoticAlgebra.map n s)
          (iteratedMap_rightInverse n g s hs))).trans
        (pullbackEquivOfEq
          (map (IteratedAsymptoticAlgebra.map n f))
          (map (IteratedAsymptoticAlgebra.map n g))
          (IteratedAsymptoticAlgebra.map (n + 1) f)
          (IteratedAsymptoticAlgebra.map (n + 1) g)
          (IteratedAsymptoticAlgebra.map_succ n f).symm
          (IteratedAsymptoticAlgebra.map_succ n g).symm)) := by
  rfl

theorem fstHom_comp_iteratedSplitPullbackEquiv
    (n : ℕ)
    {A : Type uA} {B : Type uB} {C : Type uC}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    [NonUnitalCStarAlgebra C]
    (f : A →⋆ₙₐ[ℂ] C) (g : B →⋆ₙₐ[ℂ] C)
    (s : C →⋆ₙₐ[ℂ] B)
    (hs : g.comp s = NonUnitalStarAlgHom.id ℂ C) :
    (NonUnitalCStarPullback.fstHom
        (IteratedAsymptoticAlgebra.map n f)
        (IteratedAsymptoticAlgebra.map n g)).comp
      (iteratedSplitPullbackEquiv n f g s hs).toNonUnitalStarAlgHom =
    IteratedAsymptoticAlgebra.map n
      (NonUnitalCStarPullback.fstHom f g) := by
  induction n with
  | zero =>
      rw [iteratedSplitPullbackEquiv_zero,
        fstHom_comp_pullbackEquivOfEq,
        IteratedAsymptoticAlgebra.map_zero_stage]
  | succ n ih =>
      rw [iteratedSplitPullbackEquiv_succ,
        ← StarAlgEquiv.toNonUnitalStarAlgHom_comp,
        ← NonUnitalStarAlgHom.comp_assoc,
        fstHom_comp_pullbackEquivOfEq,
        ← StarAlgEquiv.toNonUnitalStarAlgHom_comp,
        ← NonUnitalStarAlgHom.comp_assoc,
        fstHom_comp_splitPullbackEquiv,
        alphaEquiv_toNonUnitalStarAlgHom,
        ← map_comp, ih]
      exact (IteratedAsymptoticAlgebra.map_succ n
        (NonUnitalCStarPullback.fstHom f g)).symm

theorem sndHom_comp_iteratedSplitPullbackEquiv
    (n : ℕ)
    {A : Type uA} {B : Type uB} {C : Type uC}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    [NonUnitalCStarAlgebra C]
    (f : A →⋆ₙₐ[ℂ] C) (g : B →⋆ₙₐ[ℂ] C)
    (s : C →⋆ₙₐ[ℂ] B)
    (hs : g.comp s = NonUnitalStarAlgHom.id ℂ C) :
    (NonUnitalCStarPullback.sndHom
        (IteratedAsymptoticAlgebra.map n f)
        (IteratedAsymptoticAlgebra.map n g)).comp
      (iteratedSplitPullbackEquiv n f g s hs).toNonUnitalStarAlgHom =
    IteratedAsymptoticAlgebra.map n
      (NonUnitalCStarPullback.sndHom f g) := by
  induction n with
  | zero =>
      rw [iteratedSplitPullbackEquiv_zero,
        sndHom_comp_pullbackEquivOfEq,
        IteratedAsymptoticAlgebra.map_zero_stage]
  | succ n ih =>
      rw [iteratedSplitPullbackEquiv_succ,
        ← StarAlgEquiv.toNonUnitalStarAlgHom_comp,
        ← NonUnitalStarAlgHom.comp_assoc,
        sndHom_comp_pullbackEquivOfEq,
        ← StarAlgEquiv.toNonUnitalStarAlgHom_comp,
        ← NonUnitalStarAlgHom.comp_assoc,
        sndHom_comp_splitPullbackEquiv,
        alphaEquiv_toNonUnitalStarAlgHom,
        ← map_comp, ih]
      exact (IteratedAsymptoticAlgebra.map_succ n
        (NonUnitalCStarPullback.sndHom f g)).symm


end AsymptoticAlgebra
