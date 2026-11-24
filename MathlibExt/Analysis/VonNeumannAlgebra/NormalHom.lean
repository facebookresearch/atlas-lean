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

public import MathlibExt.Analysis.VonNeumannAlgebra.UltraweakDual
public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict

/-!
# Compositional normal homomorphisms and actual predual pullback

Normal homomorphisms retain the original unital complex star maps and their
ultraweak continuity. Their literal functional pullback is certified by the
weak representation theorem and restricted to the actual predual spaces.
Identity and composition act on the original algebra and functional values.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped CStarAlgebra

namespace VonNeumannAlgebra

noncomputable section

universe u v w z

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- An actual unital complex star algebra homomorphism that is ultraweak continuous. -/
structure NormalStarAlgHom (M : VonNeumannAlgebra H) (N : VonNeumannAlgebra K) where
  /-- The original unital complex star algebra homomorphism on the concrete carriers. -/
  toStarAlgHom : M →⋆ₐ[ℂ] N
  /-- Continuity of the same map for the actual evaluation-induced ultraweak topologies. -/
  continuous_ultraweak :
    Continuous fun x : Ultraweak M =>
      (ultraweakLinearEquiv N).symm (toStarAlgHom (ultraweakLinearEquiv M x))

namespace NormalStarAlgHom

variable {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}

/-- The original algebra map determines a normal homomorphism. -/
@[ext]
theorem ext {f g : NormalStarAlgHom M N} (h : f.toStarAlgHom = g.toStarAlgHom) : f = g := by
  cases f
  cases g
  cases h
  rfl

@[macro_inline]
instance : FunLike (NormalStarAlgHom M N) M N where
  coe f := f.toStarAlgHom
  coe_injective f g h := by
    have hmap : f.toStarAlgHom = g.toStarAlgHom :=
      DFunLike.ext _ _ fun x => congrFun h x
    exact ext hmap

instance : Coe (NormalStarAlgHom M N) (M →⋆ₐ[ℂ] N) := ⟨toStarAlgHom⟩

instance : AlgHomClass (NormalStarAlgHom M N) ℂ M N where
  map_one f := map_one f.toStarAlgHom
  map_mul f := map_mul f.toStarAlgHom
  map_zero f := map_zero f.toStarAlgHom
  map_add f := map_add f.toStarAlgHom
  commutes f := AlgHomClass.commutes f.toStarAlgHom

instance : StarHomClass (NormalStarAlgHom M N) M N where
  map_star f := map_star f.toStarAlgHom

/-- The forgetful algebra map evaluates at the same original element. -/
@[simp]
theorem toStarAlgHom_apply (f : NormalStarAlgHom M N) (x : M) : f.toStarAlgHom x = f x :=
  rfl

/-- The underlying complex star map is bounded for the original C-star norms. -/
def toContinuousLinearMap (f : NormalStarAlgHom M N) : M →L[ℂ] N :=
  ⟨LinearMap.ofClass f.toStarAlgHom, map_continuous f.toStarAlgHom⟩

/-- The original bounded map keeps the original normal-homomorphism values. -/
@[simp]
theorem toContinuousLinearMap_apply (f : NormalStarAlgHom M N) (x : M) :
    f.toContinuousLinearMap x = f x :=
  rfl

/-- The same original map, continuously bundled between the actual ultraweak views. -/
def ultraweakMap (f : NormalStarAlgHom M N) : Ultraweak M →L[ℂ] Ultraweak N where
  toLinearMap := (ultraweakLinearEquiv N).symm.toLinearMap.comp
    ((LinearMap.ofClass f.toStarAlgHom).comp (ultraweakLinearEquiv M).toLinearMap)
  cont := f.continuous_ultraweak

/-- The ultraweak map retains both original value identifications. -/
@[simp]
theorem ultraweakMap_apply (f : NormalStarAlgHom M N) (x : Ultraweak M) :
    f.ultraweakMap x = (ultraweakLinearEquiv N).symm (f (ultraweakLinearEquiv M x)) :=
  rfl

/-- The identity normal homomorphism uses the identity original algebra map. -/
def id (M : VonNeumannAlgebra H) : NormalStarAlgHom M M where
  toStarAlgHom := StarAlgHom.id ℂ M
  continuous_ultraweak := by
    have hfun :
        (fun x : Ultraweak M => (ultraweakLinearEquiv M).symm
          (StarAlgHom.id ℂ M (ultraweakLinearEquiv M x))) =
        (_root_.id : Ultraweak M → Ultraweak M) := by
      funext x
      change (ultraweakLinearEquiv M).symm (ultraweakLinearEquiv M x) = x
      exact (ultraweakLinearEquiv M).symm_apply_apply x
    rw [hfun]
    exact continuous_id

/-- Identity acts by the same original element. -/
@[simp]
theorem id_apply (x : M) : id M x = x :=
  rfl

variable {L : Type w} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
variable {P : VonNeumannAlgebra L}

/-- Compose normal homomorphisms by the original star-algebra composition. -/
def comp (g : NormalStarAlgHom N P) (f : NormalStarAlgHom M N) : NormalStarAlgHom M P where
  toStarAlgHom := g.toStarAlgHom.comp f.toStarAlgHom
  continuous_ultraweak := by
    have hfun :
        (fun x : Ultraweak M => (ultraweakLinearEquiv P).symm
          ((g.toStarAlgHom.comp f.toStarAlgHom) (ultraweakLinearEquiv M x))) =
        ((fun y : Ultraweak N => (ultraweakLinearEquiv P).symm
          (g.toStarAlgHom (ultraweakLinearEquiv N y))) ∘
          fun x : Ultraweak M => (ultraweakLinearEquiv N).symm
            (f.toStarAlgHom (ultraweakLinearEquiv M x))) := by
      funext x
      change (ultraweakLinearEquiv P).symm
          (g.toStarAlgHom (f.toStarAlgHom (ultraweakLinearEquiv M x))) =
        (ultraweakLinearEquiv P).symm (g.toStarAlgHom (ultraweakLinearEquiv N
          ((ultraweakLinearEquiv N).symm (f.toStarAlgHom (ultraweakLinearEquiv M x)))))
      exact congrArg (fun y : N => (ultraweakLinearEquiv P).symm (g.toStarAlgHom y))
        ((ultraweakLinearEquiv N).apply_symm_apply
          (f.toStarAlgHom (ultraweakLinearEquiv M x))).symm
    rw [hfun]
    exact g.continuous_ultraweak.comp f.continuous_ultraweak

/-- Composition applies the original maps in forward order. -/
@[simp]
theorem comp_apply (g : NormalStarAlgHom N P) (f : NormalStarAlgHom M N) (x : M) :
    g.comp f x = g (f x) :=
  rfl

/-- The target identity preserves a normal homomorphism. -/
@[simp]
theorem id_comp (f : NormalStarAlgHom M N) : (id N).comp f = f := by
  apply ext
  ext x
  rfl

/-- The source identity preserves a normal homomorphism. -/
@[simp]
theorem comp_id (f : NormalStarAlgHom M N) : f.comp (id M) = f := by
  apply ext
  ext x
  rfl

variable {QH : Type z} [NormedAddCommGroup QH] [InnerProductSpace ℂ QH] [CompleteSpace QH]
variable {Q : VonNeumannAlgebra QH}

/-- Normal-map composition is associative on the original algebra maps. -/
theorem comp_assoc (h : NormalStarAlgHom P Q) (g : NormalStarAlgHom N P)
    (f : NormalStarAlgHom M N) : (h.comp g).comp f = h.comp (g.comp f) := by
  apply ext
  ext x
  rfl

/-- Actual pullback preserves the original closed normal-functional subtype. -/
theorem predualPullback_mem (f : NormalStarAlgHom M N) (φ : normalFunctionalSpace N) :
    (φ : StrongDual ℂ N).comp f.toContinuousLinearMap ∈ normalFunctionalSpace M := by
  apply mem_normalFunctionalSpace_of_ultraweak_continuous
  have hfun :
      (fun x : Ultraweak M => ((φ : StrongDual ℂ N).comp f.toContinuousLinearMap)
        (ultraweakLinearEquiv M x)) =
      ((fun y : Ultraweak N => (φ : StrongDual ℂ N) (ultraweakLinearEquiv N y)) ∘
        fun x : Ultraweak M => (ultraweakLinearEquiv N).symm
          (f.toStarAlgHom (ultraweakLinearEquiv M x))) := by
    funext x
    change (φ : StrongDual ℂ N) (f.toStarAlgHom (ultraweakLinearEquiv M x)) =
      (φ : StrongDual ℂ N) (ultraweakLinearEquiv N
        ((ultraweakLinearEquiv N).symm (f.toStarAlgHom (ultraweakLinearEquiv M x))))
    exact congrArg (fun y : N => (φ : StrongDual ℂ N) y)
      ((ultraweakLinearEquiv N).apply_symm_apply
        (f.toStarAlgHom (ultraweakLinearEquiv M x))).symm
  rw [hfun]
  exact (ultraweak_eval_continuous N φ).comp f.continuous_ultraweak

/-- The literal bounded functional pullback restricted to the actual normal-functional spaces. -/
def predualPullback (f : NormalStarAlgHom M N) :
    normalFunctionalSpace N →L[ℂ] normalFunctionalSpace M :=
  let B := (ContinuousLinearMap.compL ℂ M N ℂ).flip f.toContinuousLinearMap
  let T := B.comp (normalFunctionalSpace N).subtypeL
  T.codRestrict (normalFunctionalSpace M) fun φ => f.predualPullback_mem φ

/-- The actual predual pullback is ordinary functional precomposition on original elements. -/
@[simp]
theorem predualPullback_apply (f : NormalStarAlgHom M N) (φ : normalFunctionalSpace N) (x : M) :
    (f.predualPullback φ : StrongDual ℂ M) x = (φ : StrongDual ℂ N) (f x) :=
  rfl

/-- Identity induces identity on the actual predual. -/
@[simp]
theorem predualPullback_id : (id M).predualPullback = ContinuousLinearMap.id ℂ _ := by
  apply ContinuousLinearMap.ext
  intro φ
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  rfl

/-- Functional pullback reverses the original normal-map composition. -/
theorem predualPullback_comp (g : NormalStarAlgHom N P) (f : NormalStarAlgHom M N) :
    (g.comp f).predualPullback = f.predualPullback.comp g.predualPullback := by
  apply ContinuousLinearMap.ext
  intro φ
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  simp only [predualPullback_apply, ContinuousLinearMap.comp_apply, comp_apply]

end NormalStarAlgHom

end

end VonNeumannAlgebra
