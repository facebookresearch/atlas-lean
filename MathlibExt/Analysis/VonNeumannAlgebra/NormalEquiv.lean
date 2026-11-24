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

public import MathlibExt.Analysis.VonNeumannAlgebra.NormalHom
public import Mathlib.Topology.Algebra.Module.Equiv.Basic

/-!
# Compositional normal equivalences and actual predual automorphisms

Normal equivalences retain both original star maps and their ultraweak
continuity. Their identity, inverse and composition form the actual normal
automorphism group. Functional pullback gives the continuous linear predual
equivalence, and inverse pullback gives its covariant automorphism action.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VonNeumannAlgebra

noncomputable section

universe u v w

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- An actual complex star algebra equivalence that is ultraweak continuous in both directions. -/
structure NormalStarAlgEquiv (M : VonNeumannAlgebra H) (N : VonNeumannAlgebra K) where
  /-- The original complex star algebra equivalence of the concrete carriers. -/
  toStarAlgEquiv : M ≃⋆ₐ[ℂ] N
  /-- Ultraweak continuity of the same original forward map. -/
  continuous_ultraweak :
    Continuous fun x : Ultraweak M =>
      (ultraweakLinearEquiv N).symm (toStarAlgEquiv (ultraweakLinearEquiv M x))
  /-- Ultraweak continuity of the same original inverse map. -/
  continuous_ultraweak_symm :
    Continuous fun x : Ultraweak N =>
      (ultraweakLinearEquiv M).symm (toStarAlgEquiv.symm (ultraweakLinearEquiv N x))

namespace NormalStarAlgEquiv

variable {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}

/-- The original star equivalence determines both maps of a normal equivalence. -/
@[ext]
theorem ext {f g : NormalStarAlgEquiv M N}
    (h : f.toStarAlgEquiv = g.toStarAlgEquiv) : f = g := by
  cases f
  cases g
  cases h
  rfl

instance : EquivLike (NormalStarAlgEquiv M N) M N where
  coe f := f.toStarAlgEquiv
  inv f := f.toStarAlgEquiv.symm
  left_inv f := f.toStarAlgEquiv.left_inv
  right_inv f := f.toStarAlgEquiv.right_inv
  coe_injective' f g h _ := by
    have hmap : f.toStarAlgEquiv = g.toStarAlgEquiv :=
      DFunLike.ext _ _ fun x => congrFun h x
    exact ext hmap

instance : Coe (NormalStarAlgEquiv M N) (M ≃⋆ₐ[ℂ] N) := ⟨toStarAlgEquiv⟩

instance : AlgEquivClass (NormalStarAlgEquiv M N) ℂ M N where
  map_mul f := map_mul f.toStarAlgEquiv
  map_add f := map_add f.toStarAlgEquiv
  commutes f := AlgHomClass.commutes f.toStarAlgEquiv

instance : StarHomClass (NormalStarAlgEquiv M N) M N where
  map_star f := map_star f.toStarAlgEquiv

/-- The forgetful star equivalence uses the same original value. -/
@[simp]
theorem toStarAlgEquiv_apply (f : NormalStarAlgEquiv M N) (x : M) :
    f.toStarAlgEquiv x = f x :=
  rfl

/-- Forget the inverse map while retaining the actual normal homomorphism. -/
def toNormalStarAlgHom (f : NormalStarAlgEquiv M N) : NormalStarAlgHom M N where
  toStarAlgHom := f.toStarAlgEquiv.toStarAlgHom
  continuous_ultraweak := f.continuous_ultraweak

/-- The normal homomorphism conversion preserves original values. -/
@[simp]
theorem toNormalStarAlgHom_apply (f : NormalStarAlgEquiv M N) (x : M) :
    f.toNormalStarAlgHom x = f x :=
  rfl

/-- The identity normal equivalence on the original algebra. -/
def refl (M : VonNeumannAlgebra H) : NormalStarAlgEquiv M M where
  toStarAlgEquiv := StarAlgEquiv.refl ℂ M
  continuous_ultraweak := by
    have hfun :
        (fun x : Ultraweak M => (ultraweakLinearEquiv M).symm
          (StarAlgEquiv.refl ℂ M (ultraweakLinearEquiv M x))) =
        (_root_.id : Ultraweak M → Ultraweak M) := by
      funext x
      change (ultraweakLinearEquiv M).symm (ultraweakLinearEquiv M x) = x
      exact (ultraweakLinearEquiv M).symm_apply_apply x
    rw [hfun]
    exact continuous_id
  continuous_ultraweak_symm := by
    have hfun :
        (fun x : Ultraweak M => (ultraweakLinearEquiv M).symm
          ((StarAlgEquiv.refl ℂ M).symm (ultraweakLinearEquiv M x))) =
        (_root_.id : Ultraweak M → Ultraweak M) := by
      funext x
      change (ultraweakLinearEquiv M).symm (ultraweakLinearEquiv M x) = x
      exact (ultraweakLinearEquiv M).symm_apply_apply x
    rw [hfun]
    exact continuous_id

/-- Identity acts by the original algebra element. -/
@[simp]
theorem refl_apply (x : M) : refl M x = x :=
  rfl

/-- Invert a normal equivalence using the same original inverse map. -/
def symm (f : NormalStarAlgEquiv M N) : NormalStarAlgEquiv N M where
  toStarAlgEquiv := f.toStarAlgEquiv.symm
  continuous_ultraweak := f.continuous_ultraweak_symm
  continuous_ultraweak_symm := by
    have hfun :
        (fun x : Ultraweak M => (ultraweakLinearEquiv N).symm
          (f.toStarAlgEquiv.symm.symm (ultraweakLinearEquiv M x))) =
        (fun x : Ultraweak M => (ultraweakLinearEquiv N).symm
          (f.toStarAlgEquiv (ultraweakLinearEquiv M x))) := by
      funext x
      exact congrArg (fun e : M ≃⋆ₐ[ℂ] N =>
        (ultraweakLinearEquiv N).symm (e (ultraweakLinearEquiv M x)))
        f.toStarAlgEquiv.symm_symm
    rw [hfun]
    exact f.continuous_ultraweak

/-- The normal inverse and original inverse have the same values. -/
theorem symm_apply (f : NormalStarAlgEquiv M N) (x : N) :
    f.symm x = f.toStarAlgEquiv.symm x :=
  rfl

/-- The original inverse recovers the source element. -/
@[simp]
theorem symm_apply_apply (f : NormalStarAlgEquiv M N) (x : M) : f.symm (f x) = x :=
  f.toStarAlgEquiv.symm_apply_apply x

/-- The original forward map recovers the target element. -/
@[simp]
theorem apply_symm_apply (f : NormalStarAlgEquiv M N) (x : N) : f (f.symm x) = x :=
  f.toStarAlgEquiv.apply_symm_apply x

/-- Inversion twice retains the same normal equivalence. -/
@[simp]
theorem symm_symm (f : NormalStarAlgEquiv M N) : f.symm.symm = f := by
  apply ext
  exact f.toStarAlgEquiv.symm_symm

variable {L : Type w} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
variable {P : VonNeumannAlgebra L}

/-- Compose normal equivalences by the same original forward and inverse maps. -/
def trans (f : NormalStarAlgEquiv M N) (g : NormalStarAlgEquiv N P) :
    NormalStarAlgEquiv M P where
  toStarAlgEquiv := f.toStarAlgEquiv.trans g.toStarAlgEquiv
  continuous_ultraweak := by
    have hfun :
        (fun x : Ultraweak M => (ultraweakLinearEquiv P).symm
          ((f.toStarAlgEquiv.trans g.toStarAlgEquiv) (ultraweakLinearEquiv M x))) =
        ((fun y : Ultraweak N => (ultraweakLinearEquiv P).symm
          (g.toStarAlgEquiv (ultraweakLinearEquiv N y))) ∘
          fun x : Ultraweak M => (ultraweakLinearEquiv N).symm
            (f.toStarAlgEquiv (ultraweakLinearEquiv M x))) := by
      funext x
      change (ultraweakLinearEquiv P).symm
          (g.toStarAlgEquiv (f.toStarAlgEquiv (ultraweakLinearEquiv M x))) =
        (ultraweakLinearEquiv P).symm (g.toStarAlgEquiv (ultraweakLinearEquiv N
          ((ultraweakLinearEquiv N).symm (f.toStarAlgEquiv (ultraweakLinearEquiv M x)))))
      exact congrArg (fun y : N => (ultraweakLinearEquiv P).symm (g.toStarAlgEquiv y))
        ((ultraweakLinearEquiv N).apply_symm_apply
          (f.toStarAlgEquiv (ultraweakLinearEquiv M x))).symm
    rw [hfun]
    exact g.continuous_ultraweak.comp f.continuous_ultraweak
  continuous_ultraweak_symm := by
    have hfun :
        (fun x : Ultraweak P => (ultraweakLinearEquiv M).symm
          ((f.toStarAlgEquiv.trans g.toStarAlgEquiv).symm (ultraweakLinearEquiv P x))) =
        ((fun y : Ultraweak N => (ultraweakLinearEquiv M).symm
          (f.toStarAlgEquiv.symm (ultraweakLinearEquiv N y))) ∘
          fun x : Ultraweak P => (ultraweakLinearEquiv N).symm
            (g.toStarAlgEquiv.symm (ultraweakLinearEquiv P x))) := by
      funext x
      change (ultraweakLinearEquiv M).symm
          (f.toStarAlgEquiv.symm (g.toStarAlgEquiv.symm (ultraweakLinearEquiv P x))) =
        (ultraweakLinearEquiv M).symm (f.toStarAlgEquiv.symm (ultraweakLinearEquiv N
          ((ultraweakLinearEquiv N).symm (g.toStarAlgEquiv.symm (ultraweakLinearEquiv P x)))))
      exact congrArg (fun y : N => (ultraweakLinearEquiv M).symm (f.toStarAlgEquiv.symm y))
        ((ultraweakLinearEquiv N).apply_symm_apply
          (g.toStarAlgEquiv.symm (ultraweakLinearEquiv P x))).symm
    rw [hfun]
    exact f.continuous_ultraweak_symm.comp g.continuous_ultraweak_symm

/-- Forward composition uses the original algebra values in order. -/
@[simp]
theorem trans_apply (f : NormalStarAlgEquiv M N) (g : NormalStarAlgEquiv N P) (x : M) :
    f.trans g x = g (f x) :=
  rfl

/-- Normal automorphisms form a group under the original function composition. -/
instance automorphismGroup : Group (NormalStarAlgEquiv M M) where
  one := refl M
  mul f g := g.trans f
  inv f := f.symm
  mul_assoc f g h := by
    apply NormalStarAlgEquiv.ext
    apply StarAlgEquiv.ext
    intro x
    rfl
  one_mul f := by
    apply NormalStarAlgEquiv.ext
    apply StarAlgEquiv.ext
    intro x
    rfl
  mul_one f := by
    apply NormalStarAlgEquiv.ext
    apply StarAlgEquiv.ext
    intro x
    rfl
  inv_mul_cancel f := by
    apply NormalStarAlgEquiv.ext
    apply StarAlgEquiv.ext
    intro x
    exact f.toStarAlgEquiv.symm_apply_apply x

/-- The normal automorphism identity has the original identity value. -/
@[simp]
theorem one_apply (x : M) : (1 : NormalStarAlgEquiv M M) x = x :=
  rfl

/-- Normal automorphism multiplication is original function composition. -/
@[simp]
theorem mul_apply (f g : NormalStarAlgEquiv M M) (x : M) : (f * g) x = f (g x) :=
  rfl

/-- The normal automorphism inverse is its original normal inverse. -/
@[simp]
theorem inv_apply (f : NormalStarAlgEquiv M M) (x : M) : f⁻¹ x = f.symm x :=
  rfl

/-- Forget normality as a group homomorphism on the same original automorphisms. -/
def toStarAlgAutHom (M : VonNeumannAlgebra H) :
    NormalStarAlgEquiv M M →* (M ≃⋆ₐ[ℂ] M) where
  toFun := toStarAlgEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Functional pullback is the actual continuous linear equivalence of predual spaces. -/
def predualEquiv (f : NormalStarAlgEquiv M N) :
    normalFunctionalSpace N ≃L[ℂ] normalFunctionalSpace M where
  toLinearEquiv :=
    { toFun := f.toNormalStarAlgHom.predualPullback
      invFun := f.symm.toNormalStarAlgHom.predualPullback
      left_inv := by
        intro φ
        apply Subtype.ext
        apply ContinuousLinearMap.ext
        intro x
        simp only [NormalStarAlgHom.predualPullback_apply, toNormalStarAlgHom_apply,
          apply_symm_apply]
      right_inv := by
        intro φ
        apply Subtype.ext
        apply ContinuousLinearMap.ext
        intro x
        simp only [NormalStarAlgHom.predualPullback_apply, toNormalStarAlgHom_apply,
          symm_apply_apply]
      map_add' := map_add f.toNormalStarAlgHom.predualPullback
      map_smul' := map_smul f.toNormalStarAlgHom.predualPullback }
  continuous_toFun := f.toNormalStarAlgHom.predualPullback.continuous
  continuous_invFun := f.symm.toNormalStarAlgHom.predualPullback.continuous

/-- The predual equivalence evaluates by the same original functional pullback. -/
@[simp]
theorem predualEquiv_apply (f : NormalStarAlgEquiv M N) (φ : normalFunctionalSpace N) (x : M) :
    (f.predualEquiv φ : StrongDual ℂ M) x = (φ : StrongDual ℂ N) (f x) :=
  f.toNormalStarAlgHom.predualPullback_apply φ x

/-- Inverse pullback gives the covariant action of actual normal automorphisms on the predual. -/
def predualActionHom (M : VonNeumannAlgebra H) :
    NormalStarAlgEquiv M M →*
      (normalFunctionalSpace M ≃L[ℂ] normalFunctionalSpace M) where
  toFun f := f.symm.predualEquiv
  map_one' := by
    apply ContinuousLinearEquiv.ext
    funext φ
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro x
    change (((1 : NormalStarAlgEquiv M M).symm).predualEquiv φ : StrongDual ℂ M) x =
      (φ : StrongDual ℂ M) x
    rw [predualEquiv_apply]
    rfl
  map_mul' f g := by
    apply ContinuousLinearEquiv.ext
    funext φ
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro x
    change ((f * g).symm.predualEquiv φ : StrongDual ℂ M) x =
      (f.symm.predualEquiv (g.symm.predualEquiv φ) : StrongDual ℂ M) x
    rw [predualEquiv_apply, predualEquiv_apply, predualEquiv_apply]
    change (φ : StrongDual ℂ M) ((g.toStarAlgEquiv.trans f.toStarAlgEquiv).symm x) =
      (φ : StrongDual ℂ M) (g.toStarAlgEquiv.symm (f.toStarAlgEquiv.symm x))
    rw [StarAlgEquiv.symm_trans_apply]

/-- The covariant predual action uses the original inverse automorphism in evaluation. -/
@[simp]
theorem predualActionHom_apply (f : NormalStarAlgEquiv M M)
    (φ : normalFunctionalSpace M) (x : M) :
    (predualActionHom M f φ : StrongDual ℂ M) x = (φ : StrongDual ℂ M) (f.symm x) :=
  f.symm.predualEquiv_apply φ x

end NormalStarAlgEquiv

end

end VonNeumannAlgebra
