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

public import MathlibExt.Analysis.VonNeumannAlgebra.Predual
public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual

/-!
# The actual ultraweak topology of a concrete von Neumann algebra

The weak copy retains the original algebra elements and operations. Its
topology is the stock `WeakBilin` topology for ordinary evaluation against
the actual normal-functional Banach space. The proved evaluation equivalence
identifies this copy with the stock weak-star dual of that same space.

Convergence and continuity are tested by the original functionals. The
original norm topology and the ultraweak topology remain distinct views.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter
open scoped Topology

namespace VonNeumannAlgebra

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The original evaluation pairing with the actual normal-functional space. -/
noncomputable def normalFunctionalPairing (M : VonNeumannAlgebra H) :
    M →ₗ[ℂ] normalFunctionalSpace M →ₗ[ℂ] ℂ where
  toFun x := (normalFunctionalEvaluation M x).toLinearMap
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro φ
    change (φ : StrongDual ℂ M) (x + y) =
      (φ : StrongDual ℂ M) x + (φ : StrongDual ℂ M) y
    exact map_add (φ : StrongDual ℂ M) x y
  map_smul' := by
    intro c x
    apply LinearMap.ext
    intro φ
    change (φ : StrongDual ℂ M) (c • x) =
      (RingHom.id ℂ) c • (φ : StrongDual ℂ M) x
    simp only [map_smul, RingHom.id_apply]

/-- The actual bilinear pairing evaluates the original continuous functional. -/
@[simp]
theorem normalFunctionalPairing_apply (M : VonNeumannAlgebra H) (x : M)
    (φ : normalFunctionalSpace M) :
    normalFunctionalPairing M x φ = (φ : StrongDual ℂ M) x :=
  rfl

/-- The actual normal-functional pairing separates the original algebra elements. -/
theorem normalFunctionalPairing_injective (M : VonNeumannAlgebra H) :
    Function.Injective (normalFunctionalPairing M) := by
  intro x y h
  apply normalFunctionalEvaluation_injective M
  apply ContinuousLinearMap.ext
  intro φ
  have he := congrArg (fun f : normalFunctionalSpace M →ₗ[ℂ] ℂ => f φ) h
  exact he

/-- Original algebra elements equipped with the evaluation-induced ultraweak topology. -/
noncomputable def Ultraweak (M : VonNeumannAlgebra H) : Type u :=
  WeakBilin (normalFunctionalPairing M)

/-- The weak copy retains the original additive monoid operations. -/
noncomputable instance ultraweakAddCommMonoid (M : VonNeumannAlgebra H) :
    AddCommMonoid (Ultraweak M) :=
  inferInstanceAs (AddCommMonoid (WeakBilin (normalFunctionalPairing M)))

/-- Complex scalar multiplication has its original algebra-element values. -/
noncomputable instance ultraweakSMul (M : VonNeumannAlgebra H) : SMul ℂ (Ultraweak M) :=
  inferInstanceAs (SMul ℂ (WeakBilin (normalFunctionalPairing M)))

/-- The original complex module structure is retained in the weak copy. -/
noncomputable instance ultraweakModule (M : VonNeumannAlgebra H) : Module ℂ (Ultraweak M) :=
  inferInstanceAs (Module ℂ (WeakBilin (normalFunctionalPairing M)))

/-- Multiplication, identity and ring operations are the original algebra operations. -/
noncomputable instance ultraweakRing (M : VonNeumannAlgebra H) : Ring (Ultraweak M) :=
  inferInstanceAs (Ring M)

/-- The weak copy uses the original complex algebra action. -/
noncomputable instance ultraweakAlgebra (M : VonNeumannAlgebra H) : Algebra ℂ (Ultraweak M) :=
  inferInstanceAs (Algebra ℂ M)

/-- The original operator involution is the weak copy's star operation. -/
noncomputable instance ultraweakStarRing (M : VonNeumannAlgebra H) : StarRing (Ultraweak M) :=
  inferInstanceAs (StarRing M)

/-- The original conjugate scalar law for star is preserved. -/
noncomputable instance ultraweakStarModule (M : VonNeumannAlgebra H) : StarModule ℂ (Ultraweak M) :=
  inferInstanceAs (StarModule ℂ M)

/-- The topology is exactly the stock weak topology of the actual evaluation pairing. -/
noncomputable instance ultraweakTopologicalSpace (M : VonNeumannAlgebra H) :
    TopologicalSpace (Ultraweak M) :=
  inferInstanceAs (TopologicalSpace (WeakBilin (normalFunctionalPairing M)))

/-- Forgetting the ultraweak view retains every original complex vector-space value. -/
noncomputable def ultraweakLinearEquiv (M : VonNeumannAlgebra H) : Ultraweak M ≃ₗ[ℂ] M where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The underlying value of a weak algebra element is its original value. -/
@[simp]
theorem ultraweakLinearEquiv_apply (M : VonNeumannAlgebra H) (x : Ultraweak M) :
    ultraweakLinearEquiv M x = x :=
  rfl

/-- Forgetting the weak topology preserves all original star-algebra operations. -/
noncomputable def ultraweakStarAlgEquiv (M : VonNeumannAlgebra H) : Ultraweak M ≃⋆ₐ[ℂ] M where
  toRingEquiv :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_mul' := fun _ _ => rfl }
  map_smul' _ _ := rfl
  map_star' _ := rfl

/-- The star-algebra and linear identifications retain the same original element. -/
@[simp]
theorem ultraweakStarAlgEquiv_apply (M : VonNeumannAlgebra H) (x : Ultraweak M) :
    ultraweakStarAlgEquiv M x = ultraweakLinearEquiv M x :=
  rfl

/-- Every actual normal functional is continuous on the ultraweak view. -/
theorem ultraweak_eval_continuous (M : VonNeumannAlgebra H) (φ : normalFunctionalSpace M) :
    Continuous fun x : Ultraweak M => (φ : StrongDual ℂ M) (ultraweakLinearEquiv M x) :=
  WeakBilin.eval_continuous (normalFunctionalPairing M) φ

/-- Continuity into the ultraweak copy is tested by all actual normal functionals. -/
theorem ultraweak_continuous_iff (M : VonNeumannAlgebra H)
    {A : Type v} [TopologicalSpace A] {f : A → Ultraweak M} :
    Continuous f ↔ ∀ φ : normalFunctionalSpace M,
      Continuous fun a => (φ : StrongDual ℂ M) (ultraweakLinearEquiv M (f a)) := by
  constructor
  · intro hf φ
    exact (ultraweak_eval_continuous M φ).comp hf
  · intro h
    exact WeakBilin.continuous_of_continuous_eval (normalFunctionalPairing M) h

/-- Convergence in the ultraweak copy is exactly convergence of its original normal evaluations. -/
theorem ultraweak_tendsto_iff (M : VonNeumannAlgebra H)
    {A : Type v} {l : Filter A} {f : A → Ultraweak M} {x : Ultraweak M} :
    Tendsto f l (𝓝 x) ↔ ∀ φ : normalFunctionalSpace M,
      Tendsto (fun a => (φ : StrongDual ℂ M) (ultraweakLinearEquiv M (f a))) l
        (𝓝 ((φ : StrongDual ℂ M) (ultraweakLinearEquiv M x))) :=
  WeakBilin.tendsto_iff_forall_eval_tendsto
    (normalFunctionalPairing M) (normalFunctionalPairing_injective M)

/-- Addition of the original algebra elements is jointly ultraweak continuous. -/
noncomputable instance ultraweakContinuousAdd (M : VonNeumannAlgebra H) : ContinuousAdd (Ultraweak M) where
  continuous_add := by
    apply (ultraweak_continuous_iff M).2
    intro φ
    have hf := (ultraweak_eval_continuous M φ).comp
      (continuous_fst : Continuous fun p : Ultraweak M × Ultraweak M => p.1)
    have hg := (ultraweak_eval_continuous M φ).comp
      (continuous_snd : Continuous fun p : Ultraweak M × Ultraweak M => p.2)
    have he :
        (fun p : Ultraweak M × Ultraweak M =>
          (φ : StrongDual ℂ M) (ultraweakLinearEquiv M (p.1 + p.2))) =
        ((fun x : Ultraweak M => (φ : StrongDual ℂ M) (ultraweakLinearEquiv M x)) ∘ Prod.fst) +
          ((fun x : Ultraweak M => (φ : StrongDual ℂ M) (ultraweakLinearEquiv M x)) ∘ Prod.snd) := by
      funext p
      rw [Pi.add_apply]
      simp only [Function.comp_apply, map_add]
    rw [he]
    exact hf.add hg

/-- The original complex scalar action is jointly ultraweak continuous. -/
noncomputable instance ultraweakContinuousSMul (M : VonNeumannAlgebra H) :
    ContinuousSMul ℂ (Ultraweak M) where
  continuous_smul := by
    apply (ultraweak_continuous_iff M).2
    intro φ
    have hf := (ultraweak_eval_continuous M φ).comp
      (continuous_snd : Continuous fun p : ℂ × Ultraweak M => p.2)
    have hc : Continuous fun p : ℂ × Ultraweak M => p.1 := continuous_fst
    have he :
        (fun p : ℂ × Ultraweak M =>
          (φ : StrongDual ℂ M) (ultraweakLinearEquiv M (p.1 • p.2))) =
        (fun p : ℂ × Ultraweak M => p.1) •
          ((fun x : Ultraweak M => (φ : StrongDual ℂ M) (ultraweakLinearEquiv M x)) ∘ Prod.snd) := by
      funext p
      rw [Pi.smul_apply']
      simp only [Function.comp_apply, map_smul]
    rw [he]
    exact hc.smul hf

/-- The actual evaluation equivalence identifies the ultraweak copy with the stock weak-star dual. -/
noncomputable def ultraweakWeakDualHomeomorph (M : VonNeumannAlgebra H) :
    Ultraweak M ≃ₜ WeakDual ℂ (normalFunctionalSpace M) :=
  let e : Ultraweak M ≃ WeakDual ℂ (normalFunctionalSpace M) :=
    { toFun := fun x =>
        (normalFunctionalEvaluationEquiv M (ultraweakLinearEquiv M x)).toWeakDual
      invFun := fun F =>
        (ultraweakLinearEquiv M).symm ((normalFunctionalEvaluationEquiv M).symm F.toStrongDual)
      left_inv := by
        intro x
        change (ultraweakLinearEquiv M).symm
          ((normalFunctionalEvaluationEquiv M).symm
            ((normalFunctionalEvaluationEquiv M (ultraweakLinearEquiv M x)).toWeakDual.toStrongDual)) = x
        rw [StrongDual.toStrongDual_toWeakDual, LinearIsometryEquiv.symm_apply_apply,
          LinearEquiv.symm_apply_apply]
      right_inv := by
        intro F
        change (normalFunctionalEvaluationEquiv M
          (ultraweakLinearEquiv M
            ((ultraweakLinearEquiv M).symm
              ((normalFunctionalEvaluationEquiv M).symm F.toStrongDual)))).toWeakDual = F
        rw [LinearEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply,
          WeakDual.toWeakDual_toStrongDual] }
  ⟨e, by
    change Continuous fun x : Ultraweak M =>
      (normalFunctionalEvaluationEquiv M (ultraweakLinearEquiv M x)).toWeakDual
    apply WeakDual.continuous_of_continuous_eval
    intro φ
    simpa only [StrongDual.toWeakDual_apply, normalFunctionalEvaluationEquiv_apply] using
      ultraweak_eval_continuous M φ,
    by
      change Continuous fun F : WeakDual ℂ (normalFunctionalSpace M) =>
        (ultraweakLinearEquiv M).symm ((normalFunctionalEvaluationEquiv M).symm F.toStrongDual)
      apply (ultraweak_continuous_iff M).2
      intro φ
      have hfun :
          (fun F : WeakDual ℂ (normalFunctionalSpace M) =>
            (φ : StrongDual ℂ M)
              ((normalFunctionalEvaluationEquiv M).symm F.toStrongDual)) =
          (fun F : WeakDual ℂ (normalFunctionalSpace M) => F φ) := by
        funext F
        have he := congrArg (fun g : StrongDual ℂ (normalFunctionalSpace M) => g φ)
          ((normalFunctionalEvaluationEquiv M).apply_symm_apply F.toStrongDual)
        simpa only [normalFunctionalEvaluationEquiv_apply, WeakDual.toStrongDual_apply] using he
      change Continuous fun F : WeakDual ℂ (normalFunctionalSpace M) =>
        (φ : StrongDual ℂ M) ((normalFunctionalEvaluationEquiv M).symm F.toStrongDual)
      rw [hfun]
      exact WeakDual.eval_continuous φ⟩

/-- The homeomorphism uses the original normal-functional evaluation on every element. -/
@[simp]
theorem ultraweakWeakDualHomeomorph_apply (M : VonNeumannAlgebra H) (x : Ultraweak M)
    (φ : normalFunctionalSpace M) :
    ultraweakWeakDualHomeomorph M x φ = (φ : StrongDual ℂ M) (ultraweakLinearEquiv M x) :=
  rfl

/-- The actual ultraweak topology is Hausdorff by its proved weak-star dual identification. -/
noncomputable instance ultraweakT2Space (M : VonNeumannAlgebra H) : T2Space (Ultraweak M) :=
  (ultraweakWeakDualHomeomorph M).isEmbedding.t2Space

/-- The identity from the original norm topology into the ultraweak topology is continuous. -/
theorem continuous_toUltraweak (M : VonNeumannAlgebra H) :
    Continuous (ultraweakLinearEquiv M).symm := by
  apply (ultraweak_continuous_iff M).2
  intro φ
  simpa only [LinearEquiv.apply_symm_apply] using (φ : StrongDual ℂ M).continuous

end VonNeumannAlgebra
