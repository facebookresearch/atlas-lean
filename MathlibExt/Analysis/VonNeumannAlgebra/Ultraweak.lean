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
# Evaluation topology and weak-star realization of a von Neumann algebra

For a concrete von Neumann algebra `M ⊆ B(H)` on a complete complex Hilbert space, let `M_*` be
the norm-closed span of vector functionals. The pairing is `⟨x,φ⟩=φ(x)` for `x ∈ M`, `φ ∈ M_*`.
It separates algebra elements and induces the ultraweak topology `σ(M,M_*)`.

The algebra with this topology retains its algebraic operations. Continuity and convergence are
tested by every evaluation `φ(x)`; addition and complex scalar multiplication are jointly
continuous. The evaluation map gives a homeomorphism to the weak-star dual `(M_*)*`, and hence
the ultraweak space is Hausdorff.

The identity from the operator-norm topology to the ultraweak topology is continuous. These are
two topologies on the algebra; no continuity of the inverse identity is asserted.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter
open scoped Topology

namespace VonNeumannAlgebra

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Evaluation pairing with the normal-functional Banach space.** Let `H` be a complete
complex Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write
`ω_(ξ,η)(x)=⟨ξ,xη⟩` for its vector functionals. Let `M_*` be their norm-closed complex
span in the continuous dual `M*`. `normalFunctionalPairing M : M →ₗ[ℂ] M_* →ₗ[ℂ] ℂ` is the
bilinear pairing `(x,φ) ↦ φ(x)`. -/
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

/-- **Value of the normal-functional evaluation pairing.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for
its vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. for `x ∈ M` and `φ ∈ M_*`, `normalFunctionalPairing M x φ=φ(x)`. -/
@[simp]
theorem normalFunctionalPairing_apply (M : VonNeumannAlgebra H) (x : M)
    (φ : normalFunctionalSpace M) :
    normalFunctionalPairing M x φ = (φ : StrongDual ℂ M) x :=
  rfl

/-- **Normal-functional evaluation separates algebra elements.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for
its vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. the map `x ↦ (φ ↦ φ(x))` is injective on `M`; equality of all normal evaluations
implies equality of algebra elements. -/
theorem normalFunctionalPairing_injective (M : VonNeumannAlgebra H) :
    Function.Injective (normalFunctionalPairing M) := by
  intro x y h
  apply normalFunctionalEvaluation_injective M
  apply ContinuousLinearMap.ext
  intro φ
  have he := congrArg (fun f : normalFunctionalSpace M →ₗ[ℂ] ℂ => f φ) h
  exact he

/-- **Von Neumann algebra with its evaluation-induced topology.** Let `H` be a complete
complex Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write
`ω_(ξ,η)(x)=⟨ξ,xη⟩` for its vector functionals. Let `M_*` be their norm-closed complex
span in the continuous dual `M*`. `Ultraweak M` is a type copy of `M` equipped with the
coarsest topology making every map `x ↦ φ(x)`, `φ ∈ M_*`, continuous. -/
noncomputable def Ultraweak (M : VonNeumannAlgebra H) : Type u :=
  WeakBilin (normalFunctionalPairing M)

/-- **Addition in the ultraweak algebra.** Let `H` be a complete complex Hilbert space and `M
⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for its vector
functionals. Let `M_*` be their norm-closed complex span in the continuous dual `M*`.
Equip `M` with the ultraweak topology `σ(M,M_*)`, induced by `x ↦ φ(x)` for `φ ∈ M_*`. the
zero and addition of `Ultraweak M` are those of the underlying von Neumann algebra `M`. -/
noncomputable instance ultraweakAddCommMonoid (M : VonNeumannAlgebra H) :
    AddCommMonoid (Ultraweak M) :=
  inferInstanceAs (AddCommMonoid (WeakBilin (normalFunctionalPairing M)))

/-- **Complex scalar action in the ultraweak algebra.** Let `H` be a complete complex Hilbert
space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for its
vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. Equip `M` with the ultraweak topology `σ(M,M_*)`, induced by `x ↦ φ(x)` for `φ ∈
M_*`. complex scalar multiplication on `Ultraweak M` is `c • x` in the underlying algebra
`M`. -/
noncomputable instance ultraweakSMul (M : VonNeumannAlgebra H) : SMul ℂ (Ultraweak M) :=
  inferInstanceAs (SMul ℂ (WeakBilin (normalFunctionalPairing M)))

/-- **Complex vector space structure of the ultraweak algebra.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for
its vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. Equip `M` with the ultraweak topology `σ(M,M_*)`, induced by `x ↦ φ(x)` for `φ ∈
M_*`. `Ultraweak M` has the complex module operations of `M`, with the same zero, addition
and scalar action. -/
noncomputable instance ultraweakModule (M : VonNeumannAlgebra H) : Module ℂ (Ultraweak M) :=
  inferInstanceAs (Module ℂ (WeakBilin (normalFunctionalPairing M)))

/-- **Ring operations of the ultraweak algebra.** Let `H` be a complete complex Hilbert space
and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for its vector
functionals. Let `M_*` be their norm-closed complex span in the continuous dual `M*`.
Equip `M` with the ultraweak topology `σ(M,M_*)`, induced by `x ↦ φ(x)` for `φ ∈ M_*`.
multiplication, unit, addition and negation on `Ultraweak M` are the corresponding algebra
operations of `M`. This ring structure does not assert joint continuity of multiplication. -/
noncomputable instance ultraweakRing (M : VonNeumannAlgebra H) : Ring (Ultraweak M) :=
  inferInstanceAs (Ring M)

/-- **Complex algebra structure of the ultraweak copy.** Let `H` be a complete complex Hilbert
space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for its
vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. Equip `M` with the ultraweak topology `σ(M,M_*)`, induced by `x ↦ φ(x)` for `φ ∈
M_*`. `Ultraweak M` is a complex algebra with scalar map `c ↦ c I_M` and the algebra
operations of `M`. -/
noncomputable instance ultraweakAlgebra (M : VonNeumannAlgebra H) : Algebra ℂ (Ultraweak M) :=
  inferInstanceAs (Algebra ℂ M)

/-- **Operator involution in the ultraweak algebra.** Let `H` be a complete complex Hilbert
space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for its
vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. Equip `M` with the ultraweak topology `σ(M,M_*)`, induced by `x ↦ φ(x)` for `φ ∈
M_*`. the star of an element of `Ultraweak M` is the Hilbert-operator adjoint of the
corresponding element of `M`, satisfying the star-ring laws. -/
noncomputable instance ultraweakStarRing (M : VonNeumannAlgebra H) : StarRing (Ultraweak M) :=
  inferInstanceAs (StarRing M)

/-- **Conjugate scalar law for the ultraweak involution.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for
its vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. Equip `M` with the ultraweak topology `σ(M,M_*)`, induced by `x ↦ φ(x)` for `φ ∈
M_*`. the involution satisfies `(c • x)*=conj(c) • x*` for `c : ℂ` and `x ∈ Ultraweak M`. -/
noncomputable instance ultraweakStarModule (M : VonNeumannAlgebra H) : StarModule ℂ (Ultraweak M) :=
  inferInstanceAs (StarModule ℂ M)

/-- **Ultraweak topology of the normal-functional pairing.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for
its vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. the topology on `Ultraweak M` is `σ(M,M_*)`, the initial topology for all
evaluations `x ↦ φ(x)` with `φ ∈ M_*`. -/
noncomputable instance ultraweakTopologicalSpace (M : VonNeumannAlgebra H) :
    TopologicalSpace (Ultraweak M) :=
  inferInstanceAs (TopologicalSpace (WeakBilin (normalFunctionalPairing M)))

/-- **Linear identification of the ultraweak and normed algebra.** Let `H` be a complete
complex Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write
`ω_(ξ,η)(x)=⟨ξ,xη⟩` for its vector functionals. Let `M_*` be their norm-closed complex
span in the continuous dual `M*`. Equip `M` with the ultraweak topology `σ(M,M_*)`,
induced by `x ↦ φ(x)` for `φ ∈ M_*`. `ultraweakLinearEquiv M : Ultraweak M ≃ₗ[ℂ] M` is the
identity on algebra elements, with the identity inverse; this is a linear identification
of the underlying spaces. -/
noncomputable def ultraweakLinearEquiv (M : VonNeumannAlgebra H) : Ultraweak M ≃ₗ[ℂ] M where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **Underlying value of an ultraweak algebra element.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for
its vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. Equip `M` with the ultraweak topology `σ(M,M_*)`, induced by `x ↦ φ(x)` for `φ ∈
M_*`. for `x ∈ Ultraweak M`, `ultraweakLinearEquiv M x` is the corresponding element `x ∈
M`. -/
@[simp]
theorem ultraweakLinearEquiv_apply (M : VonNeumannAlgebra H) (x : Ultraweak M) :
    ultraweakLinearEquiv M x = x :=
  rfl

/-- **Star-algebra identification of the ultraweak copy.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for
its vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. Equip `M` with the ultraweak topology `σ(M,M_*)`, induced by `x ↦ φ(x)` for `φ ∈
M_*`. `ultraweakStarAlgEquiv M : Ultraweak M ≃⋆ₐ[ℂ] M` is the identity on elements and
preserves addition, multiplication, scalars and adjoints. -/
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

/-- **Agreement of the ultraweak algebra identifications.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for
its vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. Equip `M` with the ultraweak topology `σ(M,M_*)`, induced by `x ↦ φ(x)` for `φ ∈
M_*`. for `x ∈ Ultraweak M`, `ultraweakStarAlgEquiv M x=ultraweakLinearEquiv M x`, the
underlying element of `M`. -/
@[simp]
theorem ultraweakStarAlgEquiv_apply (M : VonNeumannAlgebra H) (x : Ultraweak M) :
    ultraweakStarAlgEquiv M x = ultraweakLinearEquiv M x :=
  rfl

/-- **Continuity of a normal evaluation.** Let `H` be a complete complex Hilbert space and `M
⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for its vector
functionals. Let `M_*` be their norm-closed complex span in the continuous dual `M*`.
Equip `M` with the ultraweak topology `σ(M,M_*)`, induced by `x ↦ φ(x)` for `φ ∈ M_*`. for
every `φ ∈ M_*`, the scalar map `x ↦ φ(x)` is continuous on `Ultraweak M`. -/
theorem ultraweak_eval_continuous (M : VonNeumannAlgebra H) (φ : normalFunctionalSpace M) :
    Continuous fun x : Ultraweak M => (φ : StrongDual ℂ M) (ultraweakLinearEquiv M x) :=
  WeakBilin.eval_continuous (normalFunctionalPairing M) φ

/-- **Normal evaluations test continuity into the ultraweak algebra.** Let `H` be a complete
complex Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write
`ω_(ξ,η)(x)=⟨ξ,xη⟩` for its vector functionals. Let `M_*` be their norm-closed complex
span in the continuous dual `M*`. Equip `M` with the ultraweak topology `σ(M,M_*)`,
induced by `x ↦ φ(x)` for `φ ∈ M_*`. for any topological space `A` and map `f : A →
Ultraweak M`, `f` is continuous exactly when `a ↦ φ(f(a))` is continuous for every `φ ∈
M_*`. -/
theorem ultraweak_continuous_iff (M : VonNeumannAlgebra H)
    {A : Type v} [TopologicalSpace A] {f : A → Ultraweak M} :
    Continuous f ↔ ∀ φ : normalFunctionalSpace M,
      Continuous fun a => (φ : StrongDual ℂ M) (ultraweakLinearEquiv M (f a)) := by
  constructor
  · intro hf φ
    exact (ultraweak_eval_continuous M φ).comp hf
  · intro h
    exact WeakBilin.continuous_of_continuous_eval (normalFunctionalPairing M) h

/-- **Normal evaluations test ultraweak convergence.** Let `H` be a complete complex Hilbert
space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for its
vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. Equip `M` with the ultraweak topology `σ(M,M_*)`, induced by `x ↦ φ(x)` for `φ ∈
M_*`. for any filter `l` and family `x_a ∈ Ultraweak M`, `x_a→x` along `l` exactly when
`φ(x_a)→φ(x)` in `ℂ` along `l` for every `φ ∈ M_*`. -/
theorem ultraweak_tendsto_iff (M : VonNeumannAlgebra H)
    {A : Type v} {l : Filter A} {f : A → Ultraweak M} {x : Ultraweak M} :
    Tendsto f l (𝓝 x) ↔ ∀ φ : normalFunctionalSpace M,
      Tendsto (fun a => (φ : StrongDual ℂ M) (ultraweakLinearEquiv M (f a))) l
        (𝓝 ((φ : StrongDual ℂ M) (ultraweakLinearEquiv M x))) :=
  WeakBilin.tendsto_iff_forall_eval_tendsto
    (normalFunctionalPairing M) (normalFunctionalPairing_injective M)

/-- **Joint ultraweak continuity of addition.** Let `H` be a complete complex Hilbert space
and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for its vector
functionals. Let `M_*` be their norm-closed complex span in the continuous dual `M*`.
Equip `M` with the ultraweak topology `σ(M,M_*)`, induced by `x ↦ φ(x)` for `φ ∈ M_*`. the
map `(x,y) ↦ x+y` is continuous from `Ultraweak M × Ultraweak M` to `Ultraweak M`. -/
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

/-- **Joint ultraweak continuity of complex scalar multiplication.** Let `H` be a complete
complex Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write
`ω_(ξ,η)(x)=⟨ξ,xη⟩` for its vector functionals. Let `M_*` be their norm-closed complex
span in the continuous dual `M*`. Equip `M` with the ultraweak topology `σ(M,M_*)`,
induced by `x ↦ φ(x)` for `φ ∈ M_*`. the map `(c,x) ↦ c • x` is continuous from `ℂ ×
Ultraweak M` to `Ultraweak M`. -/
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

/-- **Ultraweak algebra as the weak-star dual of its normal-functionals.** Let `H` be a
complete complex Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write
`ω_(ξ,η)(x)=⟨ξ,xη⟩` for its vector functionals. Let `M_*` be their norm-closed complex
span in the continuous dual `M*`. Equip `M` with the ultraweak topology `σ(M,M_*)`,
induced by `x ↦ φ(x)` for `φ ∈ M_*`. `ultraweakWeakDualHomeomorph M : Ultraweak M ≃ₜ
WeakDual ℂ M_*` is the evaluation homeomorphism `x ↦ (φ ↦ φ(x))`. -/
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

/-- **Evaluation of the weak-star realization.** Let `H` be a complete complex Hilbert space
and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for its vector
functionals. Let `M_*` be their norm-closed complex span in the continuous dual `M*`.
Equip `M` with the ultraweak topology `σ(M,M_*)`, induced by `x ↦ φ(x)` for `φ ∈ M_*`. for
`x ∈ Ultraweak M` and `φ ∈ M_*`, `(ultraweakWeakDualHomeomorph M x)(φ)=φ(x)`. -/
@[simp]
theorem ultraweakWeakDualHomeomorph_apply (M : VonNeumannAlgebra H) (x : Ultraweak M)
    (φ : normalFunctionalSpace M) :
    ultraweakWeakDualHomeomorph M x φ = (φ : StrongDual ℂ M) (ultraweakLinearEquiv M x) :=
  rfl

/-- **Hausdorff property of the ultraweak algebra.** Let `H` be a complete complex Hilbert
space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for its
vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. Equip `M` with the ultraweak topology `σ(M,M_*)`, induced by `x ↦ φ(x)` for `φ ∈
M_*`. the topology of `Ultraweak M` is Hausdorff, since normal-functional evaluations
separate elements. -/
noncomputable instance ultraweakT2Space (M : VonNeumannAlgebra H) : T2Space (Ultraweak M) :=
  (ultraweakWeakDualHomeomorph M).isEmbedding.t2Space

/-- **Continuous identity from operator norm to ultraweak topology.** Let `H` be a complete
complex Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write
`ω_(ξ,η)(x)=⟨ξ,xη⟩` for its vector functionals. Let `M_*` be their norm-closed complex
span in the continuous dual `M*`. Equip `M` with the ultraweak topology `σ(M,M_*)`,
induced by `x ↦ φ(x)` for `φ ∈ M_*`. the identity map `M → Ultraweak M` is continuous when
its source has the inherited C-star operator-norm topology. -/
theorem continuous_toUltraweak (M : VonNeumannAlgebra H) :
    Continuous (ultraweakLinearEquiv M).symm := by
  apply (ultraweak_continuous_iff M).2
  intro φ
  simpa only [LinearEquiv.apply_symm_apply] using (φ : StrongDual ℂ M).continuous

end VonNeumannAlgebra
