/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado

module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.Etale.Finite
public import Mathlib.RingTheory.Unramified.Field

/-!
# Finite étale maps through a prescribed separable closure

Let `k` be a field, `Ω` a separable closure of `k`, and `Ψ` another field extension equipped
with a `k`-algebra map `σ : Ω → Ψ`. The image of `σ` is the relative separable closure of `k`
in `Ψ`.

Every map from a finite étale `k`-algebra to `Ψ` lands in this relative closure and therefore
lifts uniquely through `σ`. Postcomposition with `σ` gives a bijection between the maps into
`Ω` and those into `Ψ`, natural in the finite étale algebra. The base, closure, target field,
and finite-algebra carrier universes are independent.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false


section

universe u v w a

namespace CommAlgCat.FiniteEtale

variable (k : Type u) [Field k]
variable (Ω : Type v) [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]
variable (Ψ : Type w) [Field Ψ] [Algebra k Ψ]

attribute [local instance] IsSepClosure.sep_closed

/-- Prescribed separable closure identifies with the relative closure.

A `k`-algebra map `σ : Ω → Ψ` from a separable closure gives a `k`-algebra equivalence `Ω ≃
separableClosure k Ψ`, with underlying map into `Ψ` equal to `σ`. -/
def fixedSeparableClosureEquiv (σ : Ω →ₐ[k] Ψ) :
    Ω ≃ₐ[k] separableClosure k Ψ := by
  letI : Algebra.IsAlgebraic k Ω := Algebra.IsSeparable.isAlgebraic k Ω
  let f : Ω →ₐ[k] separableClosure k Ψ :=
    σ.codRestrict (separableClosure k Ψ).toSubalgebra (fun x =>
      (map_mem_separableClosure_iff σ).mpr
        (mem_separableClosure_iff.mpr (Algebra.IsSeparable.isSeparable k x)))
  let g : separableClosure k Ψ →ₐ[k] Ω := IsSepClosed.lift
  exact AlgEquiv.ofBijective f (Algebra.IsAlgebraic.algHom_bijective₂ f g).1

/-- Relative closure equivalence retains the given field map.

For `x : Ω`, include the image under the closure equivalence into `Ψ`; the resulting element
is `σ x`. -/
theorem fixedSeparableClosureEquiv_coe_apply (σ : Ω →ₐ[k] Ψ) (x : Ω) :
    ((fixedSeparableClosureEquiv k Ω Ψ σ x : separableClosure k Ψ) : Ψ) = σ x :=
  rfl

/-- Finite étale algebra maps land in the relative separable closure.

For a finite étale `k`-algebra `A`, every value of a `k`-algebra map `A → Ψ` belongs to
`separableClosure k Ψ`. -/
theorem algHom_mem_separableClosure (A : FiniteEtale.{a} k) (f : A →ₐ[k] Ψ) (x : A) :
    f x ∈ separableClosure k Ψ := by
  let p : Ideal A := RingHom.ker f
  let : p.IsPrime := RingHom.ker_isPrime f
  let : p.IsMaximal := inferInstance
  let : Field (A ⧸ p) := Ideal.Quotient.field p
  let : Algebra.IsSeparable k (A ⧸ p) :=
    Algebra.FormallyUnramified.isSeparable k (A ⧸ p)
  let fbar : A ⧸ p →ₐ[k] Ψ := Ideal.Quotient.liftₐ p f (fun _ h => h)
  have hm : fbar (Ideal.Quotient.mkₐ k p x) ∈ separableClosure k Ψ :=
    (map_mem_separableClosure_iff fbar).mpr
      (mem_separableClosure_iff.mpr
        (Algebra.IsSeparable.isSeparable k (Ideal.Quotient.mkₐ k p x)))
  change f x ∈ separableClosure k Ψ at hm
  exact hm

/-- Lift of a finite étale algebra map through the closure embedding.

Restrict a map `A → Ψ` to the relative separable closure and apply the inverse closure
equivalence to define a map `A → Ω`. -/
def liftAlgHom (σ : Ω →ₐ[k] Ψ) (A : FiniteEtale.{a} k) (f : A →ₐ[k] Ψ) :
    A →ₐ[k] Ω :=
  (fixedSeparableClosureEquiv k Ω Ψ σ).symm.toAlgHom.comp
    (f.codRestrict (separableClosure k Ψ).toSubalgebra
      (algHom_mem_separableClosure k Ψ A f))

/-- Lifted finite étale map composes to the given map.

Postcomposing `liftAlgHom σ A f` with `σ` gives `f : A → Ψ`. -/
theorem liftAlgHom_spec (σ : Ω →ₐ[k] Ψ) (A : FiniteEtale.{a} k) (f : A →ₐ[k] Ψ) :
    σ.comp (liftAlgHom k Ω Ψ σ A f) = f := by
  ext x
  let E := fixedSeparableClosureEquiv k Ω Ψ σ
  let y : separableClosure k Ψ := ⟨f x, algHom_mem_separableClosure k Ψ A f x⟩
  change σ (E.symm y) = f x
  exact (fixedSeparableClosureEquiv_coe_apply k Ω Ψ σ (E.symm y)).symm.trans
    (congrArg (fun z : separableClosure k Ψ => (z : Ψ)) (E.apply_symm_apply y))

/-- Closure embedding gives a bijection of finite étale algebra maps.

Postcomposition by `σ` is a bijection from `k`-algebra maps `A → Ω` to maps `A → Ψ`, with
inverse the closure lift. -/
def embeddingHomEquiv (σ : Ω →ₐ[k] Ψ) (A : FiniteEtale.{a} k) :
    (A →ₐ[k] Ω) ≃ (A →ₐ[k] Ψ) where
  toFun f := σ.comp f
  invFun f := liftAlgHom k Ω Ψ σ A f
  left_inv f := by
    apply AlgHom.ext
    intro x
    apply σ.injective
    exact congrArg (fun g : A →ₐ[k] Ψ => g x) (liftAlgHom_spec k Ω Ψ σ A (σ.comp f))
  right_inv f := liftAlgHom_spec k Ω Ψ σ A f

/-- Forward map of the finite étale Hom bijection is postcomposition.

The Hom bijection sends `f : A → Ω` to `σ.comp f`. -/
@[simp] theorem embeddingHomEquiv_apply (σ : Ω →ₐ[k] Ψ) (A : FiniteEtale.{a} k)
    (f : A →ₐ[k] Ω) : embeddingHomEquiv k Ω Ψ σ A f = σ.comp f := rfl

/-- Finite étale Hom bijection is natural by precomposition.

For `f : A → B`, composing a map `B → Ω` with `f` before the Hom bijection equals precomposing
its image `B → Ψ` with `f`. -/
theorem embeddingHomEquiv_naturality (σ : Ω →ₐ[k] Ψ)
    (A B : FiniteEtale.{a} k) (f : A →ₐ[k] B) (g : B →ₐ[k] Ω) :
    embeddingHomEquiv k Ω Ψ σ A (g.comp f) =
      (embeddingHomEquiv k Ω Ψ σ B g).comp f := rfl

end CommAlgCat.FiniteEtale

end
