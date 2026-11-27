/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.SymmetricDiagonal
public import MathlibExt.Algebra.Homology.Hochschild.Maps

/-!
# Naturality of the raw symmetric Hochschild diagonal

A possibly nonunital k-algebra homomorphism g : A → B induces a k-linear map between any chosen
universe lifts of the regular coefficients A and B. Multiplicativity makes this lifted map
compatible with their regular left actions.

For commutative k-algebras A,B and coefficients M,N with symmetric right actions, a k-linear map
f : M → N satisfying f(a·m) = g(a)·f(m) also respects the right actions. The tensor word maps
applying g to every algebra factor and f to the coefficient commute with the raw degree-n
symmetric diagonal. This raw diagonal square requires no unit-preservation hypothesis and allows
separate source and target algebra and coefficient universes.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory
open scoped TensorProduct Simplicial

universe u v v' w w' z

namespace ModuleCat.Algebra.Hochschild.Symmetric

attribute [local instance] ModuleCat.Algebra.Hochschild.uliftSMulCommClass

section RegularCoefficientMaps

variable {k : Type u} [CommRing k]
  {A : Type v} [Ring A] [Algebra k A]
  {B : Type v'} [Ring B] [Algebra k B]

/-- Let k be a commutative ring, A and B k-algebras with associative ring structures, and g : A
→ₙₐ[k] B a possibly nonunital algebra map. The map a ↦ the target lift of g(a) defines a
k-linear map from a chosen universe lift of A to a separately chosen universe lift of B. -/
def regularCoefficientMap (g : A →ₙₐ[k] B) : ULift.{w} A →ₗ[k] ULift.{w'} B where
  toFun a := ULift.up (g a.down)
  map_add' a b := by
    apply ULift.ext
    exact map_add g a.down b.down
  map_smul' r a := by
    apply ULift.ext
    exact map_smul g r a.down

/-- For a possibly nonunital k-algebra map g : A → B between ring k-algebras and an element a of the
chosen source lift, regularCoefficientMap g a is the target lift of g applied to the underlying
element of a. -/
@[simp]
theorem regularCoefficientMap_apply (g : A →ₙₐ[k] B) (a : ULift.{w} A) :
    (regularCoefficientMap g : ULift.{w} A →ₗ[k] ULift.{w'} B) a =
      ULift.up (g a.down) := rfl

/-- Let g : A →ₙₐ[k] B be a possibly nonunital map between ring k-algebras. For a ∈ A and m in the
chosen lifted regular coefficient A, the lifted coefficient map satisfies r_g(a·m) =
g(a)·r_g(m). This is multiplicativity of g, and the source and target lift heights may differ. -/
theorem regularCoefficientMap_smul (g : A →ₙₐ[k] B)
    (a : A) (m : ULift.{w} A) :
    (regularCoefficientMap g : ULift.{w} A →ₗ[k] ULift.{w'} B) (a • m) =
      g a • regularCoefficientMap g m := by
  apply ULift.ext
  change g (a * m.down) = g a * g m.down
  exact map_mul g a m.down

end RegularCoefficientMaps

section SymmetricCoefficients

variable {k : Type u} [CommRing k]
  {A : Type v} [CommRing A] [Algebra k A]
  {B : Type v'} [CommRing B] [Algebra k B]
  {M : Type w} [AddCommGroup M] [Module k M] [Module A M]
  [IsScalarTower k A M]
  {N : Type w'} [AddCommGroup N] [Module k N] [Module B N]
  [IsScalarTower k B N]

omit [IsScalarTower k A M] [IsScalarTower k B N] in
/-- Let k be a commutative ring, A,B commutative k-algebras, and M,N modules carrying k- and A- or
B-actions. Give them the symmetric opposite actions aᵐᵒᵖ·m = a·m. For g : A →ₙₐ[k] B and f : M
→ₗ[k] N satisfying f(a·m) = g(a)·f(m), one has f(aᵐᵒᵖ·m) = (g a)ᵐᵒᵖ·f(m) for all a,m. -/
theorem rightAction_compatibility (g : A →ₙₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) :
    letI := opModule A M
    letI := opModule B N
    ∀ a m, f (MulOpposite.op a • m) = MulOpposite.op (g a) • f m := by
  let := opModule A M
  let := opModule B N
  intro a m
  change f (a • m) = g a • f m
  exact hf a m

/-- Let k be a commutative ring, A,B commutative k-algebras and M,N compatible coefficient modules
with symmetric right actions. Let g : A →ₙₐ[k] B and f : M →ₗ[k] N satisfy f(a·m) = g(a)·f(m).
In every n : ℕ, L_{g,f} ∘ Δ_A = Δ_B ∘ (L_{g,r_g} ⊗ L_{g,f}), where L applies g to every tail and
its indicated coefficient map to the head, r_g is the lifted regular map, and Δ is the raw
symmetric diagonal. Unit preservation is unnecessary. -/
theorem diagonalRaw_naturality (g : A →ₙₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) (n : ℕ) :
    (ModuleCat.Algebra.Hochschild.linearMap g f n).comp (diagonalRaw k A M n) =
      (diagonalRaw k B N n).comp
        (TensorProduct.map
          (ModuleCat.Algebra.Hochschild.linearMap g
            (regularCoefficientMap g : ULift.{w} A →ₗ[k] ULift.{w'} B) n)
          (ModuleCat.Algebra.Hochschild.linearMap g f n)) := by
  apply TensorProduct.curry_injective
  apply ModuleCat.Algebra.Hochschild.tensorPower_ext
  intro a0 a
  apply ModuleCat.Algebra.Hochschild.tensorPower_ext
  intro m b
  change ModuleCat.Algebra.Hochschild.linearMap g f n
      (diagonalRaw k A M n
        ((a0 ⊗ₜ[k] PiTensorProduct.tprod k a) ⊗ₜ[k]
          (m ⊗ₜ[k] PiTensorProduct.tprod k b))) =
    diagonalRaw k B N n
      ((ModuleCat.Algebra.Hochschild.linearMap g
          (regularCoefficientMap g : ULift.{w} A →ₗ[k] ULift.{w'} B) n
          (a0 ⊗ₜ[k] PiTensorProduct.tprod k a)) ⊗ₜ[k]
        (ModuleCat.Algebra.Hochschild.linearMap g f n
          (m ⊗ₜ[k] PiTensorProduct.tprod k b)))
  rw [diagonalRaw_tprod, ModuleCat.Algebra.Hochschild.linearMap_tprod,
    ModuleCat.Algebra.Hochschild.linearMap_tprod,
    ModuleCat.Algebra.Hochschild.linearMap_tprod, diagonalRaw_tprod,
    regularCoefficientMap_apply, hf]
  simp only [map_mul]

end SymmetricCoefficients

end ModuleCat.Algebra.Hochschild.Symmetric
