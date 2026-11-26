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

public import Mathlib.Algebra.Module.LinearMap.Basic
public import MathlibExt.LinearAlgebra.TensorProduct.Balanced.RightActions

/-!
# Balanced tensor–Hom correspondence for right modules

Let R and S be rings, B an R–S bimodule, A a right R-module and C a right
S-module. The two actions on B commute, and all ring and module carrier
universes are independent. The group Hom_S(B, C) of right S-linear maps
has a right R-action by precomposition: (φ r)(b) = φ(r b).
The target C requires only its right S-action.

There is a natural additive equivalence
Hom_S(A ⊗_R B, C) ≃ Hom_R(A, Hom_S(B, C)).
The balanced tensor product is formed over the integer ground ring.
Currying sends f to a ↦ (b ↦ f([a ⊗ b])); uncurrying sends g to the map
[a ⊗ b] ↦ g(a)(b). The equivalence is contravariant in A and B,
covariant in C, and uses the corresponding equivariant tensor maps.
-/

@[expose] public section

noncomputable section

open MulOpposite

universe r s a b c a' b' c'

namespace TensorProduct.Balanced.CoefficientHom

/-- For a ring S and right S-modules B, C with additive commutative
group structures, Hom S B C is the group of right S-linear maps
B → C. Its addition is pointwise, and the two module carrier
universes may be independent. -/
abbrev Hom (S : Type s) [Ring S] (B : Type b) [AddCommGroup B]
    [Module Sᵐᵒᵖ B] (C : Type c) [AddCommGroup C] [Module Sᵐᵒᵖ C] :=
  B →ₗ[Sᵐᵒᵖ] C

variable (R : Type r) (S : Type s) [Ring R] [Ring S]
  (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
  [SMulCommClass R Sᵐᵒᵖ B]

/-- Let R and S be rings, B an additive commutative group with commuting
left R- and right S-actions, and C a right S-module.
The group Hom_S(B, C) carries the right R-action
(φ r)(b) = φ(r b), induced by the left R-action on B.
This action does not require an R-module structure on C. -/
abbrev homModule (C : Type c) [AddCommGroup C] [Module Sᵐᵒᵖ C] :
    Module Rᵐᵒᵖ (Hom S B C) := by
  letI : SMulCommClass Sᵐᵒᵖ R B := SMulCommClass.symm R Sᵐᵒᵖ B
  change Module Rᵈᵐᵃ (B →ₗ[Sᵐᵒᵖ] C)
  infer_instance

@[simp]
theorem homModule_smul_apply (C : Type c) [AddCommGroup C] [Module Sᵐᵒᵖ C]
    (t : Rᵐᵒᵖ) (f : Hom S B C) (x : B) :
    letI := homModule R S B C
    (t • f) x = f (t.unop • x) := by
  let : SMulCommClass Sᵐᵒᵖ R B := SMulCommClass.symm R Sᵐᵒᵖ B
  let := homModule R S B C
  change ((show Rᵈᵐᵃ from t) • f) x = f (t.unop • x)
  exact DomMulAct.smul_linearMap_apply (show Rᵈᵐᵃ from t) f x

/-- Let R and S be rings, B an additive commutative group with commuting
left R- and right S-actions, and C a right S-module.
For a right S-linear map g : C → C′, postcomposition
Hom_S(B, C) → Hom_S(B, C′), φ ↦ g ∘ φ, is right R-linear
for the precomposition actions on both Hom groups. -/
def map {C : Type c} {C' : Type c'} [AddCommGroup C] [AddCommGroup C']
    [Module Sᵐᵒᵖ C] [Module Sᵐᵒᵖ C'] (g : C →ₗ[Sᵐᵒᵖ] C') :
    letI := homModule R S B C
    letI := homModule R S B C'
    Hom S B C →ₗ[Rᵐᵒᵖ] Hom S B C' := by
  letI := homModule R S B C
  letI := homModule R S B C'
  refine { toFun := fun f => g.comp f, map_add' := ?_, map_smul' := ?_ }
  · intro f f'
    apply LinearMap.ext
    intro x
    exact g.map_add (f x) (f' x)
  · intro t f
    apply LinearMap.ext
    intro x
    change g ((t • f) x) = (t • g.comp f) x
    rw [homModule_smul_apply, homModule_smul_apply, LinearMap.comp_apply]

@[simp]
theorem map_apply {C : Type c} {C' : Type c'} [AddCommGroup C] [AddCommGroup C']
    [Module Sᵐᵒᵖ C] [Module Sᵐᵒᵖ C'] (g : C →ₗ[Sᵐᵒᵖ] C') (f : Hom S B C) :
    letI := homModule R S B C
    letI := homModule R S B C'
    map R S B g f = g.comp f := by
  let := homModule R S B C
  let := homModule R S B C'
  rfl

section TensorHom

variable {R S B}
  {A : Type a} [AddCommGroup A] [Module Rᵐᵒᵖ A]
  {C : Type c} [AddCommGroup C] [Module Sᵐᵒᵖ C]

/-- Let R and S be rings, A a right R-module, B a left R-module
and right S-module with commuting actions, and C a right S-module.
For a right S-linear map f : A ⊗_R B → C, currying gives a right
R-linear map A → Hom_S(B, C) with value curry(f)(a)(b) = f([a ⊗ b]).
The right R-action on Hom_S(B, C) is (φ r)(b) = φ(r b). -/
def curry
    (f : letI := rightModule ℤ R S A B
      Balanced ℤ R A B →ₗ[Sᵐᵒᵖ] C) :
    letI := homModule R S B C
    A →ₗ[Rᵐᵒᵖ] Hom S B C := by
  letI := rightModule ℤ R S A B
  letI := homModule R S B C
  refine { toFun := fun x => ?_, map_add' := ?_, map_smul' := ?_ }
  · refine { toFun := fun y => f (mk ℤ R A B x y), map_add' := ?_, map_smul' := ?_ }
    · intro y y'
      rw [map_add, f.map_add]
    · intro t y
      have h := f.map_smul t (mk ℤ R A B x y)
      rw [rightModule_smul_mk] at h
      exact h
  · intro x x'
    apply LinearMap.ext
    intro y
    change f (mk ℤ R A B (x + x') y) =
      f (mk ℤ R A B x y) + f (mk ℤ R A B x' y)
    rw [map_add, LinearMap.add_apply, f.map_add]
  · intro t x
    apply LinearMap.ext
    intro y
    change f (mk ℤ R A B (t • x) y) = f (mk ℤ R A B x (t.unop • y))
    simpa only [op_unop] using congrArg f (balance ℤ R A B t.unop x y)

@[simp]
theorem curry_apply
    (f : letI := rightModule ℤ R S A B
      Balanced ℤ R A B →ₗ[Sᵐᵒᵖ] C) (x : A) (y : B) :
    letI := homModule R S B C
    curry f x y = f (mk ℤ R A B x y) := by
  let := homModule R S B C
  rfl

/-- Let R and S be rings, A a right R-module, B a left R-module
and right S-module with commuting actions, and C a right S-module.
For a right R-linear map g : A → Hom_S(B, C), where
(φ r)(b) = φ(r b), evaluation gives the integer-bilinear pairing
A × B → C, (a, b) ↦ g(a)(b). -/
def pairing
    (g : letI := homModule R S B C
      A →ₗ[Rᵐᵒᵖ] Hom S B C) : A →ₗ[ℤ] B →ₗ[ℤ] C := by
  letI := homModule R S B C
  refine { toFun := fun x => ?_, map_add' := ?_, map_smul' := ?_ }
  · refine { toFun := g x, map_add' := (g x).map_add, map_smul' := ?_ }
    intro z y
    simpa only [Int.cast_id, RingHom.id_apply] using map_intCast_smul (g x) ℤ ℤ z y
  · intro x x'
    apply LinearMap.ext
    intro y
    change g (x + x') y = g x y + g x' y
    exact congrArg (fun h : Hom S B C => h y) (g.map_add x x')
  · intro z x
    apply LinearMap.ext
    intro y
    change g (z • x) y = z • g x y
    have h := map_intCast_smul g ℤ ℤ z x
    simpa only [Int.cast_id, RingHom.id_apply, LinearMap.smul_apply] using
      congrArg (fun h : Hom S B C => h y) h

@[simp]
theorem pairing_apply
    (g : letI := homModule R S B C
      A →ₗ[Rᵐᵒᵖ] Hom S B C) (x : A) (y : B) :
    pairing g x y = g x y := rfl

/-- Let R and S be rings, A a right R-module, B a left R-module
and right S-module with commuting actions, and C a right S-module.
For a right R-linear map g : A → Hom_S(B, C) with the precomposition
right action, the evaluation pairing satisfies
g(a r)(b) = g(a)(r b). Thus it is balanced over R. -/
theorem pairing_balanced
    (g : letI := homModule R S B C
      A →ₗ[Rᵐᵒᵖ] Hom S B C) (r : R) (x : A) (y : B) :
    pairing g (op r • x) y = pairing g x (r • y) := by
  let := homModule R S B C
  rw [pairing_apply (R := R) (S := S) (B := B),
    pairing_apply (R := R) (S := S) (B := B)]
  simp only [g.map_smul, homModule_smul_apply, unop_op]

/-- Let R and S be rings, A a right R-module, B a left R-module
and right S-module with commuting actions, and C a right S-module.
For a right R-linear map g : A → Hom_S(B, C) with the precomposition
right action, uncurrying gives a right S-linear map A ⊗_R B → C
whose pure value is [a ⊗ b] ↦ g(a)(b). -/
def uncurry
    (g : letI := homModule R S B C
      A →ₗ[Rᵐᵒᵖ] Hom S B C) :
    letI := rightModule ℤ R S A B
    Balanced ℤ R A B →ₗ[Sᵐᵒᵖ] C := by
  letI := homModule R S B C
  let l : Balanced ℤ R A B →ₗ[ℤ] C :=
    lift (k := ℤ) (R := R) (M := A) (N := B) (P := C)
      (pairing (R := R) (S := S) (B := B) (A := A) (C := C) g)
      (pairing_balanced (R := R) (S := S) (B := B) (A := A) (C := C) g)
  have hl (a : A) (b : B) : l (mk ℤ R A B a b) = g a b := by
    exact (lift_mk (k := ℤ) (R := R) (M := A) (N := B) (P := C)
      (pairing (R := R) (S := S) (B := B) (A := A) (C := C) g)
      (pairing_balanced (R := R) (S := S) (B := B) (A := A) (C := C) g) a b).trans
        (pairing_apply (R := R) (S := S) (B := B) (A := A) (C := C) g a b)
  letI := rightModule ℤ R S A B
  refine { toFun := l, map_add' := l.map_add, map_smul' := ?_ }
  intro t x
  have h : l.comp (rightAction ℤ R S A B t) =
      (Module.toModuleEnd ℤ C t).comp l := by
    apply hom_ext
    intro a b
    simp only [LinearMap.comp_apply, rightAction_mk]
    rw [hl, hl, leftOperator_apply]
    simpa only [RingHom.id_apply] using (g a).map_smul t b
  change l (rightAction ℤ R S A B t x) = Module.toModuleEnd ℤ C t (l x)
  exact DFunLike.congr_fun h x

@[simp, nolint simpNF] -- stated with Balanced.mk for rw; Balanced.mk_apply simplifies LHS
theorem uncurry_mk
    (g : letI := homModule R S B C
      A →ₗ[Rᵐᵒᵖ] Hom S B C) (x : A) (y : B) :
    letI := rightModule ℤ R S A B
    uncurry g (mk ℤ R A B x y) = g x y := by
  let := rightModule ℤ R S A B
  change lift (k := ℤ) (R := R) (M := A) (N := B) (P := C)
    (pairing (R := R) (S := S) (B := B) (A := A) (C := C) g)
    (pairing_balanced (R := R) (S := S) (B := B) (A := A) (C := C) g)
      (mk ℤ R A B x y) = g x y
  exact (lift_mk (k := ℤ) (R := R) (M := A) (N := B) (P := C)
    (pairing (R := R) (S := S) (B := B) (A := A) (C := C) g)
    (pairing_balanced (R := R) (S := S) (B := B) (A := A) (C := C) g) x y).trans
      (pairing_apply (R := R) (S := S) (B := B) (A := A) (C := C) g x y)

variable (R S B A C) in
/-- Let R and S be rings, A a right R-module, B a left R-module
and right S-module with commuting actions, and C a right S-module.
The additive tensor–Hom equivalence is
Hom_S(A ⊗_R B, C) ≃ Hom_R(A, Hom_S(B, C)).
Its forward map is currying and its inverse is uncurrying, with pure
values f ↦ (a ↦ (b ↦ f([a ⊗ b]))) and g ↦ ([a ⊗ b] ↦ g(a)(b)).
All carriers may have independent universes. -/
def tensorHomEquiv :
    letI := rightModule ℤ R S A B
    letI := homModule R S B C
    (Balanced ℤ R A B →ₗ[Sᵐᵒᵖ] C) ≃+ (A →ₗ[Rᵐᵒᵖ] Hom S B C) := by
  letI := rightModule ℤ R S A B
  letI := homModule R S B C
  refine
    { toFun := curry (R := R) (S := S) (B := B) (A := A) (C := C)
      invFun := uncurry (R := R) (S := S) (B := B) (A := A) (C := C)
      left_inv := ?_
      right_inv := ?_
      map_add' := ?_ }
  · intro f
    apply LinearMap.toAddMonoidHom_injective
    apply addHom_ext ℤ R A B
    intro x y
    change uncurry (R := R) (S := S) (B := B)
      (curry (R := R) (S := S) (B := B) f) (mk ℤ R A B x y) =
        f (mk ℤ R A B x y)
    rw [uncurry_mk (R := R) (S := S) (B := B),
      curry_apply (R := R) (S := S) (B := B)]
  · intro g
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    rw [curry_apply (R := R) (S := S) (B := B),
      uncurry_mk (R := R) (S := S) (B := B)]
  · intro f f'
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    rfl

@[simp]
theorem tensorHomEquiv_apply
    (f : letI := rightModule ℤ R S A B
      Balanced ℤ R A B →ₗ[Sᵐᵒᵖ] C) (x : A) (y : B) :
    letI := homModule R S B C
    tensorHomEquiv R S B A C f x y = f (mk ℤ R A B x y) := by
  let := homModule R S B C
  exact curry_apply (R := R) (S := S) (B := B) (A := A) (C := C) f x y

@[simp, nolint simpNF] -- stated with Balanced.mk for rw; Balanced.mk_apply simplifies LHS
theorem tensorHomEquiv_symm_mk
    (g : letI := homModule R S B C
      A →ₗ[Rᵐᵒᵖ] Hom S B C) (x : A) (y : B) :
    letI := rightModule ℤ R S A B
    (tensorHomEquiv R S B A C).symm g (mk ℤ R A B x y) = g x y := by
  let := rightModule ℤ R S A B
  exact uncurry_mk (R := R) (S := S) (B := B) (A := A) (C := C) g x y

end TensorHom

section TensorMaps

variable {R S B}
  {A : Type a} {A' : Type a'} {A'' : Type c'}
  [AddCommGroup A] [AddCommGroup A'] [AddCommGroup A'']
  [Module Rᵐᵒᵖ A] [Module Rᵐᵒᵖ A'] [Module Rᵐᵒᵖ A'']

/-- Let R and S be rings, A, A′ right R-modules, and B a left
R-module and right S-module with commuting actions. A right R-linear
map f : A → A′ induces the right S-linear tensor map
A ⊗_R B → A′ ⊗_R B, [a ⊗ b] ↦ [f(a) ⊗ b]. -/
def tensorMap (f : A →ₗ[Rᵐᵒᵖ] A') :
    letI := rightModule ℤ R S A B
    letI := rightModule ℤ R S A' B
    Balanced ℤ R A B →ₗ[Sᵐᵒᵖ] Balanced ℤ R A' B := by
  let f₀ : A →ₗ[ℤ] A' := f.toAddMonoidHom.toIntLinearMap
  letI := rightModule ℤ R S A B
  letI := rightModule ℤ R S A' B
  exact mapRight (k := ℤ) (R := R) (S := S)
    (Q := A) (N := B) (Q' := A') (N' := B) f₀ (LinearMap.id : B →ₗ[ℤ] B)
    (fun r x => by
      change f (op r • x) = op r • f x
      simpa only [RingHom.id_apply] using f.map_smul (op r) x)
    (fun _ _ => rfl) (fun _ _ => rfl)

@[simp, nolint simpNF] -- stated with Balanced.mk for rw; Balanced.mk_apply simplifies LHS
theorem tensorMap_mk (f : A →ₗ[Rᵐᵒᵖ] A') (x : A) (y : B) :
    letI := rightModule ℤ R S A B
    letI := rightModule ℤ R S A' B
    tensorMap (R := R) (S := S) (B := B) (A := A) (A' := A') f
      (mk ℤ R A B x y) = mk ℤ R A' B (f x) y := by
  let := rightModule ℤ R S A B
  let := rightModule ℤ R S A' B
  exact mapRight_mk (k := ℤ) (R := R) (S := S)
    (Q := A) (N := B) (Q' := A') (N' := B)
    f.toAddMonoidHom.toIntLinearMap (LinearMap.id : B →ₗ[ℤ] B)
    (fun r x => by
      change f (op r • x) = op r • f x
      simpa only [RingHom.id_apply] using f.map_smul (op r) x)
    (fun _ _ => rfl) (fun _ _ => rfl) x y

theorem tensorMap_id :
    letI := rightModule ℤ R S A B
    tensorMap (R := R) (S := S) (B := B) (A := A) (A' := A)
      (LinearMap.id : A →ₗ[Rᵐᵒᵖ] A) =
        (LinearMap.id : Balanced ℤ R A B →ₗ[Sᵐᵒᵖ] Balanced ℤ R A B) := by
  let := rightModule ℤ R S A B
  apply LinearMap.toAddMonoidHom_injective
  apply addHom_ext ℤ R A B
  intro x y
  change tensorMap (R := R) (S := S) (B := B)
    (LinearMap.id : A →ₗ[Rᵐᵒᵖ] A) (mk ℤ R A B x y) = mk ℤ R A B x y
  rw [tensorMap_mk (R := R) (S := S) (B := B)]
  rfl

theorem tensorMap_comp (f : A →ₗ[Rᵐᵒᵖ] A') (g : A' →ₗ[Rᵐᵒᵖ] A'') :
    letI := rightModule ℤ R S A B
    letI := rightModule ℤ R S A' B
    letI := rightModule ℤ R S A'' B
    tensorMap (R := R) (S := S) (B := B) (A := A) (A' := A'') (g.comp f) =
      (tensorMap (R := R) (S := S) (B := B) (A := A') (A' := A'') g).comp
        (tensorMap (R := R) (S := S) (B := B) (A := A) (A' := A') f) := by
  let := rightModule ℤ R S A B
  let := rightModule ℤ R S A' B
  let := rightModule ℤ R S A'' B
  apply LinearMap.toAddMonoidHom_injective
  apply addHom_ext ℤ R A B
  intro x y
  change tensorMap (R := R) (S := S) (B := B) (g.comp f) (mk ℤ R A B x y) =
    tensorMap (R := R) (S := S) (B := B) g
      (tensorMap (R := R) (S := S) (B := B) f (mk ℤ R A B x y))
  simp only [LinearMap.comp_apply, tensorMap_mk (R := R) (S := S) (B := B)]

theorem tensorMap_add (f g : A →ₗ[Rᵐᵒᵖ] A') :
    letI := rightModule ℤ R S A B
    letI := rightModule ℤ R S A' B
    tensorMap (R := R) (S := S) (B := B) (A := A) (A' := A') (f + g) =
      tensorMap (R := R) (S := S) (B := B) (A := A) (A' := A') f +
        tensorMap (R := R) (S := S) (B := B) (A := A) (A' := A') g := by
  let := rightModule ℤ R S A B
  let := rightModule ℤ R S A' B
  apply LinearMap.toAddMonoidHom_injective
  apply addHom_ext ℤ R A B
  intro x y
  change tensorMap (R := R) (S := S) (B := B) (f + g) (mk ℤ R A B x y) =
    tensorMap (R := R) (S := S) (B := B) f (mk ℤ R A B x y) +
      tensorMap (R := R) (S := S) (B := B) g (mk ℤ R A B x y)
  simp only [LinearMap.add_apply, tensorMap_mk (R := R) (S := S) (B := B)]
  exact DFunLike.congr_fun ((mk ℤ R A' B).map_add (f x) (g x)) y

end TensorMaps

section Naturality

variable {R S B}
  {A : Type a} {A' : Type a'} [AddCommGroup A] [AddCommGroup A']
  [Module Rᵐᵒᵖ A] [Module Rᵐᵒᵖ A']
  {C : Type c} {C' : Type c'} [AddCommGroup C] [AddCommGroup C']
  [Module Sᵐᵒᵖ C] [Module Sᵐᵒᵖ C']

/-- Let R and S be rings, A a right R-module, B a left R-module
and right S-module with commuting actions, and C a right S-module.
For a right R-linear f : A′ → A and g : A → Hom_S(B, C),
uncurrying satisfies
uncurry(g ∘ f) = uncurry(g) ∘ (f ⊗ id_B).
Here A′ is a right R-module, and both tensor maps use the induced
right S-actions. -/
theorem tensorHomEquiv_naturality_left_symm (f : A' →ₗ[Rᵐᵒᵖ] A)
    (g : letI := homModule R S B C
      A →ₗ[Rᵐᵒᵖ] Hom S B C) :
    letI := rightModule ℤ R S A B
    letI := rightModule ℤ R S A' B
    letI := homModule R S B C
    (tensorHomEquiv R S B A' C).symm (g.comp f) =
      ((tensorHomEquiv R S B A C).symm g).comp
        (tensorMap (R := R) (S := S) (B := B) (A := A') (A' := A) f) := by
  let := rightModule ℤ R S A B
  let := rightModule ℤ R S A' B
  let := homModule R S B C
  apply LinearMap.toAddMonoidHom_injective
  apply addHom_ext ℤ R A' B
  intro x y
  change (tensorHomEquiv R S B A' C).symm (g.comp f) (mk ℤ R A' B x y) =
    (tensorHomEquiv R S B A C).symm g
      (tensorMap (R := R) (S := S) (B := B) f (mk ℤ R A' B x y))
  simp only [LinearMap.comp_apply, tensorHomEquiv_symm_mk,
    tensorMap_mk (R := R) (S := S) (B := B)]

/-- Let R and S be rings, A a right R-module, B a left R-module
and right S-module with commuting actions, and C a right S-module.
For a right S-linear f : A ⊗_R B → C and g : C → C′, the currying
correspondence satisfies curry(g ∘ f) =
postcompose(g) ∘ curry(f). The Hom-valued maps are right R-linear
for the action by precomposition on B. -/
theorem tensorHomEquiv_naturality_right
    (f : letI := rightModule ℤ R S A B
      Balanced ℤ R A B →ₗ[Sᵐᵒᵖ] C) (g : C →ₗ[Sᵐᵒᵖ] C') :
    letI := rightModule ℤ R S A B
    letI := homModule R S B C
    letI := homModule R S B C'
    tensorHomEquiv R S B A C' (g.comp f) =
      (map R S B g).comp (tensorHomEquiv R S B A C f) := by
  let := rightModule ℤ R S A B
  let := homModule R S B C
  let := homModule R S B C'
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  rfl

end Naturality


section CoefficientMaps

variable {R S B}
  {B' : Type b'} [AddCommGroup B'] [Module R B'] [Module Sᵐᵒᵖ B']
  [SMulCommClass R Sᵐᵒᵖ B']
  {B'' : Type c'} [AddCommGroup B''] [Module R B''] [Module Sᵐᵒᵖ B'']
  [SMulCommClass R Sᵐᵒᵖ B'']
  {A : Type a} [AddCommGroup A] [Module Rᵐᵒᵖ A]
  {C : Type c} [AddCommGroup C] [Module Sᵐᵒᵖ C]

/-- Let R and S be rings, A a right R-module, and B, B′ left
R-modules and right S-modules with commuting actions. A right S-linear
f : B → B′ satisfying f(r b) = r f(b) induces the right S-linear map
A ⊗_R B → A ⊗_R B′ with value [a ⊗ b] ↦ [a ⊗ f(b)]. -/
def coefficientTensorMap (f : B →ₗ[Sᵐᵒᵖ] B')
    (hf : ∀ (r : R) (x : B), f (r • x) = r • f x) :
    letI := rightModule ℤ R S A B
    letI := rightModule ℤ R S A B'
    Balanced ℤ R A B →ₗ[Sᵐᵒᵖ] Balanced ℤ R A B' := by
  letI := rightModule ℤ R S A B
  letI := rightModule ℤ R S A B'
  exact mapRight (k := ℤ) (R := R) (S := S)
    (Q := A) (N := B) (Q' := A) (N' := B')
    (LinearMap.id : A →ₗ[ℤ] A) f.toAddMonoidHom.toIntLinearMap
    (fun _ _ => rfl) hf
    (fun t x => by
      change f (t • x) = t • f x
      simpa only [RingHom.id_apply] using f.map_smul t x)

@[simp, nolint simpNF] -- stated with Balanced.mk for rw; Balanced.mk_apply simplifies LHS
theorem coefficientTensorMap_mk (f : B →ₗ[Sᵐᵒᵖ] B')
    (hf : ∀ (r : R) (x : B), f (r • x) = r • f x) (a : A) (b : B) :
    letI := rightModule ℤ R S A B
    letI := rightModule ℤ R S A B'
    coefficientTensorMap (R := R) (S := S) (B := B) (B' := B') (A := A) f hf
      (mk ℤ R A B a b) = mk ℤ R A B' a (f b) := by
  let := rightModule ℤ R S A B
  let := rightModule ℤ R S A B'
  exact mapRight_mk (k := ℤ) (R := R) (S := S)
    (Q := A) (N := B) (Q' := A) (N' := B')
    (LinearMap.id : A →ₗ[ℤ] A) f.toAddMonoidHom.toIntLinearMap
    (fun _ _ => rfl) hf
    (fun t x => by
      change f (t • x) = t • f x
      simpa only [RingHom.id_apply] using f.map_smul t x) a b

/-- Let R and S be rings, B, B′ left R-modules and right S-modules
with commuting actions, and C a right S-module. A right S-linear
f : B → B′ satisfying f(r b) = r f(b) gives the right R-linear map
Hom_S(B′, C) → Hom_S(B, C), φ ↦ φ ∘ f.
The right R-actions are by precomposition with left multiplication on B
and B′; C needs no R-action. -/
def precomp (f : B →ₗ[Sᵐᵒᵖ] B')
    (hf : ∀ (r : R) (x : B), f (r • x) = r • f x) :
    letI := homModule R S B C
    letI := homModule R S B' C
    Hom S B' C →ₗ[Rᵐᵒᵖ] Hom S B C := by
  letI := homModule R S B C
  letI := homModule R S B' C
  refine { toFun := fun g => g.comp f, map_add' := ?_, map_smul' := ?_ }
  · intro g g'
    apply LinearMap.ext
    intro x
    rfl
  · intro t g
    apply LinearMap.ext
    intro x
    change (t • g) (f x) = (t • g.comp f) x
    rw [homModule_smul_apply, homModule_smul_apply, LinearMap.comp_apply]
    exact congrArg g (hf t.unop x).symm

@[simp]
theorem precomp_apply (f : B →ₗ[Sᵐᵒᵖ] B')
    (hf : ∀ (r : R) (x : B), f (r • x) = r • f x) (g : Hom S B' C) (x : B) :
    letI := homModule R S B C
    letI := homModule R S B' C
    precomp (R := R) (S := S) (B := B) (B' := B') (C := C) f hf g x =
      g (f x) := by
  let := homModule R S B C
  let := homModule R S B' C
  rfl

/-- Let R and S be rings, A a right R-module, B a left R-module
and right S-module with commuting actions, and C a right S-module.
Let B′ have the same bimodule structures, f : B → B′ preserve both
actions, and g : A ⊗_R B′ → C be right S-linear.
The coefficient naturality equation is
curry(g ∘ (id_A ⊗ f)) = precompose(f) ∘ curry(g).
It identifies covariance of the tensor factor with contravariance of
the coefficient Hom domain. -/
theorem tensorHomEquiv_naturality_coefficient (f : B →ₗ[Sᵐᵒᵖ] B')
    (hf : ∀ (r : R) (x : B), f (r • x) = r • f x)
    (g : letI := rightModule ℤ R S A B'
      Balanced ℤ R A B' →ₗ[Sᵐᵒᵖ] C) :
    letI := rightModule ℤ R S A B
    letI := rightModule ℤ R S A B'
    letI := homModule R S B C
    letI := homModule R S B' C
    tensorHomEquiv R S B A C
      (g.comp (coefficientTensorMap (R := R) (S := S) (B := B) (B' := B')
        (A := A) f hf)) =
      (precomp (R := R) (S := S) (B := B) (B' := B') (C := C) f hf).comp
        (tensorHomEquiv R S B' A C g) := by
  let := rightModule ℤ R S A B
  let := rightModule ℤ R S A B'
  let := homModule R S B C
  let := homModule R S B' C
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  simp only [LinearMap.comp_apply, tensorHomEquiv_apply,
    coefficientTensorMap_mk (R := R) (S := S) (A := A),
    precomp_apply (R := R) (S := S) (C := C)]

/-- Let R and S be rings, A a right R-module and B an R–S bimodule
with commuting actions. The right S-linear balanced tensor map induced
by id_B is id_(A⊗_R B). -/
theorem coefficientTensorMap_id :
    letI := rightModule ℤ R S A B
    coefficientTensorMap (R := R) (S := S) (B := B) (B' := B) (A := A)
      (LinearMap.id : B →ₗ[Sᵐᵒᵖ] B) (fun _ _ => rfl) =
        (LinearMap.id : Balanced ℤ R A B →ₗ[Sᵐᵒᵖ] Balanced ℤ R A B) := by
  let := rightModule ℤ R S A B
  apply LinearMap.toAddMonoidHom_injective
  apply addHom_ext ℤ R A B
  intro x y
  change coefficientTensorMap (R := R) (S := S) (A := A)
    (LinearMap.id : B →ₗ[Sᵐᵒᵖ] B) (fun _ _ => rfl) (mk ℤ R A B x y) =
      mk ℤ R A B x y
  rw [coefficientTensorMap_mk (R := R) (S := S) (A := A)]
  rfl

/-- Let R and S be rings, A a right R-module, and B, B′, B″ R–S
bimodules with commuting actions. For maps f : B → B′ and g : B′ → B″
preserving both actions, coefficientTensorMap(g ∘ f) =
coefficientTensorMap(g) ∘ coefficientTensorMap(f) as right S-linear
maps out of A ⊗_R B. -/
theorem coefficientTensorMap_comp (f : B →ₗ[Sᵐᵒᵖ] B') (g : B' →ₗ[Sᵐᵒᵖ] B'')
    (hf : ∀ (r : R) (x : B), f (r • x) = r • f x)
    (hg : ∀ (r : R) (x : B'), g (r • x) = r • g x) :
    letI := rightModule ℤ R S A B
    letI := rightModule ℤ R S A B'
    letI := rightModule ℤ R S A B''
    coefficientTensorMap (R := R) (S := S) (B := B) (B' := B'') (A := A) (g.comp f)
      (fun r x => (congrArg g (hf r x)).trans (hg r (f x))) =
        (coefficientTensorMap (R := R) (S := S) (B := B') (B' := B'') (A := A) g hg).comp
          (coefficientTensorMap (R := R) (S := S) (B := B) (B' := B') (A := A) f hf) := by
  let := rightModule ℤ R S A B
  let := rightModule ℤ R S A B'
  let := rightModule ℤ R S A B''
  apply LinearMap.toAddMonoidHom_injective
  apply addHom_ext ℤ R A B
  intro x y
  change coefficientTensorMap (R := R) (S := S) (A := A) (g.comp f)
      (fun r x => (congrArg g (hf r x)).trans (hg r (f x))) (mk ℤ R A B x y) =
    coefficientTensorMap (R := R) (S := S) (A := A) g hg
      (coefficientTensorMap (R := R) (S := S) (A := A) f hf (mk ℤ R A B x y))
  simp only [LinearMap.comp_apply, coefficientTensorMap_mk (R := R) (S := S) (A := A)]

/-- Let R and S be rings, B an additive commutative group with commuting
left R- and right S-actions, and C a right S-module.
Precomposition by id_B is the identity on Hom_S(B, C), regarded
as a right R-module through the action (φ r)(b) = φ(r b). -/
theorem precomp_id :
    letI := homModule R S B C
    precomp (R := R) (S := S) (B := B) (B' := B) (C := C)
      (LinearMap.id : B →ₗ[Sᵐᵒᵖ] B) (fun _ _ => rfl) =
      (LinearMap.id : Hom S B C →ₗ[Rᵐᵒᵖ] Hom S B C) := by
  let := homModule R S B C
  apply LinearMap.ext
  intro f
  apply LinearMap.ext
  intro x
  rfl

/-- Let R and S be rings, B, B′, B″ R–S bimodules with commuting
actions, and C a right S-module. For f : B → B′ and g : B′ → B″
preserving both actions, the right R-linear Hom maps satisfy
precompose(g ∘ f) = precompose(f) ∘ precompose(g).
Thus coefficient precomposition reverses composition. -/
theorem precomp_comp (f : B →ₗ[Sᵐᵒᵖ] B') (g : B' →ₗ[Sᵐᵒᵖ] B'')
    (hf : ∀ (r : R) (x : B), f (r • x) = r • f x)
    (hg : ∀ (r : R) (x : B'), g (r • x) = r • g x) :
    letI := homModule R S B C
    letI := homModule R S B' C
    letI := homModule R S B'' C
    precomp (R := R) (S := S) (B := B) (B' := B'') (C := C) (g.comp f)
      (fun r x => (congrArg g (hf r x)).trans (hg r (f x))) =
      (precomp (R := R) (S := S) (B := B) (B' := B') (C := C) f hf).comp
        (precomp (R := R) (S := S) (B := B') (B' := B'') (C := C) g hg) := by
  let := homModule R S B C
  let := homModule R S B' C
  let := homModule R S B'' C
  apply LinearMap.ext
  intro h
  apply LinearMap.ext
  intro x
  rfl

end CoefficientMaps

end TensorProduct.Balanced.CoefficientHom
