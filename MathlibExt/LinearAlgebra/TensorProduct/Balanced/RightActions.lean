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

public import MathlibExt.LinearAlgebra.TensorProduct.Balanced.Actions

/-!
# Right actions on balanced tensor quotients

Let `k` be a commutative ring, `R` and `S` semirings, and `Q` and `N` be `k`-modules with a
right `R`-action on `Q` and a left `R`-action on `N`. Their balanced tensor quotient is
obtained from `Q ⊗[k] N` by imposing `(op r • q) ⊗ n = q ⊗ (r • n)`.

A right `S`-action on `N` that commutes with the `k`-action and the left `R`-action induces a
right `S`-action on this quotient, with `t • [q ⊗ n] = [q ⊗ (t • n)]`. Factor maps preserving
the balancing actions and this right action induce right-linear maps of quotients. A
compatible algebra scalar tower on `N` descends to the quotient.

Left and right outer actions on separate factors commute when each commutes with the ground
and balancing actions on its own factor. Scalar, balancing, outer-action, and coefficient
universes remain independent.
-/

@[expose] public section

noncomputable section

open MulOpposite

universe u v s w z w' z'

namespace TensorProduct.Balanced

section Action

variable (k : Type u) (R : Type v) (S : Type s) (Q : Type w) (N : Type z)
  [CommRing k] [Semiring R] [Semiring S]
  [AddCommGroup Q] [AddCommGroup N]
  [Module k Q] [Module k N] [Module Rᵐᵒᵖ Q] [Module R N]
  [Module Sᵐᵒᵖ N] [SMulCommClass Sᵐᵒᵖ k N] [SMulCommClass R Sᵐᵒᵖ N]

/-- Right outer operator commutes with the balancing action.

For `t : Sᵐᵒᵖ`, the `k`-linear endomorphism `n ↦ t • n` satisfies `t • (r • n) = r • (t • n)`
for every `r : R` and `n : N`. This is the compatibility needed to descend it to the balanced
quotient. -/
theorem rightOperator_equivariant (t : Sᵐᵒᵖ) :
    ∀ (r : R) (n : N),
      (Module.toModuleEnd k N t) (r • n) =
        r • (Module.toModuleEnd k N t) n := by
  intro r n
  rw [leftOperator_apply, leftOperator_apply]
  exact (smul_comm r t n).symm

/-- Right outer operator on a pure balanced class.

The quotient map induced by the identity on `Q` and the endomorphism `n ↦ t • n` on `N` sends
`[q ⊗ n]` to `[q ⊗ (t • n)]`. -/
theorem rightOperator_map_mk (t : Sᵐᵒᵖ) (q : Q) (n : N) :
    map (LinearMap.id : Q →ₗ[k] Q) (Module.toModuleEnd k N t)
        (fun r q => leftIdentity_equivariant k Rᵐᵒᵖ Q (op r) q)
        (rightOperator_equivariant k R S N t) (mk k R Q N q n) =
      mk k R Q N q (t • n) := by
  have h := map_mk (LinearMap.id : Q →ₗ[k] Q) (Module.toModuleEnd k N t)
    (fun r q => leftIdentity_equivariant k Rᵐᵒᵖ Q (op r) q)
    (rightOperator_equivariant k R S N t) q n
  exact h.trans (by rw [LinearMap.id_apply, leftOperator_apply])

/-- Right outer action as linear endomorphisms of the quotient.

The right `S`-action on `N`, commuting with `k` and `R`, gives a semiring homomorphism `Sᵐᵒᵖ
→+* Module.End k (Balanced k R Q N)`. Its value at `t` acts on the second factor of a balanced
class. -/
def rightAction : Sᵐᵒᵖ →+* Module.End k (Balanced k R Q N) where
  toFun t := map (LinearMap.id : Q →ₗ[k] Q) (Module.toModuleEnd k N t)
    (fun r q => leftIdentity_equivariant k Rᵐᵒᵖ Q (op r) q)
    (rightOperator_equivariant k R S N t)
  map_one' := by
    apply hom_ext
    intro q n
    rw [rightOperator_map_mk]
    change mk k R Q N q ((1 : Sᵐᵒᵖ) • n) = mk k R Q N q n
    rw [one_smul]
  map_mul' t t' := by
    apply hom_ext
    intro q n
    simp only [Module.End.mul_apply, rightOperator_map_mk]
    change mk k R Q N q ((t * t') • n) = mk k R Q N q (t • (t' • n))
    rw [mul_smul]
  map_zero' := by
    apply hom_ext
    intro q n
    rw [rightOperator_map_mk]
    change mk k R Q N q ((0 : Sᵐᵒᵖ) • n) = 0
    rw [zero_smul, map_zero]
  map_add' t t' := by
    apply hom_ext
    intro q n
    simp only [LinearMap.add_apply, rightOperator_map_mk]
    change mk k R Q N q ((t + t') • n) =
      mk k R Q N q (t • n) + mk k R Q N q (t' • n)
    rw [add_smul, map_add]

/-- Pure-class formula for the right outer action.

For `t : Sᵐᵒᵖ`, applying `rightAction k R S Q N t` to `[q ⊗ n]` gives `[q ⊗ (t • n)]`. -/
@[simp, nolint simpNF] -- stated with Balanced.mk for rw; Balanced.mk_apply simplifies LHS
theorem rightAction_mk (t : Sᵐᵒᵖ) (q : Q) (n : N) :
    rightAction k R S Q N t (mk k R Q N q n) = mk k R Q N q (t • n) := by
  exact rightOperator_map_mk k R S Q N t q n

/-- Right semimodule structure on the balanced quotient.

The endomorphism-valued right action defines a `Module Sᵐᵒᵖ (Balanced k R Q N)` structure by
composition with its semiring homomorphism. -/
abbrev rightModule : Module Sᵐᵒᵖ (Balanced k R Q N) :=
  Module.compHom (Balanced k R Q N) (rightAction k R S Q N)

/-- Right quotient scalar multiplication on pure classes.

With the `Sᵐᵒᵖ`-module structure given by `rightModule`, the equality `t • [q ⊗ n] = [q ⊗ (t •
n)]` holds for all pure balanced classes. -/
theorem rightModule_smul_mk (t : Sᵐᵒᵖ) (q : Q) (n : N) :
    letI := rightModule k R S Q N
    t • mk k R Q N q n = mk k R Q N q (t • n) := by
  let := rightModule k R S Q N
  change rightAction k R S Q N t (mk k R Q N q n) = _
  exact rightAction_mk k R S Q N t q n

/-- Right quotient action commutes with ground scalars.

The `Sᵐᵒᵖ`-action given by `rightModule` commutes with the `k`-action on `Balanced k R Q N`,
because each right-action operator is `k`-linear. -/
theorem rightSMulCommClass :
    letI := rightModule k R S Q N
    SMulCommClass Sᵐᵒᵖ k (Balanced k R Q N) := by
  let := rightModule k R S Q N
  refine ⟨?_⟩
  intro t c x
  change rightAction k R S Q N t (c • x) = c • rightAction k R S Q N t x
  exact (rightAction k R S Q N t).map_smul c x

variable [Algebra k S] [hSN : IsScalarTower k Sᵐᵒᵖ N]

include hSN in
/-- Ground scalars in the opposite algebra act as ground multiplication.

Assume `S` is a `k`-algebra and the actions on `N` form a scalar tower `k → Sᵐᵒᵖ → N`. Then
the quotient operator for `algebraMap k Sᵐᵒᵖ c` is `c` times the identity `k`-linear
endomorphism. -/
theorem rightAction_algebraMap (c : k) :
    rightAction k R S Q N (algebraMap k Sᵐᵒᵖ c) =
      c • (1 : Module.End k (Balanced k R Q N)) := by
  apply hom_ext
  intro q n
  rw [rightAction_mk]
  change mk k R Q N q ((algebraMap k Sᵐᵒᵖ c) • n) = c • mk k R Q N q n
  rw [algebraMap_smul Sᵐᵒᵖ c n]
  exact (mk k R Q N q).map_smul c n

include hSN in
/-- Second-factor scalar tower descends to the balanced quotient.

Assume `S` is a `k`-algebra and `IsScalarTower k Sᵐᵒᵖ N`. The right quotient module structure
then satisfies `IsScalarTower k Sᵐᵒᵖ (Balanced k R Q N)`. -/
theorem rightScalarTower :
    letI := rightModule k R S Q N
    IsScalarTower k Sᵐᵒᵖ (Balanced k R Q N) := by
  let := rightModule k R S Q N
  apply IsScalarTower.of_algebraMap_smul
  intro c x
  change rightAction k R S Q N (algebraMap k Sᵐᵒᵖ c) x = c • x
  rw [rightAction_algebraMap]
  rfl

end Action

section Maps

variable {k : Type u} {R : Type v} {S : Type s}
  {Q : Type w} {N : Type z} {Q' : Type w'} {N' : Type z'}
  [CommRing k] [Semiring R] [Semiring S]
  [AddCommGroup Q] [AddCommGroup N] [AddCommGroup Q'] [AddCommGroup N']
  [Module k Q] [Module k N] [Module k Q'] [Module k N']
  [Module Rᵐᵒᵖ Q] [Module R N] [Module Rᵐᵒᵖ Q'] [Module R N']
  [Module Sᵐᵒᵖ N] [Module Sᵐᵒᵖ N']
  [SMulCommClass Sᵐᵒᵖ k N] [SMulCommClass R Sᵐᵒᵖ N]
  [SMulCommClass Sᵐᵒᵖ k N'] [SMulCommClass R Sᵐᵒᵖ N']

/-- Balanced factor map intertwines right outer operators.

Let `f : Q →ₗ[k] Q'` preserve the right `R`-action and `g : N →ₗ[k] N'` preserve the left
`R`-action and the right `S`-action. The induced balanced map composed after a source right
operator equals the corresponding target right operator composed after the balanced map. -/
theorem map_rightAction (f : Q →ₗ[k] Q') (g : N →ₗ[k] N')
    (hf : ∀ (r : R) (q : Q), f (op r • q) = op r • f q)
    (hg : ∀ (r : R) (n : N), g (r • n) = r • g n)
    (hgS : ∀ (t : Sᵐᵒᵖ) (n : N), g (t • n) = t • g n) (t : Sᵐᵒᵖ) :
    (map f g hf hg).comp (rightAction k R S Q N t) =
      (rightAction k R S Q' N' t).comp (map f g hf hg) := by
  apply hom_ext
  intro q n
  simp only [LinearMap.comp_apply, rightAction_mk, map_mk]
  rw [hgS]

/-- Right-linear balanced map induced by compatible factor maps.

Ground-linear factor maps `f` and `g` preserving the balancing actions, with `g` also
preserving the right `S`-action, induce an `Sᵐᵒᵖ`-linear map between the balanced quotients
equipped with `rightModule`. -/
def mapRight (f : Q →ₗ[k] Q') (g : N →ₗ[k] N')
    (hf : ∀ (r : R) (q : Q), f (op r • q) = op r • f q)
    (hg : ∀ (r : R) (n : N), g (r • n) = r • g n)
    (hgS : ∀ (t : Sᵐᵒᵖ) (n : N), g (t • n) = t • g n) :
    letI := rightModule k R S Q N
    letI := rightModule k R S Q' N'
    Balanced k R Q N →ₗ[Sᵐᵒᵖ] Balanced k R Q' N' := by
  let l : Balanced k R Q N →ₗ[k] Balanced k R Q' N' := map f g hf hg
  letI := rightModule k R S Q N
  letI := rightModule k R S Q' N'
  refine { toFun := l, map_add' := l.map_add, map_smul' := ?_ }
  intro t x
  change l (rightAction k R S Q N t x) = rightAction k R S Q' N' t (l x)
  exact congrArg (fun a : Balanced k R Q N →ₗ[k] Balanced k R Q' N' => a x)
    (map_rightAction f g hf hg hgS t)

/-- Pure-class formula for a right-linear balanced map.

The right-linear map induced by compatible factor maps `f` and `g` sends `[q ⊗ n]` to `[f q ⊗
g n]`. -/
@[simp, nolint simpNF] -- stated with Balanced.mk for rw; Balanced.mk_apply simplifies LHS
theorem mapRight_mk (f : Q →ₗ[k] Q') (g : N →ₗ[k] N')
    (hf : ∀ (r : R) (q : Q), f (op r • q) = op r • f q)
    (hg : ∀ (r : R) (n : N), g (r • n) = r • g n)
    (hgS : ∀ (t : Sᵐᵒᵖ) (n : N), g (t • n) = t • g n) (q : Q) (n : N) :
    letI := rightModule k R S Q N
    letI := rightModule k R S Q' N'
    mapRight f g hf hg hgS (mk k R Q N q n) = mk k R Q' N' (f q) (g n) := by
  let := rightModule k R S Q N
  let := rightModule k R S Q' N'
  change map f g hf hg (mk k R Q N q n) = _
  exact map_mk f g hf hg q n

end Maps

section CommutingFactorActions

universe vL vT

variable (k : Type u) (R : Type v) (L : Type vL) (T : Type vT)
  (M : Type w) (N : Type z)
  [CommRing k] [Semiring R] [Semiring L] [Semiring T]
  [AddCommGroup M] [AddCommGroup N] [Module k M] [Module k N]
  [Module Rᵐᵒᵖ M] [Module R N]
  [Module L M] [SMulCommClass L k M] [SMulCommClass L Rᵐᵒᵖ M]
  [Module Tᵐᵒᵖ N] [SMulCommClass Tᵐᵒᵖ k N] [SMulCommClass R Tᵐᵒᵖ N]

/-- Outer actions on separate balanced factors commute.

Let a left `L`-action on `M` commute with its `k`-action and right `R`-action, and a right
`T`-action on `N` commute with its `k`-action and left `R`-action. The induced left `L`-action
and right `T`-action commute on `Balanced k R M N`. -/
theorem leftRightSMulCommClass_of_factor_actions :
    letI := leftModule k R L M N
    letI := rightModule k R T M N
    SMulCommClass L Tᵐᵒᵖ (Balanced k R M N) := by
  let := leftModule k R L M N
  let := rightModule k R T M N
  refine @SMulCommClass.mk L Tᵐᵒᵖ (Balanced k R M N)
    (leftModule k R L M N).toSMul (rightModule k R T M N).toSMul ?_
  intro l t x
  have h : (leftAction k R L M N l).comp (rightAction k R T M N t) =
      (rightAction k R T M N t).comp (leftAction k R L M N l) := by
    apply hom_ext (k := k) (R := R) (M := M) (N := N)
    intro m n
    simp only [LinearMap.comp_apply, leftAction_mk, rightAction_mk]
  change leftAction k R L M N l (rightAction k R T M N t x) =
    rightAction k R T M N t (leftAction k R L M N l x)
  exact DFunLike.congr_fun h x

end CommutingFactorActions

end TensorProduct.Balanced
