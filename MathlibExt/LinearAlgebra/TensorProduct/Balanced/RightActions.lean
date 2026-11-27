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
# Right outer actions on a balanced tensor quotient

Let k be a commutative ring, R a semiring, Q a right R-module and N a left R-module, both
additive commutative groups with k-module structures. Write B=B_k(R;Q,N) for the ground
k-tensor quotient by (q·r)⊗n=q⊗(r•n), and q⊠n for its pure class. Let S be a semiring acting
on N on the right, commuting with its k-action and left R-action. For t∈Sᵒᵖ, define
ρ_t(q⊠n)=q⊠(t•n). The operators ρ_t give a semiring homomorphism Sᵒᵖ→End_k(B), hence a right
S-module structure on B. When S is a k-algebra and N has a compatible scalar tower, this
action restricts to the ground k-action.
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

/-- **Right outer operator preserves left balancing scalars.**

Let k be a commutative ring, R a semiring, Q a right R-module and N a left R-module, both
additive commutative groups with k-module structures. Write B=B_k(R;Q,N) for the ground
k-tensor quotient by (q·r)⊗n=q⊗(r•n), and q⊠n for its pure class. Let S be a semiring acting
on N on the right, commuting with its k-action and left R-action. For t∈Sᵒᵖ, define
ρ_t(q⊠n)=q⊠(t•n). For t∈Sᵒᵖ, r∈R and n∈N, t•(r•n)=r•(t•n).
-/
theorem rightOperator_equivariant (t : Sᵐᵒᵖ) :
    ∀ (r : R) (n : N),
      (Module.toModuleEnd k N t) (r • n) =
        r • (Module.toModuleEnd k N t) n := by
  intro r n
  rw [leftOperator_apply, leftOperator_apply]
  exact (smul_comm r t n).symm

/-- **Balanced pure value of the right outer operator.**

Let k be a commutative ring, R a semiring, Q a right R-module and N a left R-module, both
additive commutative groups with k-module structures. Write B=B_k(R;Q,N) for the ground
k-tensor quotient by (q·r)⊗n=q⊗(r•n), and q⊠n for its pure class. Let S be a semiring acting
on N on the right, commuting with its k-action and left R-action. For t∈Sᵒᵖ, define
ρ_t(q⊠n)=q⊠(t•n). The map induced by id_Q and n↦t•n sends q⊠n to q⊠(t•n).
-/
theorem rightOperator_map_mk (t : Sᵐᵒᵖ) (q : Q) (n : N) :
    map (LinearMap.id : Q →ₗ[k] Q) (Module.toModuleEnd k N t)
        (fun r q => leftIdentity_equivariant k Rᵐᵒᵖ Q (op r) q)
        (rightOperator_equivariant k R S N t) (mk k R Q N q n) =
      mk k R Q N q (t • n) := by
  have h := map_mk (LinearMap.id : Q →ₗ[k] Q) (Module.toModuleEnd k N t)
    (fun r q => leftIdentity_equivariant k Rᵐᵒᵖ Q (op r) q)
    (rightOperator_equivariant k R S N t) q n
  exact h.trans (by rw [LinearMap.id_apply, leftOperator_apply])

/-- **Opposite-semiring representation on the balanced quotient.**

Let k be a commutative ring, R a semiring, Q a right R-module and N a left R-module, both
additive commutative groups with k-module structures. Write B=B_k(R;Q,N) for the ground
k-tensor quotient by (q·r)⊗n=q⊗(r•n), and q⊠n for its pure class. Let S be a semiring acting
on N on the right, commuting with its k-action and left R-action. For t∈Sᵒᵖ, define
ρ_t(q⊠n)=q⊠(t•n). The semiring homomorphism rightAction k R S Q N:Sᵒᵖ→End_k(B) sends t to ρ_t.
-/
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

@[simp, nolint simpNF] -- stated with Balanced.mk for rw; Balanced.mk_apply simplifies LHS
theorem rightAction_mk (t : Sᵐᵒᵖ) (q : Q) (n : N) :
    rightAction k R S Q N t (mk k R Q N q n) = mk k R Q N q (t • n) := by
  exact rightOperator_map_mk k R S Q N t q n

/-- **Right outer module on the balanced quotient.**

Let k be a commutative ring, R a semiring, Q a right R-module and N a left R-module, both
additive commutative groups with k-module structures. Write B=B_k(R;Q,N) for the ground
k-tensor quotient by (q·r)⊗n=q⊗(r•n), and q⊠n for its pure class. Let S be a semiring acting
on N on the right, commuting with its k-action and left R-action. For t∈Sᵒᵖ, define
ρ_t(q⊠n)=q⊠(t•n). The module rightModule k R S Q N over Sᵒᵖ has t•(q⊠n)=q⊠(t•n).
-/
abbrev rightModule : Module Sᵐᵒᵖ (Balanced k R Q N) :=
  Module.compHom (Balanced k R Q N) (rightAction k R S Q N)

theorem rightModule_smul_mk (t : Sᵐᵒᵖ) (q : Q) (n : N) :
    letI := rightModule k R S Q N
    t • mk k R Q N q n = mk k R Q N q (t • n) := by
  let := rightModule k R S Q N
  change rightAction k R S Q N t (mk k R Q N q n) = _
  exact rightAction_mk k R S Q N t q n

/-- **Right outer and ground scalars commute.**

Let k be a commutative ring, R a semiring, Q a right R-module and N a left R-module, both
additive commutative groups with k-module structures. Write B=B_k(R;Q,N) for the ground
k-tensor quotient by (q·r)⊗n=q⊗(r•n), and q⊠n for its pure class. Let S be a semiring acting
on N on the right, commuting with its k-action and left R-action. For t∈Sᵒᵖ, define
ρ_t(q⊠n)=q⊠(t•n). For t∈Sᵒᵖ, c∈k and z∈B, ρ_t(c•z)=c•ρ_t(z).
-/
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
/-- **Ground scalars in the opposite algebra act on the quotient.**

Let k be a commutative ring, R a semiring, Q a right R-module and N a left R-module, both
additive commutative groups with k-module structures. Write B=B_k(R;Q,N) for the ground
k-tensor quotient by (q·r)⊗n=q⊗(r•n), and q⊠n for its pure class. Let S be a semiring acting
on N on the right, commuting with its k-action and left R-action. For t∈Sᵒᵖ, define
ρ_t(q⊠n)=q⊠(t•n). Assume S is a k-algebra and N has compatible k,Sᵒᵖ scalar actions. Then
rightAction(algebraMap k Sᵒᵖ c)=c•id_B for c∈k.
-/
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
/-- **Scalar tower for the right outer quotient action.**

Let k be a commutative ring, R a semiring, Q a right R-module and N a left R-module, both
additive commutative groups with k-module structures. Write B=B_k(R;Q,N) for the ground
k-tensor quotient by (q·r)⊗n=q⊗(r•n), and q⊠n for its pure class. Let S be a semiring acting
on N on the right, commuting with its k-action and left R-action. For t∈Sᵒᵖ, define
ρ_t(q⊠n)=q⊠(t•n). If S is a k-algebra and N has a compatible k,Sᵒᵖ scalar tower, then the
induced k,Sᵒᵖ actions on B form the same scalar tower.
-/
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

/-- **Balanced factor maps intertwine right outer actions.**

Let k be a commutative ring, R a semiring, Q a right R-module and N a left R-module, both
additive commutative groups with k-module structures. Write B=B_k(R;Q,N) for the ground
k-tensor quotient by (q·r)⊗n=q⊗(r•n), and q⊠n for its pure class. Let S be a semiring acting
on N on the right, commuting with its k-action and left R-action. For t∈Sᵒᵖ, define
ρ_t(q⊠n)=q⊠(t•n). Let Q′,N′ have the corresponding structures and f:Q→Q′, g:N→N′ be k-linear,
with f(q·r)=f(q)·r and g(r•n)=r•g(n). If g(t•n)=t•g(n), the induced balanced map F satisfies
F∘ρ_t=ρ′_t∘F for all t∈Sᵒᵖ.
-/
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

/-- **Right outer-linear map induced on balanced quotients.**

Let k be a commutative ring, R a semiring, Q a right R-module and N a left R-module, both
additive commutative groups with k-module structures. Write B=B_k(R;Q,N) for the ground
k-tensor quotient by (q·r)⊗n=q⊗(r•n), and q⊠n for its pure class. Let S be a semiring acting
on N on the right, commuting with its k-action and left R-action. For t∈Sᵒᵖ, define
ρ_t(q⊠n)=q⊠(t•n). Let Q′,N′ have the corresponding structures and f:Q→Q′, g:N→N′ be k-linear,
with f(q·r)=f(q)·r and g(r•n)=r•g(n). If g is Sᵒᵖ-equivariant, mapRight f g is Sᵒᵖ-linear,
with pure value q⊠n↦f(q)⊠g(n).
-/
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

/-- **Actions on separate balanced factors commute.**

Let k be a commutative ring, R a semiring, Q a right R-module and N a left R-module, both
additive commutative groups with k-module structures. Write B=B_k(R;Q,N) for the ground
k-tensor quotient by (q·r)⊗n=q⊗(r•n), and q⊠n for its pure class. Let L act on Q commuting
with its k and right R-actions, and let Tᵒᵖ act on N commuting with its k and left R-actions.
The induced left L- and right T-actions on B commute: ℓ_l(ρ_t(z))=ρ_t(ℓ_l(z)). L,T are
semirings; no k-linearity premise on the balancing R-actions is required.
-/
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
