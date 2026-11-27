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

public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Algebra.Tower
public import MathlibExt.LinearAlgebra.TensorProduct.Balanced

/-!
# Left outer actions on a balanced tensor quotient

Let k be a commutative ring, R a semiring, Q a right R-module and N a left R-module, both
additive commutative groups with k-module structures. Write B=B_k(R;Q,N) for the ground
k-tensor quotient by (q·r)⊗n=q⊗(r•n), and q⊠n for its pure class. Let S be a semiring acting
on Q with its action commuting with the k-action and right R-action. On B define
ℓ_s(q⊠n)=(s•q)⊠n. The operators ℓ_s are k-linear and give a semiring homomorphism S→End_k(B),
hence an S-module structure. If S is a k-algebra and Q has the compatible scalar tower, the
quotient has the same k,S scalar compatibility.
-/

@[expose] public section

open MulOpposite

universe u v v' w z w' z' t

namespace TensorProduct.Balanced

section AdditiveExt

variable (k : Type u) (R : Type v) (Q : Type w) (N : Type z)
  [CommRing k] [Semiring R] [AddCommGroup Q] [AddCommGroup N]
  [Module k Q] [Module k N] [Module Rᵐᵒᵖ Q] [Module R N]

/-- **Pure balanced classes determine an additive map.**

Let k be a commutative ring, R a semiring, Q a right R-module and N a left R-module, both
additive commutative groups with k-module structures. Write B=B_k(R;Q,N) for the ground
k-tensor quotient by (q·r)⊗n=q⊗(r•n), and q⊠n for its pure class. For an additive commutative
monoid P, additive maps F,G:B→P agreeing on every q⊠n are equal.
-/
theorem addHom_ext {P : Type t} [AddCommMonoid P]
    {f g : Balanced k R Q N →+ P}
    (h : ∀ (q : Q) (n : N), f (mk k R Q N q n) = g (mk k R Q N q n)) :
    f = g := by
  apply AddMonoidHom.ext
  intro x
  obtain ⟨a, rfl⟩ := (balanceRelations k R Q N).mkQ_surjective x
  induction a using TensorProduct.inductionOn with
  | tmul q n => exact h q n
  | add a b ha hb =>
      have hq : (balanceRelations k R Q N).mkQ (a + b) =
          (balanceRelations k R Q N).mkQ a + (balanceRelations k R Q N).mkQ b :=
        (balanceRelations k R Q N).mkQ.toAddMonoidHom.map_add a b
      exact (congrArg f hq).trans
        ((f.map_add _ _).trans
          ((congrArg₂ (fun x y : P => x + y) ha hb).trans
            ((g.map_add _ _).symm.trans (congrArg g hq).symm)))


end AdditiveExt

section LeftAction

variable (k : Type u) (R : Type v) (S : Type v') (Q : Type w) (N : Type z)
  [CommRing k] [Semiring R] [Semiring S]
  [AddCommGroup Q] [AddCommGroup N]
  [Module k Q] [Module k N] [Module Rᵐᵒᵖ Q] [Module R N]
  [Module S Q] [SMulCommClass S k Q] [SMulCommClass S Rᵐᵒᵖ Q]

/-- **Evaluation of an outer-action endomorphism.**

Let k be a commutative ring, S a semiring and Q a k-module and S-module with commuting scalar
actions. For s∈S and q∈Q, Module.toModuleEnd k Q s q=s•q.
-/
theorem leftOperator_apply (s : S) (q : Q) :
    Module.toModuleEnd k Q s q = s • q := rfl

/-- **Outer operator preserves the right balancing action.**

Let k be a commutative ring, R a semiring, Q a right R-module and N a left R-module, both
additive commutative groups with k-module structures. Write B=B_k(R;Q,N) for the ground
k-tensor quotient by (q·r)⊗n=q⊗(r•n), and q⊠n for its pure class. Let S be a semiring acting
on Q with its action commuting with the k-action and right R-action. On B define
ℓ_s(q⊠n)=(s•q)⊠n. For s∈S, r∈R and q∈Q, ℓ_s on the first factor satisfies s•(q·r)=(s•q)·r.
-/
theorem leftOperator_equivariant (s : S) :
    ∀ (r : R) (q : Q),
      (Module.toModuleEnd k Q s) (op r • q) =
        op r • (Module.toModuleEnd k Q s) q := by
  intro r q
  rw [leftOperator_apply, leftOperator_apply]
  exact smul_comm s (op r) q

/-- **The identity map preserves the second-factor action.**

Let k be a commutative ring, R a semiring and N a k-module and left R-module. For r∈R and n∈N,
id_N(r•n)=r•id_N(n).
-/
theorem leftIdentity_equivariant :
    ∀ (r : R) (n : N), (LinearMap.id : N →ₗ[k] N) (r • n) =
      r • (LinearMap.id : N →ₗ[k] N) n := fun _ _ => rfl

/-- **Balanced quotient value of an outer operator.**

Let k be a commutative ring, R a semiring, Q a right R-module and N a left R-module, both
additive commutative groups with k-module structures. Write B=B_k(R;Q,N) for the ground
k-tensor quotient by (q·r)⊗n=q⊗(r•n), and q⊠n for its pure class. Let S be a semiring acting
on Q with its action commuting with the k-action and right R-action. On B define
ℓ_s(q⊠n)=(s•q)⊠n. The balanced map induced by q↦s•q and id_N sends q⊠n to (s•q)⊠n.
-/
theorem leftOperator_map_mk (s : S) (q : Q) (n : N) :
    map (Module.toModuleEnd k Q s) (LinearMap.id : N →ₗ[k] N)
        (leftOperator_equivariant k R S Q s) (leftIdentity_equivariant k R N)
          (mk k R Q N q n) =
      mk k R Q N (s • q) n := by
  have h := map_mk (Module.toModuleEnd k Q s) (LinearMap.id : N →ₗ[k] N)
    (leftOperator_equivariant k R S Q s) (leftIdentity_equivariant k R N) q n
  exact h.trans (by rw [leftOperator_apply, LinearMap.id_apply])

/-- **Outer semiring representation on the balanced quotient.**

Let k be a commutative ring, R a semiring, Q a right R-module and N a left R-module, both
additive commutative groups with k-module structures. Write B=B_k(R;Q,N) for the ground
k-tensor quotient by (q·r)⊗n=q⊗(r•n), and q⊠n for its pure class. Let S be a semiring acting
on Q with its action commuting with the k-action and right R-action. On B define
ℓ_s(q⊠n)=(s•q)⊠n. The semiring homomorphism leftAction k R S Q N:S→End_k(B) sends s to ℓ_s.
-/
def leftAction : S →+* Module.End k (Balanced k R Q N) where
  toFun s := map (Module.toModuleEnd k Q s) (LinearMap.id : N →ₗ[k] N)
    (leftOperator_equivariant k R S Q s) (leftIdentity_equivariant k R N)
  map_one' := by
    apply hom_ext
    intro q n
    rw [leftOperator_map_mk]
    change mk k R Q N ((1 : S) • q) n = mk k R Q N q n
    rw [one_smul]
  map_mul' s t := by
    apply hom_ext
    intro q n
    simp only [Module.End.mul_apply, leftOperator_map_mk]
    change mk k R Q N ((s * t) • q) n = mk k R Q N (s • (t • q)) n
    rw [mul_smul]
  map_zero' := by
    apply hom_ext
    intro q n
    rw [leftOperator_map_mk]
    change mk k R Q N ((0 : S) • q) n = 0
    rw [zero_smul, map_zero, LinearMap.zero_apply]
  map_add' s t := by
    apply hom_ext
    intro q n
    simp only [LinearMap.add_apply, leftOperator_map_mk]
    change mk k R Q N ((s + t) • q) n =
      mk k R Q N (s • q) n + mk k R Q N (t • q) n
    rw [add_smul, map_add, LinearMap.add_apply]

@[simp, nolint simpNF] -- stated with Balanced.mk for rw; Balanced.mk_apply simplifies LHS
theorem leftAction_mk (s : S) (q : Q) (n : N) :
    leftAction k R S Q N s (mk k R Q N q n) = mk k R Q N (s • q) n := by
  exact leftOperator_map_mk k R S Q N s q n

/-- **Left outer module on a balanced quotient.**

Let k be a commutative ring, R a semiring, Q a right R-module and N a left R-module, both
additive commutative groups with k-module structures. Write B=B_k(R;Q,N) for the ground
k-tensor quotient by (q·r)⊗n=q⊗(r•n), and q⊠n for its pure class. Let S be a semiring acting
on Q with its action commuting with the k-action and right R-action. On B define
ℓ_s(q⊠n)=(s•q)⊠n. The S-module structure leftModule k R S Q N is the action s•(q⊠n)=(s•q)⊠n.
-/
abbrev leftModule : Module S (Balanced k R Q N) :=
  Module.compHom (Balanced k R Q N) (leftAction k R S Q N)

theorem leftModule_smul_mk (s : S) (q : Q) (n : N) :
    letI := leftModule k R S Q N
    s • mk k R Q N q n = mk k R Q N (s • q) n := by
  let := leftModule k R S Q N
  change leftAction k R S Q N s (mk k R Q N q n) = _
  exact leftAction_mk k R S Q N s q n

/-- **Outer and ground scalar actions commute on the quotient.**

Let k be a commutative ring, R a semiring, Q a right R-module and N a left R-module, both
additive commutative groups with k-module structures. Write B=B_k(R;Q,N) for the ground
k-tensor quotient by (q·r)⊗n=q⊗(r•n), and q⊠n for its pure class. Let S be a semiring acting
on Q with its action commuting with the k-action and right R-action. On B define
ℓ_s(q⊠n)=(s•q)⊠n. For s∈S, c∈k and z∈B, ℓ_s(c•z)=c•ℓ_s(z).
-/
theorem leftSMulCommClass :
    letI := leftModule k R S Q N
    SMulCommClass S k (Balanced k R Q N) := by
  let := leftModule k R S Q N
  refine ⟨?_⟩
  intro s c x
  change leftAction k R S Q N s (c • x) = c • leftAction k R S Q N s x
  exact (leftAction k R S Q N s).map_smul c x

variable [Algebra k S] [hSQ : IsScalarTower k S Q]

include hSQ in
/-- **Ground scalars in the outer algebra act as ground scalars.**

Let k be a commutative ring, R a semiring, Q a right R-module and N a left R-module, both
additive commutative groups with k-module structures. Write B=B_k(R;Q,N) for the ground
k-tensor quotient by (q·r)⊗n=q⊗(r•n), and q⊠n for its pure class. Let S be a semiring acting
on Q with its action commuting with the k-action and right R-action. On B define
ℓ_s(q⊠n)=(s•q)⊠n. Assume S is a k-algebra and c•q=(algebraMap k S c)•q on Q. Then
leftAction(algebraMap k S c)=c•id_B as k-linear endomorphisms.
-/
theorem leftAction_algebraMap (c : k) :
    leftAction k R S Q N (algebraMap k S c) =
      c • (1 : Module.End k (Balanced k R Q N)) := by
  apply hom_ext
  intro q n
  rw [leftAction_mk]
  change mk k R Q N ((algebraMap k S c) • q) n = c • mk k R Q N q n
  rw [algebraMap_smul S c q]
  simpa only [LinearMap.smul_apply] using
    congrArg (fun l : N →ₗ[k] Balanced k R Q N => l n)
      ((mk k R Q N).map_smul c q)

include hSQ in
/-- **Scalar tower for the left outer quotient action.**

Let k be a commutative ring, R a semiring, Q a right R-module and N a left R-module, both
additive commutative groups with k-module structures. Write B=B_k(R;Q,N) for the ground
k-tensor quotient by (q·r)⊗n=q⊗(r•n), and q⊠n for its pure class. Let S be a semiring acting
on Q with its action commuting with the k-action and right R-action. On B define
ℓ_s(q⊠n)=(s•q)⊠n. If S is a k-algebra and the k,S actions on Q form a scalar tower, then
c•(s•z)=((algebraMap k S c)*s)•z on B; the k-action agrees with restriction of the S-action.
-/
theorem leftScalarTower :
    letI := leftModule k R S Q N
    IsScalarTower k S (Balanced k R Q N) := by
  let := leftModule k R S Q N
  apply IsScalarTower.of_algebraMap_smul
  intro c x
  change leftAction k R S Q N (algebraMap k S c) x = c • x
  rw [leftAction_algebraMap]
  rfl

end LeftAction

section LeftMaps

variable {k : Type u} {R : Type v} {S : Type v'}
  {Q : Type w} {N : Type z} {Q' : Type w'} {N' : Type z'}
  [CommRing k] [Semiring R] [Semiring S]
  [AddCommGroup Q] [AddCommGroup N] [AddCommGroup Q'] [AddCommGroup N']
  [Module k Q] [Module k N] [Module k Q'] [Module k N']
  [Module Rᵐᵒᵖ Q] [Module R N] [Module Rᵐᵒᵖ Q'] [Module R N']
  [Module S Q] [Module S Q']
  [SMulCommClass S k Q] [SMulCommClass S Rᵐᵒᵖ Q]
  [SMulCommClass S k Q'] [SMulCommClass S Rᵐᵒᵖ Q']

/-- **Balanced factor maps intertwine left outer actions.**

Let k be a commutative ring, R a semiring, Q a right R-module and N a left R-module, both
additive commutative groups with k-module structures. Write B=B_k(R;Q,N) for the ground
k-tensor quotient by (q·r)⊗n=q⊗(r•n), and q⊠n for its pure class. Let S be a semiring acting
on Q with its action commuting with the k-action and right R-action. On B define
ℓ_s(q⊠n)=(s•q)⊠n. Let Q′,N′ have the corresponding structures and f:Q→Q′, g:N→N′ be k-linear,
with f(q·r)=f(q)·r and g(r•n)=r•g(n). If f(s•q)=s•f(q), the induced balanced map F satisfies
F∘ℓ_s=ℓ′_s∘F for every s∈S.
-/
theorem map_leftAction (f : Q →ₗ[k] Q') (g : N →ₗ[k] N')
    (hf : ∀ (r : R) (q : Q), f (op r • q) = op r • f q)
    (hg : ∀ (r : R) (n : N), g (r • n) = r • g n)
    (hfS : ∀ (s : S) (q : Q), f (s • q) = s • f q) (s : S) :
    (map f g hf hg).comp (leftAction k R S Q N s) =
      (leftAction k R S Q' N' s).comp (map f g hf hg) := by
  apply hom_ext
  intro q n
  simp only [LinearMap.comp_apply, leftAction_mk, map_mk]
  rw [hfS]

/-- **Outer-linear map induced on balanced quotients.**

Let k be a commutative ring, R a semiring, Q a right R-module and N a left R-module, both
additive commutative groups with k-module structures. Write B=B_k(R;Q,N) for the ground
k-tensor quotient by (q·r)⊗n=q⊗(r•n), and q⊠n for its pure class. Let S be a semiring acting
on Q with its action commuting with the k-action and right R-action. On B define
ℓ_s(q⊠n)=(s•q)⊠n. Let Q′,N′ have the corresponding structures and f:Q→Q′, g:N→N′ be k-linear,
with f(q·r)=f(q)·r and g(r•n)=r•g(n). If f is S-equivariant, mapLeft f g is the S-linear map
between the left outer quotient modules, with pure value q⊠n↦f(q)⊠g(n).
-/
def mapLeft (f : Q →ₗ[k] Q') (g : N →ₗ[k] N')
    (hf : ∀ (r : R) (q : Q), f (op r • q) = op r • f q)
    (hg : ∀ (r : R) (n : N), g (r • n) = r • g n)
    (hfS : ∀ (s : S) (q : Q), f (s • q) = s • f q) :
    letI := leftModule k R S Q N
    letI := leftModule k R S Q' N'
    Balanced k R Q N →ₗ[S] Balanced k R Q' N' := by
  let l : Balanced k R Q N →ₗ[k] Balanced k R Q' N' := map f g hf hg
  letI := leftModule k R S Q N
  letI := leftModule k R S Q' N'
  refine { toFun := l, map_add' := l.map_add, map_smul' := ?_ }
  intro s x
  change l (leftAction k R S Q N s x) = leftAction k R S Q' N' s (l x)
  exact congrArg (fun u : Balanced k R Q N →ₗ[k] Balanced k R Q' N' => u x)
    (map_leftAction f g hf hg hfS s)

@[simp, nolint simpNF] -- stated with Balanced.mk for rw; Balanced.mk_apply simplifies LHS
theorem mapLeft_mk (f : Q →ₗ[k] Q') (g : N →ₗ[k] N')
    (hf : ∀ (r : R) (q : Q), f (op r • q) = op r • f q)
    (hg : ∀ (r : R) (n : N), g (r • n) = r • g n)
    (hfS : ∀ (s : S) (q : Q), f (s • q) = s • f q) (q : Q) (n : N) :
    letI := leftModule k R S Q N
    letI := leftModule k R S Q' N'
    mapLeft f g hf hg hfS (mk k R Q N q n) =
      mk k R Q' N' (f q) (g n) := by
  let := leftModule k R S Q N
  let := leftModule k R S Q' N'
  change map f g hf hg (mk k R Q N q n) = _
  exact map_mk f g hf hg q n

end LeftMaps

end TensorProduct.Balanced
