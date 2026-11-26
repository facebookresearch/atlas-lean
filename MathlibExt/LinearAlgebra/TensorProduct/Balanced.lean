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

public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Balanced tensor quotients over an acting semiring

Let k be a commutative ring, R a semiring, and M,N additive commutative groups with k-module
structures, a right R-action on M and a left R-action on N. Put
B_k(R;M,N)=(M⊗_kN)/span_k{(m·r)⊗n-m⊗(r•n)} and write m⊠n for the class of m⊗n. The pure
pairing is k-bilinear and R-balanced, and a balanced k-bilinear map descends uniquely to this
quotient. For a k-algebra R and compatible right module M, cancellation identifies
B_k(R;M,R⊗_kV) with M⊗_kV. Carrier universes may be independent.
-/

@[expose] public section

open scoped TensorProduct
open MulOpposite

universe u v w z w' z' t

namespace TensorProduct

section Quotient

variable (k : Type u) (R : Type v) (M : Type w) (N : Type z)
  [CommRing k] [Semiring R] [AddCommGroup M] [AddCommGroup N]
  [Module k M] [Module k N] [Module Rᵐᵒᵖ M] [Module R N]

/-- **Ground-linear balancing relations.**

Let k be a commutative ring, R a semiring, and M,N additive commutative groups with k-module
structures, a right R-action on M and a left R-action on N. Put
B_k(R;M,N)=(M⊗_kN)/span_k{(m·r)⊗n-m⊗(r•n)} and write m⊠n for the class of m⊗n. The submodule
balanceRelations k R M N is the k-span of the displayed balancing differences in M⊗_kN.
-/
def balanceRelations : Submodule k (M ⊗[k] N) :=
  Submodule.span k {x | ∃ (r : R) (m : M) (n : N),
    x = (op r • m) ⊗ₜ[k] n - m ⊗ₜ[k] (r • n)}

/-- **Balanced quotient of the ground tensor product.**

Let k be a commutative ring, R a semiring, and M,N additive commutative groups with k-module
structures, a right R-action on M and a left R-action on N. Put
B_k(R;M,N)=(M⊗_kN)/span_k{(m·r)⊗n-m⊗(r•n)} and write m⊠n for the class of m⊗n. The type
Balanced k R M N is B_k(R;M,N), with its quotient k-module structure.
-/
abbrev Balanced := (M ⊗[k] N) ⧸ balanceRelations k R M N

namespace Balanced

/-- **Bilinear pure pairing into the balanced quotient.**

Let k be a commutative ring, R a semiring, and M,N additive commutative groups with k-module
structures, a right R-action on M and a left R-action on N. Put
B_k(R;M,N)=(M⊗_kN)/span_k{(m·r)⊗n-m⊗(r•n)} and write m⊠n for the class of m⊗n. The map
Balanced.mk k R M N:M→ₗ[k](N→ₗ[k]B_k(R;M,N)) sends (m,n) to m⊠n.
-/
def mk : M →ₗ[k] N →ₗ[k] Balanced k R M N :=
  (TensorProduct.mk k M N).compr₂ (balanceRelations k R M N).mkQ

@[simp]
theorem mk_apply (m : M) (n : N) :
    mk k R M N m n = (balanceRelations k R M N).mkQ (m ⊗ₜ[k] n) :=
  rfl

/-- **Moving an acting scalar across a balanced class.**

Let k be a commutative ring, R a semiring, and M,N additive commutative groups with k-module
structures, a right R-action on M and a left R-action on N. Put
B_k(R;M,N)=(M⊗_kN)/span_k{(m·r)⊗n-m⊗(r•n)} and write m⊠n for the class of m⊗n. For r∈R, m∈M
and n∈N, (m·r)⊠n=m⊠(r•n).
-/
theorem balance (r : R) (m : M) (n : N) :
    mk k R M N (op r • m) n = mk k R M N m (r • n) := by
  change Submodule.Quotient.mk ((op r • m) ⊗ₜ[k] n) =
    (Submodule.Quotient.mk (m ⊗ₜ[k] (r • n)) : Balanced k R M N)
  exact (Submodule.Quotient.eq (balanceRelations k R M N)).mpr
    (Submodule.subset_span ⟨r, m, n, rfl⟩)

variable {k R M N}
variable {P : Type t} [AddCommGroup P] [Module k P]

/-- **Lift of a balanced bilinear map.**

Let k be a commutative ring, R a semiring, and M,N additive commutative groups with k-module
structures, a right R-action on M and a left R-action on N. Put
B_k(R;M,N)=(M⊗_kN)/span_k{(m·r)⊗n-m⊗(r•n)} and write m⊠n for the class of m⊗n. For a k-module
P and k-bilinear f:M×N→P with f(m·r,n)=f(m,r•n), Balanced.lift f hf:B_k(R;M,N)→ₗ[k]P has value
m⊠n↦f(m,n).
-/
def lift (f : M →ₗ[k] N →ₗ[k] P)
    (hf : ∀ (r : R) (m : M) (n : N), f (op r • m) n = f m (r • n)) :
    Balanced k R M N →ₗ[k] P :=
  (balanceRelations k R M N).liftQ (TensorProduct.lift f) (by
    apply Submodule.span_le.mpr
    rintro x ⟨r, m, n, rfl⟩
    apply LinearMap.mem_ker.mpr
    rw [map_sub, TensorProduct.lift.tmul, TensorProduct.lift.tmul,
      hf r m n, sub_self])

@[simp, nolint simpNF] -- stated with Balanced.mk for rw; Balanced.mk_apply simplifies LHS
theorem lift_mk (f : M →ₗ[k] N →ₗ[k] P)
    (hf : ∀ (r : R) (m : M) (n : N), f (op r • m) n = f m (r • n))
    (m : M) (n : N) : lift f hf (mk k R M N m n) = f m n :=
  rfl

/-- **Pure balanced classes determine a linear map.**

Let k be a commutative ring, R a semiring, and M,N additive commutative groups with k-module
structures, a right R-action on M and a left R-action on N. Put
B_k(R;M,N)=(M⊗_kN)/span_k{(m·r)⊗n-m⊗(r•n)} and write m⊠n for the class of m⊗n. If k-linear
F,G:B_k(R;M,N)→P agree on every m⊠n, then F=G.
-/
theorem hom_ext {f g : Balanced k R M N →ₗ[k] P}
    (h : ∀ (m : M) (n : N), f (mk k R M N m n) = g (mk k R M N m n)) :
    f = g := by
  apply (balanceRelations k R M N).quot_hom_ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul m n => exact h m n
  | add x y hx hy =>
      change f ((balanceRelations k R M N).mkQ (x + y)) =
        g ((balanceRelations k R M N).mkQ (x + y))
      simp only [map_add]
      change f (Submodule.Quotient.mk x) + f (Submodule.Quotient.mk y) =
        g (Submodule.Quotient.mk x) + g (Submodule.Quotient.mk y)
      rw [hx, hy]

variable {M' : Type w'} {N' : Type z'}
  [AddCommGroup M'] [AddCommGroup N'] [Module k M'] [Module k N']
  [Module Rᵐᵒᵖ M'] [Module R N']

/-- **Equivariant maps preserve the balancing submodule.**

Let k be a commutative ring, R a semiring, and M,N additive commutative groups with k-module
structures, a right R-action on M and a left R-action on N. Put
B_k(R;M,N)=(M⊗_kN)/span_k{(m·r)⊗n-m⊗(r•n)} and write m⊠n for the class of m⊗n. Let M′,N′ have
the same scalar structures and f:M→M′, g:N→N′ be k-linear maps respecting the right and left
R-actions. Then (f⊗g) sends the balancing submodule for M,N into that for M′,N′.
-/
theorem map_preserves_balanceRelations (f : M →ₗ[k] M') (g : N →ₗ[k] N')
    (hf : ∀ (r : R) (m : M), f (op r • m) = op r • f m)
    (hg : ∀ (r : R) (n : N), g (r • n) = r • g n) :
    balanceRelations k R M N ≤
      Submodule.comap (TensorProduct.map f g) (balanceRelations k R M' N') := by
  apply Submodule.span_le.mpr
  rintro x ⟨r, m, n, rfl⟩
  change (TensorProduct.map f g)
      ((op r • m) ⊗ₜ[k] n - m ⊗ₜ[k] (r • n)) ∈
    balanceRelations k R M' N'
  rw [map_sub, TensorProduct.map_tmul, TensorProduct.map_tmul, hf, hg]
  exact Submodule.subset_span ⟨r, f m, g n, rfl⟩

/-- **Balanced quotient map induced by factor maps.**

Let k be a commutative ring, R a semiring, and M,N additive commutative groups with k-module
structures, a right R-action on M and a left R-action on N. Put
B_k(R;M,N)=(M⊗_kN)/span_k{(m·r)⊗n-m⊗(r•n)} and write m⊠n for the class of m⊗n. For k-linear
R-equivariant f:M→M′ and g:N→N′ between modules of the same kind, Balanced.map f g sends m⊠n
to f(m)⊠g(n).
-/
def map (f : M →ₗ[k] M') (g : N →ₗ[k] N')
    (hf : ∀ (r : R) (m : M), f (op r • m) = op r • f m)
    (hg : ∀ (r : R) (n : N), g (r • n) = r • g n) :
    Balanced k R M N →ₗ[k] Balanced k R M' N' :=
  (balanceRelations k R M N).mapQ (balanceRelations k R M' N')
    (TensorProduct.map f g) (map_preserves_balanceRelations f g hf hg)

/-- **Balanced factor map on an arbitrary tensor representative.**

Let k be a commutative ring, R a semiring, and M,N additive commutative groups with k-module
structures, a right R-action on M and a left R-action on N. Put
B_k(R;M,N)=(M⊗_kN)/span_k{(m·r)⊗n-m⊗(r•n)} and write m⊠n for the class of m⊗n. For k-linear
R-equivariant f:M→M′ and g:N→N′, and quotient projections q,q′, Balanced.map f g
(q(z))=q′((f⊗g)(z)) for every z∈M⊗_kN.
-/
theorem map_mkQ (f : M →ₗ[k] M') (g : N →ₗ[k] N')
    (hf : ∀ (r : R) (m : M), f (op r • m) = op r • f m)
    (hg : ∀ (r : R) (n : N), g (r • n) = r • g n) (x : M ⊗[k] N) :
    map f g hf hg ((balanceRelations k R M N).mkQ x) =
      (balanceRelations k R M' N').mkQ (TensorProduct.map f g x) := by
  exact LinearMap.congr_fun
    (Submodule.mapQ_mkQ (balanceRelations k R M N) (balanceRelations k R M' N')
      (TensorProduct.map f g) (h := map_preserves_balanceRelations f g hf hg)) x

@[simp, nolint simpNF] -- stated with Balanced.mk for rw; Balanced.mk_apply simplifies LHS
theorem map_mk (f : M →ₗ[k] M') (g : N →ₗ[k] N')
    (hf : ∀ (r : R) (m : M), f (op r • m) = op r • f m)
    (hg : ∀ (r : R) (n : N), g (r • n) = r • g n)
    (m : M) (n : N) :
    map f g hf hg (mk k R M N m n) = mk k R M' N' (f m) (g n) := by
  change (balanceRelations k R M' N').mkQ
      ((TensorProduct.map f g) (m ⊗ₜ[k] n)) = _
  rw [TensorProduct.map_tmul]
  rfl

theorem map_id :
    map (k := k) (R := R) (M := M) (N := N) (M' := M) (N' := N)
      (LinearMap.id : M →ₗ[k] M) (LinearMap.id : N →ₗ[k] N)
      (fun _ _ => rfl) (fun _ _ => rfl) =
        (LinearMap.id : Balanced k R M N →ₗ[k] Balanced k R M N) := by
  apply hom_ext (k := k) (R := R) (M := M) (N := N)
  intro m n
  rw [map_mk]
  rfl

/-- **Balanced quotient equivalence from factor equivalences.**

Let k be a commutative ring, R a semiring, and M,N additive commutative groups with k-module
structures, a right R-action on M and a left R-action on N. Put
B_k(R;M,N)=(M⊗_kN)/span_k{(m·r)⊗n-m⊗(r•n)} and write m⊠n for the class of m⊗n. For k-linear
equivalences f:M≃M′ and g:N≃N′ respecting their R-actions, Balanced.congr f
g:B_k(R;M,N)≃ₗ[k]B_k(R;M′,N′) has pure value m⊠n↦f(m)⊠g(n).
-/
def congr (f : M ≃ₗ[k] M') (g : N ≃ₗ[k] N')
    (hf : ∀ (r : R) (m : M), f (op r • m) = op r • f m)
    (hg : ∀ (r : R) (n : N), g (r • n) = r • g n) :
    Balanced k R M N ≃ₗ[k] Balanced k R M' N' := by
  have hf' : ∀ (r : R) (m : M'), f.symm (op r • m) = op r • f.symm m := by
    intro r m
    apply f.injective
    rw [f.apply_symm_apply, hf, f.apply_symm_apply]
  have hg' : ∀ (r : R) (n : N'), g.symm (r • n) = r • g.symm n := by
    intro r n
    apply g.injective
    rw [g.apply_symm_apply, hg, g.apply_symm_apply]
  refine LinearEquiv.ofLinearMap
    (map f.toLinearMap g.toLinearMap hf hg)
    (map f.symm.toLinearMap g.symm.toLinearMap hf' hg') ?_ ?_
  · apply hom_ext
    intro m n
    simp only [LinearMap.comp_apply, map_mk, LinearMap.id_apply]
    change mk k R M' N' (f (f.symm m)) (g (g.symm n)) = mk k R M' N' m n
    rw [f.apply_symm_apply, g.apply_symm_apply]
  · apply hom_ext
    intro m n
    simp only [LinearMap.comp_apply, map_mk, LinearMap.id_apply]
    change mk k R M N (f.symm (f m)) (g.symm (g n)) = mk k R M N m n
    rw [f.symm_apply_apply, g.symm_apply_apply]

@[simp, nolint simpNF] -- stated with Balanced.mk for rw; Balanced.mk_apply simplifies LHS
theorem congr_mk (f : M ≃ₗ[k] M') (g : N ≃ₗ[k] N')
    (hf : ∀ (r : R) (m : M), f (op r • m) = op r • f m)
    (hg : ∀ (r : R) (n : N), g (r • n) = r • g n)
    (m : M) (n : N) :
    congr f g hf hg (mk k R M N m n) = mk k R M' N' (f m) (g n) :=
  map_mk f.toLinearMap g.toLinearMap hf hg m n

end Balanced
end Quotient

section FreeAction

variable (k : Type u) (R : Type v) (M : Type w) (V : Type z)
  [CommRing k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module k M] [Module Rᵐᵒᵖ M]
  [SMulCommClass k Rᵐᵒᵖ M] [IsScalarTower k Rᵐᵒᵖ M]
  [AddCommGroup V] [Module k V]

namespace Balanced

/-- **Absorption of the regular factor into a right module.**

Let k be a commutative ring, R a k-algebra that may be noncommutative, M a right R-module with
compatible commuting k-actions, and V a k-module. For the k-balanced quotient B_k(R;M,R⊗_kV),
free-factor cancellation sends m⊠(r⊗v) to (m·r)⊗v. The k-bilinear map absorb k R M
V:M×(R⊗_kV)→M⊗_kV is (m,r⊗v)↦(m·r)⊗v.
-/
def absorb : M →ₗ[k] (R ⊗[k] V) →ₗ[k] (M ⊗[k] V) where
  toFun m := TensorProduct.lift
    ((TensorProduct.mk k M V).comp
      (show R →ₗ[k] M from
      { toFun := fun r => op r • m
        map_add' := by intro r₁ r₂; rw [op_add, add_smul]
        map_smul' := by
          intro c r
          rw [RingHom.id_apply]
          change (c • (op r : Rᵐᵒᵖ)) • m = c • ((op r : Rᵐᵒᵖ) • m)
          exact smul_assoc c (op r) m }))
  map_add' := by
    intro m₁ m₂
    apply TensorProduct.ext'
    intro r v
    change (op r • (m₁ + m₂)) ⊗ₜ[k] v =
      (op r • m₁) ⊗ₜ[k] v + (op r • m₂) ⊗ₜ[k] v
    rw [smul_add, TensorProduct.add_tmul]
  map_smul' := by
    intro c m
    rw [RingHom.id_apply]
    apply TensorProduct.ext'
    intro r v
    change (op r • (c • m)) ⊗ₜ[k] v = c • ((op r • m) ⊗ₜ[k] v)
    rw [← smul_comm c (op r) m, TensorProduct.smul_tmul']

@[simp]
theorem absorb_tmul (m : M) (r : R) (v : V) :
    absorb k R M V m (r ⊗ₜ[k] v) = (op r • m) ⊗ₜ[k] v :=
  rfl

/-- **Absorption respects the acting-ring balance.**

Let k be a commutative ring, R a k-algebra that may be noncommutative, M a right R-module with
compatible commuting k-actions, and V a k-module. For the k-balanced quotient B_k(R;M,R⊗_kV),
free-factor cancellation sends m⊠(r⊗v) to (m·r)⊗v. For r∈R, m∈M and z∈R⊗_kV,
absorb(m·r,z)=absorb(m,r•z), where the left R-action is on the first factor of R⊗_kV.
-/
theorem absorb_balanced (r : R) (m : M) (x : R ⊗[k] V) :
    absorb k R M V (op r • m) x = absorb k R M V m (r • x) := by
  induction x using TensorProduct.inductionOn with
  | tmul s v =>
      rw [TensorProduct.smul_tmul', smul_eq_mul, absorb_tmul, absorb_tmul]
      apply congrArg (fun q : M => q ⊗ₜ[k] v)
      rw [← mul_smul, ← op_mul]
  | add x y hx hy =>
      rw [map_add, smul_add, map_add, hx, hy]

/-- **Cancellation map from a free-action balanced quotient.**

Let k be a commutative ring, R a k-algebra that may be noncommutative, M a right R-module with
compatible commuting k-actions, and V a k-module. For the k-balanced quotient B_k(R;M,R⊗_kV),
free-factor cancellation sends m⊠(r⊗v) to (m·r)⊗v. The k-linear map cancel k R M V sends
m⊠(r⊗v) to (m·r)⊗v.
-/
def cancel : Balanced k R M (R ⊗[k] V) →ₗ[k] (M ⊗[k] V) :=
  lift (absorb k R M V) (absorb_balanced k R M V)

@[simp, nolint simpNF] -- stated with Balanced.mk for rw; Balanced.mk_apply simplifies LHS
theorem cancel_mk_tmul (m : M) (r : R) (v : V) :
    cancel k R M V (mk k R M (R ⊗[k] V) m (r ⊗ₜ[k] v)) =
      (op r • m) ⊗ₜ[k] v :=
  rfl

/-- **Unit insertion into a free-action balanced quotient.**

Let k be a commutative ring, R a k-algebra that may be noncommutative, M a right R-module with
compatible commuting k-actions, and V a k-module. For the k-balanced quotient B_k(R;M,R⊗_kV),
free-factor cancellation sends m⊠(r⊗v) to (m·r)⊗v. The k-linear map insert k R M
V:M⊗_kV→B_k(R;M,R⊗_kV) sends m⊗v to m⊠(1_R⊗v).
-/
def insert : (M ⊗[k] V) →ₗ[k] Balanced k R M (R ⊗[k] V) :=
  TensorProduct.lift
    ((mk k R M (R ⊗[k] V)).compl₂ (TensorProduct.mk k R V 1))

omit [SMulCommClass k Rᵐᵒᵖ M] [IsScalarTower k Rᵐᵒᵖ M] in
@[simp]
theorem insert_tmul (m : M) (v : V) :
    insert k R M V (m ⊗ₜ[k] v) =
      mk k R M (R ⊗[k] V) m ((1 : R) ⊗ₜ[k] v) :=
  rfl

theorem cancel_insert :
    (cancel k R M V).comp (insert k R M V) = LinearMap.id := by
  apply TensorProduct.ext'
  intro m v
  change cancel k R M V
      (mk k R M (R ⊗[k] V) m ((1 : R) ⊗ₜ[k] v)) = m ⊗ₜ[k] v
  rw [cancel_mk_tmul, op_one, one_smul]

theorem insert_cancel :
    (insert k R M V).comp (cancel k R M V) = LinearMap.id := by
  apply hom_ext
  intro m x
  induction x using TensorProduct.inductionOn with
  | tmul r v =>
      change insert k R M V
          (cancel k R M V (mk k R M (R ⊗[k] V) m (r ⊗ₜ[k] v))) =
        mk k R M (R ⊗[k] V) m (r ⊗ₜ[k] v)
      rw [cancel_mk_tmul, insert_tmul]
      simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using
        balance k R M (R ⊗[k] V) r m ((1 : R) ⊗ₜ[k] v)
  | add x y hx hy =>
      simp only [LinearMap.comp_apply, map_add, LinearMap.id_apply] at hx hy ⊢
      rw [hx, hy]

/-- **Free-action balanced tensor cancellation.**

Let k be a commutative ring, R a k-algebra that may be noncommutative, M a right R-module with
compatible commuting k-actions, and V a k-module. For the k-balanced quotient B_k(R;M,R⊗_kV),
free-factor cancellation sends m⊠(r⊗v) to (m·r)⊗v. The k-linear equivalence cancelEquiv k R M
V has inverse m⊗v↦m⊠(1_R⊗v). The coefficient modules M,V are arbitrary.
-/
def cancelEquiv : Balanced k R M (R ⊗[k] V) ≃ₗ[k] (M ⊗[k] V) :=
  LinearEquiv.ofLinearMap (cancel k R M V) (insert k R M V)
    (cancel_insert k R M V) (insert_cancel k R M V)

@[simp, nolint simpNF] -- stated with Balanced.mk for rw; Balanced.mk_apply simplifies LHS
theorem cancelEquiv_mk_tmul (m : M) (r : R) (v : V) :
    cancelEquiv k R M V (mk k R M (R ⊗[k] V) m (r ⊗ₜ[k] v)) =
      (op r • m) ⊗ₜ[k] v :=
  cancel_mk_tmul k R M V m r v

@[simp]
theorem cancelEquiv_symm_tmul (m : M) (v : V) :
    (cancelEquiv k R M V).symm (m ⊗ₜ[k] v) =
      mk k R M (R ⊗[k] V) m ((1 : R) ⊗ₜ[k] v) :=
  rfl

end Balanced
end FreeAction
end TensorProduct
