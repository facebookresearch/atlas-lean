/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


/- Actual coefficient balancing of the original Koszul differential. -/
module

public import MathlibExt.Algebra.Homology.KoszulComplex.Finsupp
public import MathlibExt.Algebra.Category.ModuleCat.BalancedTensor
public import MathlibExt.LinearAlgebra.TensorProduct.Balanced.Unitors

/-!
# Balanced coefficients for exterior Koszul complexes

Let k and R be commutative rings with R a k-algebra, let V be an R-module and x : V →ₗ[R] R a
functional. Give M a k-module structure and a right R-module structure. Applying the
coefficient-first balanced tensor functor to the Koszul complex gives degree-n term B k R M
(⋀[R]^n V) and boundary [m, a] ↦ [m, d_x(a)].

On a decomposable wedge, the boundary is the signed deletion sum, moving the scalar (−1)^j
x(a_j) onto M through its right action. If every x(v) annihilates M under that action, every
boundary is zero. With the additional scalar tower k → Rᵐᵒᵖ → M, the degree-zero term is
k-linearly equivalent to M by the zero-exterior equivalence and the balanced unitor.

The four carrier universes u, v, w and z are separate; the coefficient complex takes values in
ModuleCat.{max v w z} k.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct
open MulOpposite

universe u v w z

namespace KoszulComplex

variable (k : Type u) [CommRing k] (R : Type v) [CommRing R] [Algebra k R]
  (V : Type w) [AddCommGroup V] [Module R V]
  (M : Type z) [AddCommGroup M] [Module k M] [Module Rᵐᵒᵖ M]

attribute [local instance] ModuleCat.BalancedTensor.additive

/-- Let k : Type u and R : Type v be commutative rings with R a k-algebra. Let V : Type w be an
R-module, and let M : Type z have k- and Rᵐᵒᵖ-module structures. For x : V →ₗ[R] R, define
balancedCoefficientComplex k R V M x by applying N ↦ B k R M N to the Koszul complex on V and
x. Its degree-n object is B k R M (⋀[R]^n V), in ModuleCat.{max v w z} k, with shape down ℕ. -/
def balancedCoefficientComplex (x : V →ₗ[R] R) :
    ChainComplex (ModuleCat.{max v w z} k) ℕ :=
  ((ModuleCat.BalancedTensor.functor k R M).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (complex R V x)

/-- Let k : Type u and R : Type v be commutative rings with R a k-algebra. Let V : Type w be an
R-module, and let M : Type z have k- and Rᵐᵒᵖ-module structures. For x : V →ₗ[R] R, n : ℕ, m :
M and a : ⋀[R]^(n+1) V, the balanced coefficient differential sends [m, a] to [m, differential
R V x n a]. The exterior powers use the k-action restricted along algebraMap k R. -/
theorem balancedCoefficientComplex_d_mk (x : V →ₗ[R] R) (n : ℕ) (m : M)
    (a : ⋀[R]^(n + 1) V) :
    letI : Module k (⋀[R]^(n + 1) V) := Module.compHom _ (algebraMap k R)
    letI : Module k (⋀[R]^n V) := Module.compHom _ (algebraMap k R)
    ((balancedCoefficientComplex k R V M x).d (n + 1) n).hom
        (TensorProduct.Balanced.mk k R M (⋀[R]^(n + 1) V) m a) =
      TensorProduct.Balanced.mk k R M (⋀[R]^n V) m (differential R V x n a) := by
  letI : Module k (⋀[R]^(n + 1) V) := Module.compHom _ (algebraMap k R)
  letI : Module k (⋀[R]^n V) := Module.compHom _ (algebraMap k R)
  change (ModuleCat.BalancedTensor.map k R M ((complex R V x).d (n + 1) n)).hom
    (TensorProduct.Balanced.mk k R M (⋀[R]^(n + 1) V) m a) = _
  erw [ModuleCat.BalancedTensor.map_mk, complex_d_succ]
  rfl

/-- Let k : Type u and R : Type v be commutative rings with R a k-algebra. Let V : Type w be an
R-module, and let M : Type z have k- and Rᵐᵒᵖ-module structures. For x : V →ₗ[R] R, n : ℕ, m :
M and a : Fin (n + 1) → V, the boundary of [m, a₀ ∧ … ∧ a_n] is ∑ j : Fin (n + 1), [op(((−1 :
R)^j) * x(a_j)) • m, ⋀ q : Fin n, a_(j.succAbove q)]. The undeleted vectors retain their
order, and the full signed coefficient acts on the right-module coefficient through Rᵐᵒᵖ. -/
theorem balancedCoefficientComplex_d_mk_ιMulti (x : V →ₗ[R] R) (n : ℕ)
    (m : M) (a : Fin (n + 1) → V) :
    letI : Module k (⋀[R]^(n + 1) V) := Module.compHom _ (algebraMap k R)
    letI : Module k (⋀[R]^n V) := Module.compHom _ (algebraMap k R)
    ((balancedCoefficientComplex k R V M x).d (n + 1) n).hom
        (TensorProduct.Balanced.mk k R M (⋀[R]^(n + 1) V) m (exteriorPower.ιMulti R (n + 1) a)) =
      ∑ j : Fin (n + 1), TensorProduct.Balanced.mk k R M (⋀[R]^n V)
        (op (((-1 : R) ^ j.val) * x (a j)) • m)
        (exteriorPower.ιMulti R n (fun q => a (j.succAbove q))) := by
  letI : Module k (⋀[R]^(n + 1) V) := Module.compHom _ (algebraMap k R)
  letI : Module k (⋀[R]^n V) := Module.compHom _ (algebraMap k R)
  rw [balancedCoefficientComplex_d_mk, differential_apply_ιMulti]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [smul_smul, ← TensorProduct.Balanced.balance]
  rfl

/-- Let k : Type u and R : Type v be commutative rings with R a k-algebra. Let V : Type w be an
R-module, and let M : Type z have k- and Rᵐᵒᵖ-module structures. Let x : V →ₗ[R] R satisfy
op(x(a)) • m = 0 for every a : V and m : M. Then (balancedCoefficientComplex k R V M x).d (n +
1) n = 0 for every n : ℕ. -/
theorem balancedCoefficientComplex_d_eq_zero (x : V →ₗ[R] R)
    (hx : ∀ (a : V) (m : M), op (x a) • m = 0) (n : ℕ) :
    (balancedCoefficientComplex k R V M x).d (n + 1) n = 0 := by
  letI : Module k (⋀[R]^(n + 1) V) := Module.compHom _ (algebraMap k R)
  letI : Module k (⋀[R]^n V) := Module.compHom _ (algebraMap k R)
  let d : (⋀[R]^(n + 1) V) →ₗ[R] (⋀[R]^n V) := differential R V x n
  let T : Submodule R (⋀[R]^(n + 1) V) :=
    { carrier := {a | ∀ m : M, TensorProduct.Balanced.mk k R M (⋀[R]^n V) m (d a) = 0}
      zero_mem' := by intro m; simp
      add_mem' := by
        intro a b ha hb m
        rw [map_add, map_add, ha, hb, add_zero]
      smul_mem' := by
        intro r a ha m
        rw [map_smul, ← TensorProduct.Balanced.balance]
        exact ha (op r • m) }
  have hspan : Submodule.span R (Set.range (exteriorPower.ιMulti R (n + 1) (M := V))) ≤ T := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩ m
    change TensorProduct.Balanced.mk k R M (⋀[R]^n V) m
      (differential R V x n (exteriorPower.ιMulti R (n + 1) a)) = 0
    rw [differential_apply_ιMulti, map_sum]
    apply Finset.sum_eq_zero
    intro j _
    rw [smul_smul, ← TensorProduct.Balanced.balance, op_mul, mul_smul, hx]
    simp
  have htop : (⊤ : Submodule R (⋀[R]^(n + 1) V)) ≤ T := by
    rw [← exteriorPower.ιMulti_span]
    exact hspan
  letI : Module k ((complex R V x).X (n + 1)) := Module.compHom _ (algebraMap k R)
  letI : Module k ((complex R V x).X n) := Module.compHom _ (algebraMap k R)
  apply ModuleCat.hom_ext
  change (ModuleCat.BalancedTensor.map k R M ((complex R V x).d (n + 1) n)).hom = 0
  change (ModuleCat.BalancedTensor.map k R M ((complex R V x).d (n + 1) n)).hom =
    (0 : TensorProduct.Balanced k R M (⋀[R]^(n + 1) V) →ₗ[k] TensorProduct.Balanced k R M (⋀[R]^n
      V))
  apply TensorProduct.Balanced.hom_ext
  intro m a
  erw [ModuleCat.BalancedTensor.map_mk, complex_d_succ]
  let a₀ : ⋀[R]^(n + 1) V := a
  have ha₀ : a₀ ∈ T := htop (by trivial)
  exact ha₀ m

section DegreeZero

variable [IsScalarTower k Rᵐᵒᵖ M]

/-- Let k : Type u and R : Type v be commutative rings with R a k-algebra. Let V : Type w be an
R-module, and let M : Type z have k- and Rᵐᵒᵖ-module structures. Assume also IsScalarTower k
Rᵐᵒᵖ M. For any x : V →ₗ[R] R, the degree-zero object B k R M (⋀[R]^0 V) is k-linearly
equivalent to M. The equivalence first identifies ⋀[R]^0 V with R, then contracts the regular
factor by the right action on M. -/
def balancedCoefficientDegreeZeroEquiv (x : V →ₗ[R] R) :
    (balancedCoefficientComplex k R V M x).X 0 ≃ₗ[k] M := by
  letI : Module k (⋀[R]^0 V) := Module.compHom _ (algebraMap k R)
  letI : IsScalarTower k R (⋀[R]^0 V) := IsScalarTower.of_compHom k R (⋀[R]^0 V)
  let e : (⋀[R]^0 V) ≃ₗ[k] R := (exteriorPower.zeroEquiv R V).restrictScalars k
  exact (TensorProduct.Balanced.congr (LinearEquiv.refl k M) e
    (fun _ _ => rfl) (fun r a => (exteriorPower.zeroEquiv R V).map_smul r a)).trans
      (TensorProduct.Balanced.rightUnitor k R M)

/-- Let k : Type u and R : Type v be commutative rings with R a k-algebra. Let V : Type w be an
R-module, and let M : Type z have k- and Rᵐᵒᵖ-module structures. Assume the scalar tower k →
Rᵐᵒᵖ → M. For x : V →ₗ[R] R, m : M and a : ⋀[R]^0 V, balancedCoefficientDegreeZeroEquiv sends
[m, a] to op(exteriorPower.zeroEquiv R V a) • m. -/
theorem balancedCoefficientDegreeZeroEquiv_mk (x : V →ₗ[R] R) (m : M) (a : ⋀[R]^0 V) :
    letI : Module k (⋀[R]^0 V) := Module.compHom _ (algebraMap k R)
    balancedCoefficientDegreeZeroEquiv k R V M x
        (TensorProduct.Balanced.mk k R M (⋀[R]^0 V) m a) =
      op (exteriorPower.zeroEquiv R V a) • m := by
  letI : Module k (⋀[R]^0 V) := Module.compHom _ (algebraMap k R)
  letI : IsScalarTower k R (⋀[R]^0 V) := IsScalarTower.of_compHom k R (⋀[R]^0 V)
  change TensorProduct.Balanced.rightUnitor k R M
    (TensorProduct.Balanced.congr (LinearEquiv.refl k M)
      ((exteriorPower.zeroEquiv R V).restrictScalars k)
      (fun _ _ => rfl) (fun r z => (exteriorPower.zeroEquiv R V).map_smul r z)
      (TensorProduct.Balanced.mk k R M (⋀[R]^0 V) m a)) = _
  erw [TensorProduct.Balanced.congr_mk, TensorProduct.Balanced.rightUnitor_mk]
  rfl

end DegreeZero

end KoszulComplex
