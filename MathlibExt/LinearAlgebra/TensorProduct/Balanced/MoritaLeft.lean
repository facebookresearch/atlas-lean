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

public import MathlibExt.LinearAlgebra.TensorProduct.Balanced.Associator
public import MathlibExt.LinearAlgebra.TensorProduct.Balanced.Unitors

/-!
# Return from a balanced bimodule pair on left modules

Let k be a commutative ring, R and S possibly noncommutative k-algebras,
P an R–S bimodule, Q an S–R bimodule, and M a left R-module.
All module actions are compatible with k and the actions on each bimodule
commute. The scalar and carrier universes are independent.

A right R-linear equivalence u : P ⊗_S Q ≅ R gives a k-linear return
P ⊗_S (Q ⊗_R M) ≅ M, with pure value
[p ⊗ (q ⊗ m)] ↦ u([p ⊗ q]) • m.
Its inverse inserts u⁻¹(1) and then reassociates.
If u is also left R-equivariant, the return is R-linear for the outer
R-action on the first factor P.
-/

@[expose] public section

noncomputable section

open MulOpposite
open scoped TensorProduct

universe u r s p q m

namespace TensorProduct.Balanced.Morita

variable (k : Type u) [CommRing k]
  (R : Type r) [Ring R] [Algebra k R]
  (S : Type s) [Ring S] [Algebra k S]
  (P : Type p) [AddCommGroup P] [Module k P]
  [Module R P] [Module Sᵐᵒᵖ P] [SMulCommClass R Sᵐᵒᵖ P]
  [IsScalarTower k R P] [IsScalarTower k Sᵐᵒᵖ P]
  (Q : Type q) [AddCommGroup Q] [Module k Q]
  [Module S Q] [Module Rᵐᵒᵖ Q] [SMulCommClass S Rᵐᵒᵖ Q]
  [IsScalarTower k S Q] [IsScalarTower k Rᵐᵒᵖ Q]
  (M : Type m) [AddCommGroup M] [Module k M] [Module R M]
  [IsScalarTower k R M]

/-- Let k be a commutative ring and R, S k-algebras which are rings.
Let P be an R–S bimodule, Q an S–R bimodule, and M a left R-module,
all with compatible k-actions; the two actions on each bimodule commute.
This is the right-parenthesized balanced carrier
P ⊗_S (Q ⊗_R M), with the inner left S-action induced from Q. -/
abbrev leftReturnSource := assocTarget k S R P Q M

/-- Let k be a commutative ring and R, S k-algebras which are rings.
Let P be an R–S bimodule, Q an S–R bimodule, and M a left R-module,
all with compatible k-actions; the two actions on each bimodule commute.
The outer left R-module structure on P ⊗_S (Q ⊗_R M) is induced
from P: r [p ⊗ (q ⊗ m)] = [r p ⊗ (q ⊗ m)]. -/
abbrev leftReturnModule : Module R (leftReturnSource k R S P Q M) := by
  letI := leftModule k R S Q M
  exact leftModule k S R P (TensorProduct.Balanced k R Q M)

variable
  (u : letI := leftModule k S R P Q
    letI := rightModule k S R P Q
    TensorProduct.Balanced k S P Q ≃ₗ[Rᵐᵒᵖ] R)

include u in
/-- Let k be a commutative ring and R, S k-algebras which are rings.
Let P be an R–S bimodule, Q an S–R bimodule, and M a left R-module,
all with compatible k-actions; the two actions on each bimodule commute.
Suppose u : P ⊗_S Q ≅ R is a right R-linear equivalence.
This is the k-linear return P ⊗_S (Q ⊗_R M) ≅ M, obtained by
moving to (P ⊗_S Q) ⊗_R M, applying u to the first factor, and
using the left tensor unitor of M. -/
def leftReturnRaw : leftReturnSource k R S P Q M ≃ₗ[k] M := by
  let B := TensorProduct.Balanced k S P Q
  letI := leftModule k S R P Q
  letI := rightModule k S R P Q
  letI := rightScalarTower k S R P Q
  let e : B ≃ₗ[k] R := u.restrictScalars k
  exact (assoc k S R P Q M).symm.trans
    ((congr e (LinearEquiv.refl k M)
      (fun r b => u.map_smul (op r) b) (fun _ _ => rfl)).trans
        (leftUnitor k R M))

set_option linter.unusedSectionVars false in
/-- Let k be a commutative ring and R, S k-algebras which are rings.
Let P be an R–S bimodule, Q an S–R bimodule, and M a left R-module,
all with compatible k-actions; the two actions on each bimodule commute.
Suppose u : P ⊗_S Q ≅ R is a right R-linear equivalence.
For any balanced class b ∈ P ⊗_S Q and m ∈ M, the return sends
assoc([b ⊗ m]) to u(b) • m. This formula applies to arbitrary b,
not only to a pure P–Q tensor. -/
@[nolint unusedArguments] -- omitting them cascades via `leftReturnRaw_mk` into `leftReturn`
theorem leftReturnRaw_assoc_mk (b : TensorProduct.Balanced k S P Q) (m : M) :
    letI := rightModule k S R P Q
    leftReturnRaw k R S P Q M u
        (assoc k S R P Q M (mk k R (TensorProduct.Balanced k S P Q) M b m)) =
      u b • m := by
  let := leftModule k S R P Q
  let := rightModule k S R P Q
  let := rightScalarTower k S R P Q
  let B := TensorProduct.Balanced k S P Q
  let e : B ≃ₗ[k] R := u.restrictScalars k
  have hf : ∀ (r : R) (b : B), e (op r • b) = op r • e b := by
    intro r b
    change u (op r • b) = op r • u b
    exact u.map_smul (op r) b
  have hg : ∀ (r : R) (m : M), (LinearEquiv.refl k M) (r • m) =
      r • (LinearEquiv.refl k M) m := fun _ _ => rfl
  rw [leftReturnRaw, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    LinearEquiv.trans_apply]
  change (leftUnitor k R M)
      ((congr (k := k) (R := R) (M := B) (N := M) (M' := R) (N' := M)
        e (LinearEquiv.refl k M) hf hg) (mk k R B M b m)) = u b • m
  have h := congr_mk (k := k) (R := R) (M := B) (N := M)
    (M' := R) (N' := M) e (LinearEquiv.refl k M) hf hg b m
  exact (congrArg (fun x : TensorProduct.Balanced k R R M => leftUnitor k R M x) h).trans
    (leftUnitor_mk k R M (e b) ((LinearEquiv.refl k M) m))

/-- Let k be a commutative ring and R, S k-algebras which are rings.
Let P be an R–S bimodule, Q an S–R bimodule, and M a left R-module,
all with compatible k-actions; the two actions on each bimodule commute.
Suppose u : P ⊗_S Q ≅ R is a right R-linear equivalence.
For p ∈ P, q ∈ Q and m ∈ M, the return has value
[p ⊗ (q ⊗ m)] ↦ u([p ⊗ q]) • m.
The contraction acts on the left of the final coefficient m. -/
@[simp, nolint simpNF] -- stated with Balanced.mk for rw; Balanced.mk_apply simplifies LHS
theorem leftReturnRaw_mk (p : P) (q : Q) (m : M) :
    letI := leftModule k R S Q M
    leftReturnRaw k R S P Q M u
        (mk k S P (TensorProduct.Balanced k R Q M) p (mk k R Q M q m)) =
      u (mk k S P Q p q) • m := by
  let := leftModule k R S Q M
  let := rightModule k S R P Q
  have h := leftReturnRaw_assoc_mk k R S P Q M u (mk k S P Q p q) m
  rw [assoc_mk_mk] at h
  exact h

/-- Let k be a commutative ring and R, S k-algebras which are rings.
Let P be an R–S bimodule, Q an S–R bimodule, and M a left R-module,
all with compatible k-actions; the two actions on each bimodule commute.
Suppose u : P ⊗_S Q ≅ R is a right R-linear equivalence.
The inverse return sends m ∈ M to
assoc([u⁻¹(1) ⊗ m]) ∈ P ⊗_S (Q ⊗_R M),
where u⁻¹(1) is a balanced class in P ⊗_S Q. -/
theorem leftReturnRaw_symm (m : M) :
    letI := rightModule k S R P Q
    (leftReturnRaw k R S P Q M u).symm m =
      assoc k S R P Q M
        (mk k R (TensorProduct.Balanced k S P Q) M (u.symm 1) m) := by
  let := rightModule k S R P Q
  apply (leftReturnRaw k R S P Q M u).injective
  rw [LinearEquiv.apply_symm_apply, leftReturnRaw_assoc_mk,
    LinearEquiv.apply_symm_apply, one_smul]

variable
  (hu : letI := leftModule k S R P Q
    letI := rightModule k S R P Q
    ∀ (r : R) (b : TensorProduct.Balanced k S P Q), u (r • b) = r * u b)

include u hu in
/-- Let k be a commutative ring and R, S k-algebras which are rings.
Let P be an R–S bimodule, Q an S–R bimodule, and M a left R-module,
all with compatible k-actions; the two actions on each bimodule commute.
Suppose u : P ⊗_S Q ≅ R is a right R-linear equivalence.
If u also satisfies u(r • b) = r u(b) for the outer left R-action,
the return P ⊗_S (Q ⊗_R M) ≅ M is R-linear, with the source R-action
induced from the first factor P. -/
def leftReturn :
    letI := leftReturnModule k R S P Q M
    leftReturnSource k R S P Q M ≃ₗ[R] M := by
  letI := leftModule k R S Q M
  letI := leftReturnModule k R S P Q M
  let E := leftReturnRaw k R S P Q M u
  refine E.toAddEquiv.toLinearEquiv ?_
  intro r x
  let C := TensorProduct.Balanced k R Q M
  have h : E.toLinearMap.toAddMonoidHom.comp
      (DistribSMul.toAddMonoidHom (leftReturnSource k R S P Q M) r) =
      (DistribSMul.toAddMonoidHom M r).comp E.toLinearMap.toAddMonoidHom := by
    apply addHom_ext k S P C
    intro p c
    have hc : (E.toLinearMap.toAddMonoidHom.comp
        (DistribSMul.toAddMonoidHom (leftReturnSource k R S P Q M) r)).comp
          ((mk k S P C p).toAddMonoidHom) =
        ((DistribSMul.toAddMonoidHom M r).comp E.toLinearMap.toAddMonoidHom).comp
          ((mk k S P C p).toAddMonoidHom) := by
      apply addHom_ext k R Q M
      intro q m
      change E (leftAction k S R P C r (mk k S P C p (mk k R Q M q m))) =
        r • E (mk k S P C p (mk k R Q M q m))
      rw [leftAction_mk]
      change leftReturnRaw k R S P Q M u
          (mk k S P C (r • p) (mk k R Q M q m)) =
        r • leftReturnRaw k R S P Q M u (mk k S P C p (mk k R Q M q m))
      rw [leftReturnRaw_mk, leftReturnRaw_mk]
      have huP : u (mk k S P Q (r • p) q) = r * u (mk k S P Q p q) := by
        let := leftModule k S R P Q
        rw [← leftModule_smul_mk k S R P Q]
        exact hu r (mk k S P Q p q)
      rw [huP, mul_smul]
    exact DFunLike.congr_fun hc c
  exact DFunLike.congr_fun h x

/-- Let k be a commutative ring and R, S k-algebras which are rings.
Let P be an R–S bimodule, Q an S–R bimodule, and M a left R-module,
all with compatible k-actions; the two actions on each bimodule commute.
Suppose u : P ⊗_S Q ≅ R is a right R-linear equivalence.
If u is also left R-equivariant, the R-linear return and the
k-linear return have the same value on every element of
P ⊗_S (Q ⊗_R M). -/
@[simp]
theorem leftReturn_apply (x : leftReturnSource k R S P Q M) :
    leftReturn k R S P Q M u hu x = leftReturnRaw k R S P Q M u x := rfl

/-- Let k be a commutative ring and R, S k-algebras which are rings.
Let P be an R–S bimodule, Q an S–R bimodule, and M a left R-module,
all with compatible k-actions; the two actions on each bimodule commute.
Suppose u : P ⊗_S Q ≅ R is a right R-linear equivalence.
If u is also left R-equivariant, the R-linear return has pure value
[p ⊗ (q ⊗ m)] ↦ u([p ⊗ q]) • m. -/
@[simp, nolint simpNF] -- stated with Balanced.mk for rw; Balanced.mk_apply simplifies LHS
theorem leftReturn_mk (p : P) (q : Q) (m : M) :
    letI := leftModule k R S Q M
    leftReturn k R S P Q M u hu
        (mk k S P (TensorProduct.Balanced k R Q M) p (mk k R Q M q m)) =
      u (mk k S P Q p q) • m :=
  leftReturnRaw_mk k R S P Q M u p q m

/-- Let k be a commutative ring and R, S k-algebras which are rings.
Let P be an R–S bimodule, Q an S–R bimodule, and M a left R-module,
all with compatible k-actions; the two actions on each bimodule commute.
Suppose u : P ⊗_S Q ≅ R is a right R-linear equivalence.
If u is also left R-equivariant, the inverse R-linear return sends
m to assoc([u⁻¹(1) ⊗ m]). It is the same inverse as that of
the ground-linear return. -/
theorem leftReturn_symm (m : M) :
    letI := rightModule k S R P Q
    (leftReturn k R S P Q M u hu).symm m =
      assoc k S R P Q M
        (mk k R (TensorProduct.Balanced k S P Q) M (u.symm 1) m) :=
  leftReturnRaw_symm k R S P Q M u m

end TensorProduct.Balanced.Morita
