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
# The actual left-module Morita return

The return from `P ⊗_S (Q ⊗_R M)` is the inverse of the existing
associator, the original contraction, and the actual left unitor. Its
outer R action and R-linearity are earned. The given ground modules and
noncommutative factor order are retained; no normalized contraction,
finite frame or tensor comparison is caller data.
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

/-- The original right parentheses, with their already constructed inner action. -/
abbrev leftReturnSource := assocTarget k S R P Q M

/-- The original R action on P earns the outer action on the return source. -/
abbrev leftReturnModule : Module R (leftReturnSource k R S P Q M) := by
  letI := leftModule k R S Q M
  exact leftModule k S R P (TensorProduct.Balanced k R Q M)

variable
  (u : letI := leftModule k S R P Q
    letI := rightModule k S R P Q
    TensorProduct.Balanced k S P Q ≃ₗ[Rᵐᵒᵖ] R)

include u in
/-- Reassociate and contract the original balanced pair, keeping the ground action. -/
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
/-- The return contracts any actual P–Q class, without a finite representation. -/
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

/-- The source order is p, q, m, and the contraction acts on the left of m. -/
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

/-- The actual inverse inserts u⁻¹(1), then uses the original associator. -/
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
/-- The same raw return is linear for its computed outer R module. -/
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

/-- R-linearity does not change the original ground return value. -/
@[simp]
theorem leftReturn_apply (x : leftReturnSource k R S P Q M) :
    leftReturn k R S P Q M u hu x = leftReturnRaw k R S P Q M u x := rfl

/-- The outer-linear return keeps the original pure contraction formula. -/
@[simp, nolint simpNF] -- stated with Balanced.mk for rw; Balanced.mk_apply simplifies LHS
theorem leftReturn_mk (p : P) (q : Q) (m : M) :
    letI := leftModule k R S Q M
    leftReturn k R S P Q M u hu
        (mk k S P (TensorProduct.Balanced k R Q M) p (mk k R Q M q m)) =
      u (mk k S P Q p q) • m :=
  leftReturnRaw_mk k R S P Q M u p q m

/-- The R-linear inverse is exactly the constructed raw inverse. -/
theorem leftReturn_symm (m : M) :
    letI := rightModule k S R P Q
    (leftReturn k R S P Q M u hu).symm m =
      assoc k S R P Q M
        (mk k R (TensorProduct.Balanced k S P Q) M (u.symm 1) m) :=
  leftReturnRaw_symm k R S P Q M u m

end TensorProduct.Balanced.Morita
