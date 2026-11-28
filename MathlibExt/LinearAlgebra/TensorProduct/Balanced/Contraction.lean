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

public import MathlibExt.Algebra.Module.NatInt
public import MathlibExt.LinearAlgebra.TensorProduct.Balanced.Unitors
public import MathlibExt.LinearAlgebra.TensorProduct.Balanced.Actions

/-!
# Contraction of a balanced tensor factor

Let R be a ring, with no commutativity assumption. If C is a right R-module
and B a left R-module equipped with an additive equivalence e : B ≅ R
satisfying e(r b) = r e(b), then contraction gives
C ⊗_R B ≅ C, [c ⊗ b] ↦ c e(b).
Its inverse sends c to [c ⊗ e⁻¹(1)]. Dually, a right R-module B with
e(b r) = e(b) r gives B ⊗_R C ≅ C for a left R-module C.

The integer-ground versions respect any supplied integer-module structures.
For a commutative ground ring k and a k-algebra R, compatible k-actions and
a k-linear e give k-linear contractions. A left outer action on C commuting
with its right R-action is preserved by right-factor contraction; over k,
that outer action must also commute with k. Scalar and module universes
remain independent.
-/

@[expose] public section

noncomputable section

open MulOpposite

universe r b c s

namespace TensorProduct.Balanced

variable (R : Type r) [Ring R]

section Right

variable (C : Type c) (B : Type b) [AddCommGroup C] [AddCommGroup B]
  [dC : Module ℤ C] [dB : Module ℤ B] [dCR : Module Rᵐᵒᵖ C] [Module R B]
  (e : B ≃ₗ[ℤ] R) (he : ∀ (r : R) (b : B), e (r • b) = r * e b)

include e he in
/-- Let R be a ring, C a right R-module and B a left R-module, with
additive commutative group structures and supplied integer-module structures.
Suppose e : B ≃ₗ[ℤ] R satisfies e(r b) = r e(b).
This integer-linear contraction C ⊗_R B ≅ C sends [c ⊗ b] to c e(b)
and has inverse c ↦ [c ⊗ e⁻¹(1)]. -/
def rightContraction : TensorProduct.Balanced ℤ R C B ≃ₗ[ℤ] C := by
  letI dR : Module ℤ R := (Algebra.toModule : Module ℤ R)
  let eR := e.toAddEquiv.toIntLinearEquiv (modM := dB) (modM₂ := dR)
  have heR : ∀ (r : R) (b : B), eR (r • b) = r • eR b := by
    intro r b
    change e (r • b) = r * e b
    exact he r b
  let tC := Module.intModule_isScalarTower (dRM := dCR)
    (Algebra.toModule : Module ℤ Rᵐᵒᵖ) dC
  let E := (congr (LinearEquiv.refl ℤ C) eR (fun _ _ => rfl) heR).trans
    (@rightUnitor ℤ R _ _ _ C _ dC dCR tC)
  let A : TensorProduct.Balanced ℤ R C B ≃+ C := by
    letI : @SMulCommClass ℤ ℤ C dC.toSMul dC.toSMul :=
      Module.intModule_smulCommClass (dS := dC.toDistribMulAction.toDistribSMul) (dM := dC)
    letI : Module ℤ (TensorProduct ℤ C B) := TensorProduct.leftModule
    exact @LinearEquiv.toAddEquiv ℤ ℤ _ _ (RingHom.id ℤ) (RingHom.id ℤ) _ _
      (TensorProduct.Balanced ℤ R C B) C _ _
      (Submodule.Quotient.module (balanceRelations ℤ R C B)) dC E
  exact A.toIntLinearEquiv
    (modM := AddCommGroup.toIntModule (TensorProduct.Balanced ℤ R C B)) (modM₂ := dC)

@[simp, nolint simpNF] -- stated with Balanced.mk for rw; Balanced.mk_apply simplifies LHS
theorem rightContraction_mk (c : C) (b : B) :
    rightContraction R C B e he (mk ℤ R C B c b) = op (e b) • c := by
  let dR : Module ℤ R := (Algebra.toModule : Module ℤ R)
  let eR := e.toAddEquiv.toIntLinearEquiv (modM := dB) (modM₂ := dR)
  have heR : ∀ (r : R) (b : B), eR (r • b) = r • eR b := by
    intro r b
    change e (r • b) = r * e b
    exact he r b
  let tC := Module.intModule_isScalarTower (dRM := dCR)
    (Algebra.toModule : Module ℤ Rᵐᵒᵖ) dC
  let U := @rightUnitor ℤ R _ _ _ C _ dC dCR tC
  let f := congr (LinearEquiv.refl ℤ C) eR (fun _ _ => rfl) heR
  have hmk : f (mk ℤ R C B c b) = mk ℤ R C R c (eR b) := by
    calc
      f (mk ℤ R C B c b) =
          mk ℤ R C R ((LinearEquiv.refl ℤ C) c) (eR b) :=
        congr_mk (LinearEquiv.refl ℤ C) eR (fun _ _ => rfl) heR c b
      _ = _ := rfl
  change U (f (mk ℤ R C B c b)) = op (e b) • c
  exact (congrArg U hmk).trans
    (@rightUnitor_mk ℤ R _ _ _ C _ dC dCR tC c (eR b))

variable (S : Type s) [Semiring S] [dSC : Module S C]
  [SMulCommClass S Rᵐᵒᵖ C]

/-- Let R be a ring, C a right R-module and B a left R-module with
supplied integer-module structures, and let e : B ≃ₗ[ℤ] R satisfy
e(r b) = r e(b). If a semiring S acts on C on the left and that action
commutes with the right R-action, the induced action on C ⊗_R B is
preserved by contraction: contraction(s • x) = s • contraction(x). -/
theorem rightContraction_left_smul (s : S) (x : TensorProduct.Balanced ℤ R C B) :
    letI : @SMulCommClass S ℤ C dSC.toSMul dC.toSMul :=
      Module.intModule_smulCommClass (dS := dSC.toDistribMulAction.toDistribSMul) (dM := dC)
    letI := leftModule ℤ R S C B
    rightContraction R C B e he (s • x) = s • rightContraction R C B e he x := by
  let : @SMulCommClass S ℤ C dSC.toSMul dC.toSMul :=
    Module.intModule_smulCommClass (dS := dSC.toDistribMulAction.toDistribSMul) (dM := dC)
  let := leftModule ℤ R S C B
  have h : (rightContraction R C B e he).toLinearMap.toAddMonoidHom.comp
      (leftAction ℤ R S C B s).toAddMonoidHom =
      (DistribSMul.toAddMonoidHom C s).comp
        (rightContraction R C B e he).toLinearMap.toAddMonoidHom := by
    apply addHom_ext ℤ R C B
    intro c b
    change rightContraction R C B e he (leftAction ℤ R S C B s (mk ℤ R C B c b)) =
      s • rightContraction R C B e he (mk ℤ R C B c b)
    rw [leftAction_mk, rightContraction_mk, rightContraction_mk]
    exact (smul_comm s (op (e b)) c).symm
  change rightContraction R C B e he (leftAction ℤ R S C B s x) =
    s • rightContraction R C B e he x
  exact DFunLike.congr_fun h x

end Right

section Left

variable (B : Type b) (C : Type c) [AddCommGroup B] [AddCommGroup C]
  [dB : Module ℤ B] [dC : Module ℤ C] [Module Rᵐᵒᵖ B] [dRC : Module R C]
  (e : B ≃ₗ[ℤ] R)
  (he : ∀ (r : R) (b : B), e (op r • b) = e b * r)

include e he in
/-- Let R be a ring, B a right R-module and C a left R-module, with
additive commutative group structures and supplied integer-module structures.
Suppose e : B ≃ₗ[ℤ] R satisfies e(b r) = e(b) r.
This integer-linear contraction B ⊗_R C ≅ C sends [b ⊗ c] to e(b) c
and has inverse c ↦ [e⁻¹(1) ⊗ c]. -/
def leftContraction : TensorProduct.Balanced ℤ R B C ≃ₗ[ℤ] C := by
  letI dR : Module ℤ R := (Algebra.toModule : Module ℤ R)
  let eR := e.toAddEquiv.toIntLinearEquiv (modM := dB) (modM₂ := dR)
  have heR : ∀ (r : R) (b : B), eR (op r • b) = op r • eR b := by
    intro r b
    change e (op r • b) = e b * r
    exact he r b
  let tC := Module.intModule_isScalarTower (dRM := dRC) dR dC
  let E := (congr eR (LinearEquiv.refl ℤ C) heR (fun _ _ => rfl)).trans
    (@leftUnitor ℤ R _ _ _ C _ dC dRC tC)
  let A : TensorProduct.Balanced ℤ R B C ≃+ C := by
    letI : @SMulCommClass ℤ ℤ B dB.toSMul dB.toSMul :=
      Module.intModule_smulCommClass (dS := dB.toDistribMulAction.toDistribSMul) (dM := dB)
    letI : Module ℤ (TensorProduct ℤ B C) := TensorProduct.leftModule
    exact @LinearEquiv.toAddEquiv ℤ ℤ _ _ (RingHom.id ℤ) (RingHom.id ℤ) _ _
      (TensorProduct.Balanced ℤ R B C) C _ _
      (Submodule.Quotient.module (balanceRelations ℤ R B C)) dC E
  exact A.toIntLinearEquiv
    (modM := AddCommGroup.toIntModule (TensorProduct.Balanced ℤ R B C)) (modM₂ := dC)

@[simp, nolint simpNF] -- stated with Balanced.mk for rw; Balanced.mk_apply simplifies LHS
theorem leftContraction_mk (b : B) (c : C) :
    leftContraction R B C e he (mk ℤ R B C b c) = e b • c := by
  let dR : Module ℤ R := (Algebra.toModule : Module ℤ R)
  let eR := e.toAddEquiv.toIntLinearEquiv (modM := dB) (modM₂ := dR)
  have heR : ∀ (r : R) (b : B), eR (op r • b) = op r • eR b := by
    intro r b
    change e (op r • b) = e b * r
    exact he r b
  let tC := Module.intModule_isScalarTower (dRM := dRC) dR dC
  let U := @leftUnitor ℤ R _ _ _ C _ dC dRC tC
  let f := congr eR (LinearEquiv.refl ℤ C) heR (fun _ _ => rfl)
  have hmk : f (mk ℤ R B C b c) = mk ℤ R R C (eR b) c := by
    calc
      f (mk ℤ R B C b c) =
          mk ℤ R R C (eR b) ((LinearEquiv.refl ℤ C) c) :=
        congr_mk eR (LinearEquiv.refl ℤ C) heR (fun _ _ => rfl) b c
      _ = _ := rfl
  change U (f (mk ℤ R B C b c)) = e b • c
  exact (congrArg U hmk).trans
    (@leftUnitor_mk ℤ R _ _ _ C _ dC dRC tC (eR b) c)

end Left

end TensorProduct.Balanced

namespace TensorProduct.Balanced.Over

universe u

variable (k : Type u) [CommRing k] (R : Type r) [Ring R] [Algebra k R]

section Right

variable (C : Type c) (B : Type b) [AddCommGroup C] [AddCommGroup B]
  [Module k C] [Module k B] [Module Rᵐᵒᵖ C] [Module R B]
  [IsScalarTower k Rᵐᵒᵖ C] [IsScalarTower k R B]
  (e : B ≃ₗ[k] R) (he : ∀ (r : R) (b : B), e (r • b) = r * e b)

include e he in
/-- Let k be a commutative ring, R a k-algebra which is a ring,
C a right R-module with compatible k-action, and B a left R-module
with a k-module structure. Given e : B ≃ₗ[k] R with e(r b) = r e(b),
this k-linear contraction C ⊗_R B ≅ C sends [c ⊗ b] to c e(b)
and has inverse c ↦ [c ⊗ e⁻¹(1)]. -/
def rightContraction : TensorProduct.Balanced k R C B ≃ₗ[k] C := by
  have h : ∀ (r : R) (b : B), e (r • b) = r • e b := by
    intro r b
    change e (r • b) = r * e b
    exact he r b
  exact (congr (LinearEquiv.refl k C) e (fun _ _ => rfl) h).trans
    (rightUnitor k R C)
omit [IsScalarTower k R B] in
-- stated with Balanced.mk for rw; Balanced.mk_apply simplifies its left-hand side
@[simp, nolint simpNF]
theorem rightContraction_mk (c : C) (b : B) :
    rightContraction k R C B e he (mk k R C B c b) = op (e b) • c := by
  have h : ∀ (r : R) (b : B), e (r • b) = r • e b := by
    intro r b
    change e (r • b) = r * e b
    exact he r b
  let f := congr (LinearEquiv.refl k C) e (fun _ _ => rfl) h
  have hf : f (mk k R C B c b) = mk k R C R c (e b) := by
    exact (congr_mk (LinearEquiv.refl k C) e (fun _ _ => rfl) h c b).trans (by rfl)
  change rightUnitor k R C (f (mk k R C B c b)) = op (e b) • c
  exact (congrArg (rightUnitor k R C) hf).trans (rightUnitor_mk k R C c (e b))

variable (S : Type s) [Semiring S] [Module S C]
  [SMulCommClass S k C] [SMulCommClass S Rᵐᵒᵖ C]
omit [IsScalarTower k R B] in

/-- Let k be a commutative ring, R a k-algebra which is a ring,
C a right R-module with compatible k-action, and B a left R-module
with a k-module structure and e : B ≃ₗ[k] R satisfying e(r b) = r e(b).
If a semiring S acts on C on the left, commuting with k and the right
R-action, right-factor contraction satisfies
contraction(s • x) = s • contraction(x) for the induced action on C ⊗_R B. -/
theorem rightContraction_left_smul (s : S) (x : TensorProduct.Balanced k R C B) :
    letI := leftModule k R S C B
    rightContraction k R C B e he (s • x) = s • rightContraction k R C B e he x := by
  let := leftModule k R S C B
  have h : (rightContraction k R C B e he).toLinearMap.toAddMonoidHom.comp
      (leftAction k R S C B s).toAddMonoidHom =
      (DistribSMul.toAddMonoidHom C s).comp
        (rightContraction k R C B e he).toLinearMap.toAddMonoidHom := by
    apply addHom_ext k R C B
    intro c b
    change rightContraction k R C B e he (leftAction k R S C B s (mk k R C B c b)) =
      s • rightContraction k R C B e he (mk k R C B c b)
    rw [leftAction_mk, rightContraction_mk, rightContraction_mk]
    exact (smul_comm s (op (e b)) c).symm
  change rightContraction k R C B e he (leftAction k R S C B s x) =
    s • rightContraction k R C B e he x
  exact DFunLike.congr_fun h x

end Right

section Left

variable (B : Type b) (C : Type c) [AddCommGroup B] [AddCommGroup C]
  [Module k B] [Module k C] [Module Rᵐᵒᵖ B] [Module R C]
  [IsScalarTower k Rᵐᵒᵖ B] [IsScalarTower k R C]
  (e : B ≃ₗ[k] R) (he : ∀ (r : R) (b : B), e (op r • b) = e b * r)

include e he in
/-- Let k be a commutative ring, R a k-algebra which is a ring,
B a right R-module with a k-module structure, and C a left R-module
with compatible k-action. Given e : B ≃ₗ[k] R with e(b r) = e(b) r,
this k-linear contraction B ⊗_R C ≅ C sends [b ⊗ c] to e(b) c
and has inverse c ↦ [e⁻¹(1) ⊗ c]. -/
def leftContraction : TensorProduct.Balanced k R B C ≃ₗ[k] C := by
  have h : ∀ (r : R) (b : B), e (op r • b) = op r • e b := by
    intro r b
    change e (op r • b) = e b * r
    exact he r b
  exact (congr e (LinearEquiv.refl k C) h (fun _ _ => rfl)).trans
    (leftUnitor k R C)
omit [IsScalarTower k Rᵐᵒᵖ B] in
-- stated with Balanced.mk for rw; Balanced.mk_apply simplifies its left-hand side
@[simp, nolint simpNF]
theorem leftContraction_mk (b : B) (c : C) :
    leftContraction k R B C e he (mk k R B C b c) = e b • c := by
  have h : ∀ (r : R) (b : B), e (op r • b) = op r • e b := by
    intro r b
    change e (op r • b) = e b * r
    exact he r b
  let f := congr e (LinearEquiv.refl k C) h (fun _ _ => rfl)
  have hf : f (mk k R B C b c) = mk k R R C (e b) c := by
    exact (congr_mk e (LinearEquiv.refl k C) h (fun _ _ => rfl) b c).trans (by rfl)
  change leftUnitor k R C (f (mk k R B C b c)) = e b • c
  exact (congrArg (leftUnitor k R C) hf).trans (leftUnitor_mk k R C (e b) c)

end Left

end TensorProduct.Balanced.Over
