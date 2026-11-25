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

public import MathlibExt.LinearAlgebra.TensorProduct.Balanced.MoritaLeft
public import MathlibExt.LinearAlgebra.TensorProduct.Balanced.Contraction

/-!
# Normalization of Morita contraction maps

The ratio of two invertible bimodule contractions defines an automorphism.
It constructs the normalized equations on the balanced quotient objects.
-/

@[expose] public section

noncomputable section

open MulOpposite
open scoped TensorProduct

universe r s p q c

namespace TensorProduct.Balanced.Morita

variable (R : Type r) (S : Type s) [Ring R] [Ring S]
  (P : Type p) (Q : Type q) [AddCommGroup P] [AddCommGroup Q]
  [Module R P] [Module Sᵐᵒᵖ P] [SMulCommClass R Sᵐᵒᵖ P]
  [Module S Q] [Module Rᵐᵒᵖ Q] [SMulCommClass S Rᵐᵒᵖ Q]

/-- The original right-parenthesized P–Q–P tensor. -/
abbrev normalizationSource := assocTarget ℤ S R P Q P

/-- The original R action on the first P earns the source's left module. -/
abbrev normalizationLeftModule : Module R (normalizationSource R S P Q) :=
  leftReturnModule ℤ R S P Q P

/-- The original right S action on the last P earns the source's right module. -/
abbrev normalizationRightModule : Module Sᵐᵒᵖ (normalizationSource R S P Q) := by
  letI := leftModule ℤ R S Q P
  letI := rightModule ℤ R S Q P
  letI := leftSMulCommClass ℤ R S Q P
  letI := rightSMulCommClass ℤ R S Q P
  letI := leftRightSMulCommClass ℤ R S Q P S
  exact rightModule ℤ S S P (TensorProduct.Balanced ℤ R Q P)

/-- Its original ordered pure class. -/
def normalizationMk (p : P) (q : Q) (p' : P) : normalizationSource R S P Q := by
  letI := leftModule ℤ R S Q P
  exact mk ℤ S P (TensorProduct.Balanced ℤ R Q P) p (mk ℤ R Q P q p')

/-- The actual right action on the triple is the original action on its last P. -/
theorem normalizationRightModule_mk (t : Sᵐᵒᵖ) (p : P) (q : Q) (p' : P) :
    (normalizationRightModule R S P Q).smul t (normalizationMk R S P Q p q p') =
      normalizationMk R S P Q p q (t • p') := by
  let := leftModule ℤ R S Q P
  let := rightModule ℤ R S Q P
  let := leftSMulCommClass ℤ R S Q P
  let := rightSMulCommClass ℤ R S Q P
  let := leftRightSMulCommClass ℤ R S Q P S
  let C := TensorProduct.Balanced ℤ R Q P
  change rightAction ℤ S S P C t (mk ℤ S P C p (mk ℤ R Q P q p')) = _
  rw [rightAction_mk]
  change mk ℤ S P C p (rightAction ℤ R S Q P t (mk ℤ R Q P q p')) = _
  rw [rightAction_mk]
  rfl

omit [SMulCommClass R Sᵐᵒᵖ P] in
/-- Original ordered pure classes determine an additive map on this actual tensor. -/
theorem normalizationHom_ext {C : Type c} [AddCommMonoid C]
    {f g : normalizationSource R S P Q →+ C}
    (h : ∀ (p : P) (q : Q) (p' : P),
      f (normalizationMk R S P Q p q p') = g (normalizationMk R S P Q p q p')) :
    f = g := by
  let := leftModule ℤ R S Q P
  let B := TensorProduct.Balanced ℤ R Q P
  apply addHom_ext ℤ S P B
  intro p b
  have hb : f.comp ((mk ℤ S P B p).toAddMonoidHom) =
      g.comp ((mk ℤ S P B p).toAddMonoidHom) := by
    apply addHom_ext ℤ R Q P
    intro q p'
    exact h p q p'
  exact DFunLike.congr_fun hb b

variable
  (u : letI := leftModule ℤ S R P Q
    letI := rightModule ℤ S R P Q
    TensorProduct.Balanced ℤ S P Q ≃ₗ[Rᵐᵒᵖ] R)
  (hu : letI := leftModule ℤ S R P Q
    letI := rightModule ℤ S R P Q
    ∀ (r : R) (b : TensorProduct.Balanced ℤ S P Q), u (r • b) = r * u b)

include u in
/-- The first actual contraction: associate left, apply u, then the left unitor. -/
def sourceToPLeft : normalizationSource R S P Q ≃ₗ[ℤ] P :=
  leftReturnRaw ℤ R S P Q P u

@[simp]
theorem sourceToPLeft_mk (p : P) (q : Q) (p' : P) :
    sourceToPLeft R S P Q u (normalizationMk R S P Q p q p') =
      u (mk ℤ S P Q p q) • p' :=
  leftReturnRaw_mk ℤ R S P Q P u p q p'

include hu in
/-- The first original contraction is R-linear for the computed source module. -/
theorem sourceToPLeft_smul (r : R) (x : normalizationSource R S P Q) :
    letI := normalizationLeftModule R S P Q
    sourceToPLeft R S P Q u (r • x) = r • sourceToPLeft R S P Q u x :=
  (leftReturn ℤ R S P Q P u hu).map_smul r x

/-- The original u contraction also preserves the actual last-factor right action. -/
theorem sourceToPLeft_right (t : Sᵐᵒᵖ) (x : normalizationSource R S P Q) :
    sourceToPLeft R S P Q u ((normalizationRightModule R S P Q).smul t x) =
      t • sourceToPLeft R S P Q u x := by
  let := normalizationRightModule R S P Q
  have h : (sourceToPLeft R S P Q u).toLinearMap.toAddMonoidHom.comp
      (DistribSMul.toAddMonoidHom (normalizationSource R S P Q) t) =
      (DistribSMul.toAddMonoidHom P t).comp
        (sourceToPLeft R S P Q u).toLinearMap.toAddMonoidHom := by
    apply normalizationHom_ext R S P Q
    intro p q p'
    change sourceToPLeft R S P Q u
        ((normalizationRightModule R S P Q).smul t (normalizationMk R S P Q p q p')) =
      t • sourceToPLeft R S P Q u (normalizationMk R S P Q p q p')
    rw [normalizationRightModule_mk, sourceToPLeft_mk, sourceToPLeft_mk]
    exact smul_comm (u (mk ℤ S P Q p q)) t p'
  exact DFunLike.congr_fun h x

variable
  (w : letI := leftModule ℤ R S Q P
    letI := rightModule ℤ R S Q P
    TensorProduct.Balanced ℤ R Q P ≃ₗ[Sᵐᵒᵖ] S)
  (hw : letI := leftModule ℤ R S Q P
    letI := rightModule ℤ R S Q P
    ∀ (s : S) (b : TensorProduct.Balanced ℤ R Q P), w (s • b) = s * w b)

include w hw in
/-- The second actual contraction: apply w inside, then the original right unitor. -/
def sourceToPRight : normalizationSource R S P Q ≃ₗ[ℤ] P := by
  let B := TensorProduct.Balanced ℤ R Q P
  let dB : Module ℤ B := inferInstance
  letI : Module ℤ B := dB
  letI := leftModule ℤ R S Q P
  letI := rightModule ℤ R S Q P
  let e : B ≃ₗ[ℤ] S := w.toAddEquiv.toIntLinearEquiv (modM := dB)
  exact rightContraction S P B e (fun s b => hw s b)

@[simp]
theorem sourceToPRight_mk (p : P) (q : Q) (p' : P) :
    sourceToPRight R S P Q w hw (normalizationMk R S P Q p q p') =
      op (w (mk ℤ R Q P q p')) • p := by
  let B := TensorProduct.Balanced ℤ R Q P
  let dB : Module ℤ B := inferInstance
  let : Module ℤ B := dB
  let := leftModule ℤ R S Q P
  let := rightModule ℤ R S Q P
  let e : B ≃ₗ[ℤ] S := w.toAddEquiv.toIntLinearEquiv (modM := dB)
  have he : ∀ (s : S) (b : B), e (s • b) = s * e b := by
    intro s b
    change w (s • b) = s * w b
    exact hw s b
  change rightContraction S P B e he (mk ℤ S P B p (mk ℤ R Q P q p')) =
    op (w (mk ℤ R Q P q p')) • p
  exact rightContraction_mk S P B e he p (mk ℤ R Q P q p')

/-- The second original contraction is also R-linear, by the original outer commutation. -/
theorem sourceToPRight_smul (r : R) (x : normalizationSource R S P Q) :
    letI := normalizationLeftModule R S P Q
    sourceToPRight R S P Q w hw (r • x) = r • sourceToPRight R S P Q w hw x := by
  let := normalizationLeftModule R S P Q
  let B := TensorProduct.Balanced ℤ R Q P
  let dB : Module ℤ B := inferInstance
  let : Module ℤ B := dB
  let := leftModule ℤ R S Q P
  let := rightModule ℤ R S Q P
  let e : B ≃ₗ[ℤ] S := w.toAddEquiv.toIntLinearEquiv (modM := dB)
  exact rightContraction_left_smul S P B e (fun s b => hw s b) R r x

/-- The original w contraction preserves the same last-factor S action. -/
theorem sourceToPRight_right (t : Sᵐᵒᵖ) (x : normalizationSource R S P Q) :
    sourceToPRight R S P Q w hw ((normalizationRightModule R S P Q).smul t x) =
      t • sourceToPRight R S P Q w hw x := by
  let := normalizationRightModule R S P Q
  let := leftModule ℤ R S Q P
  let := rightModule ℤ R S Q P
  have h : (sourceToPRight R S P Q w hw).toLinearMap.toAddMonoidHom.comp
      (DistribSMul.toAddMonoidHom (normalizationSource R S P Q) t) =
      (DistribSMul.toAddMonoidHom P t).comp
        (sourceToPRight R S P Q w hw).toLinearMap.toAddMonoidHom := by
    apply normalizationHom_ext R S P Q
    intro p q p'
    change sourceToPRight R S P Q w hw
        ((normalizationRightModule R S P Q).smul t (normalizationMk R S P Q p q p')) =
      t • sourceToPRight R S P Q w hw (normalizationMk R S P Q p q p')
    rw [normalizationRightModule_mk, sourceToPRight_mk, sourceToPRight_mk]
    have hwt : w (mk ℤ R Q P q (t • p')) = w (mk ℤ R Q P q p') * t.unop := by
      rw [← rightModule_smul_mk ℤ R S Q P]
      exact w.map_smul t (mk ℤ R Q P q p')
    rw [hwt, op_mul, op_unop, mul_smul]
  exact DFunLike.congr_fun h x

include u w hw in
/-- The actual ratio of the two invertible maps; normalization is not an input. -/
def contractionDifference : P ≃ₗ[ℤ] P :=
  (sourceToPLeft R S P Q u).symm.trans (sourceToPRight R S P Q w hw)

/-- This actual automorphism is precisely the difference between the two contractions. -/
theorem contractionDifference_apply_left (x : normalizationSource R S P Q) :
    contractionDifference R S P Q u w hw (sourceToPLeft R S P Q u x) =
      sourceToPRight R S P Q w hw x := by
  rw [contractionDifference, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]

include u hu w hw in
/-- The same actual difference automorphism is R-linear. -/
def contractionDifferenceLeft : P ≃ₗ[R] P := by
  letI := normalizationLeftModule R S P Q
  let A := leftReturn ℤ R S P Q P u hu
  let B := (sourceToPRight R S P Q w hw).toAddEquiv.toLinearEquiv
    (fun r x => sourceToPRight_smul R S P Q w hw r x)
  exact A.symm.trans B

@[simp]
theorem contractionDifferenceLeft_apply (p : P) :
    contractionDifferenceLeft R S P Q u hu w hw p =
      contractionDifference R S P Q u w hw p := rfl

/-- The actual difference automorphism preserves the original S action as well. -/
theorem contractionDifference_right (t : Sᵐᵒᵖ) (p : P) :
    contractionDifference R S P Q u w hw (t • p) =
      t • contractionDifference R S P Q u w hw p := by
  let A := sourceToPLeft R S P Q u
  let x := A.symm p
  have hA : A ((normalizationRightModule R S P Q).smul t x) = t • p := by
    rw [sourceToPLeft_right, LinearEquiv.apply_symm_apply]
  have hInv : A.symm (t • p) = (normalizationRightModule R S P Q).smul t x := by
    apply A.injective
    exact (A.apply_symm_apply (t • p)).trans hA.symm
  change sourceToPRight R S P Q w hw (A.symm (t • p)) =
    t • sourceToPRight R S P Q w hw x
  rw [hInv, sourceToPRight_right]

include u w hw in
/-- Apply the actual difference automorphism to the first factor of P⊗_S Q. -/
def differenceTensor : TensorProduct.Balanced ℤ S P Q ≃ₗ[ℤ]
    TensorProduct.Balanced ℤ S P Q :=
  congr (contractionDifference R S P Q u w hw) (LinearEquiv.refl ℤ Q)
    (fun s p => contractionDifference_right R S P Q u w hw (op s) p)
    (fun _ _ => rfl)

@[simp, nolint simpNF] -- stated with Balanced.mk for rw; Balanced.mk_apply simplifies LHS
theorem differenceTensor_mk (p : P) (q : Q) :
    differenceTensor R S P Q u w hw (mk ℤ S P Q p q) =
      mk ℤ S P Q (contractionDifference R S P Q u w hw p) q := by
  let E := contractionDifference R S P Q u w hw
  have hf : ∀ (s : S) (p : P), E (op s • p) = op s • E p := by
    intro s p
    exact contractionDifference_right R S P Q u w hw (op s) p
  have hg : ∀ (s : S) (q : Q), (LinearEquiv.refl ℤ Q) (s • q) =
      s • (LinearEquiv.refl ℤ Q) q := fun _ _ => rfl
  change (congr (k := ℤ) (R := S) (M := P) (N := Q) (M' := P) (N' := Q)
    E (LinearEquiv.refl ℤ Q) hf hg) (mk ℤ S P Q p q) = mk ℤ S P Q (E p) q
  exact congr_mk (k := ℤ) (R := S) (M := P) (N := Q) (M' := P) (N' := Q)
    E (LinearEquiv.refl ℤ Q) hf hg p q

/-- The actual tensor difference keeps the original right R action on Q. -/
theorem differenceTensor_right (t : Rᵐᵒᵖ) (x : TensorProduct.Balanced ℤ S P Q) :
    letI := rightModule ℤ S R P Q
    differenceTensor R S P Q u w hw (t • x) = t • differenceTensor R S P Q u w hw x := by
  let := rightModule ℤ S R P Q
  let E := differenceTensor R S P Q u w hw
  have h : E.toLinearMap.toAddMonoidHom.comp
      (DistribSMul.toAddMonoidHom (TensorProduct.Balanced ℤ S P Q) t) =
      (DistribSMul.toAddMonoidHom (TensorProduct.Balanced ℤ S P Q) t).comp
        E.toLinearMap.toAddMonoidHom := by
    apply addHom_ext ℤ S P Q
    intro p q
    change E (rightAction ℤ S R P Q t (mk ℤ S P Q p q)) =
      rightAction ℤ S R P Q t (E (mk ℤ S P Q p q))
    simp only [E, rightAction_mk, differenceTensor_mk]
  exact DFunLike.congr_fun h x

include hu in
/-- It preserves the original left R action through the earned R-linearity of the difference. -/
theorem differenceTensor_left (r : R) (x : TensorProduct.Balanced ℤ S P Q) :
    letI := leftModule ℤ S R P Q
    differenceTensor R S P Q u w hw (r • x) = r • differenceTensor R S P Q u w hw x := by
  let := leftModule ℤ S R P Q
  let E := differenceTensor R S P Q u w hw
  have h : E.toLinearMap.toAddMonoidHom.comp
      (DistribSMul.toAddMonoidHom (TensorProduct.Balanced ℤ S P Q) r) =
      (DistribSMul.toAddMonoidHom (TensorProduct.Balanced ℤ S P Q) r).comp
        E.toLinearMap.toAddMonoidHom := by
    apply addHom_ext ℤ S P Q
    intro p q
    change E (leftAction ℤ S R P Q r (mk ℤ S P Q p q)) =
      leftAction ℤ S R P Q r (E (mk ℤ S P Q p q))
    simp only [E, leftAction_mk, differenceTensor_mk]
    have hr := (contractionDifferenceLeft R S P Q u hu w hw).map_smul r p
    simpa only [contractionDifferenceLeft_apply] using congrArg (fun p : P => mk ℤ S P Q p q) hr
  exact DFunLike.congr_fun h x

include u w hw in
/-- The same actual tensor difference with its earned right R linearity. -/
def differenceTensorRight :
    letI := rightModule ℤ S R P Q
    TensorProduct.Balanced ℤ S P Q ≃ₗ[Rᵐᵒᵖ] TensorProduct.Balanced ℤ S P Q := by
  letI := rightModule ℤ S R P Q
  exact (differenceTensor R S P Q u w hw).toAddEquiv.toLinearEquiv
    (fun t x => differenceTensor_right R S P Q u w hw t x)

include u w hw in
/-- Transport the actual tensor difference through the given u, on R itself. -/
def ringDifference : R ≃ₗ[Rᵐᵒᵖ] R :=
  u.symm.trans ((differenceTensorRight R S P Q u w hw).trans u)

include hu in
/-- The transported automorphism retains the actual left R action as well. -/
theorem ringDifference_left (r x : R) :
    ringDifference R S P Q u w hw (r * x) = r * ringDifference R S P Q u w hw x := by
  let := leftModule ℤ S R P Q
  let := rightModule ℤ S R P Q
  have hi : u.symm (r * x) = r • u.symm x := by
    apply u.injective
    rw [LinearEquiv.apply_symm_apply, hu, LinearEquiv.apply_symm_apply]
  change u (differenceTensor R S P Q u w hw (u.symm (r * x))) =
    r * u (differenceTensor R S P Q u w hw (u.symm x))
  rw [hi, differenceTensor_left R S P Q u hu w hw, hu]

/-- Right R linearity gives left multiplication by the automorphism’s value at 1. -/
theorem ringDifference_apply (x : R) :
    ringDifference R S P Q u w hw x = ringDifference R S P Q u w hw 1 * x := by
  have h := (ringDifference R S P Q u w hw).map_smul (op x) (1 : R)
  change ringDifference R S P Q u w hw (1 * x) =
    ringDifference R S P Q u w hw 1 * x at h
  simpa only [one_mul] using h

include hu in
/-- The actual automorphism's scalar is central, by its two genuine module laws. -/
theorem ringDifference_commutes (r : R) :
    ringDifference R S P Q u w hw 1 * r = r * ringDifference R S P Q u w hw 1 := by
  have h := ringDifference_left R S P Q u hu w hw r 1
  rw [mul_one, ringDifference_apply] at h
  exact h

/-- The central scalar is an actual unit, with the inverse obtained from the actual inverse map. -/
def normalizationUnit : Rˣ where
  val := ringDifference R S P Q u w hw 1
  inv := (ringDifference R S P Q u w hw).symm 1
  val_inv := by
    rw [← ringDifference_apply]
    exact (ringDifference R S P Q u w hw).apply_symm_apply 1
  inv_val := by
    have h := (ringDifference R S P Q u w hw).symm.map_smul
      (op (ringDifference R S P Q u w hw 1)) (1 : R)
    change (ringDifference R S P Q u w hw).symm
        (1 * ringDifference R S P Q u w hw 1) =
      (ringDifference R S P Q u w hw).symm 1 * ringDifference R S P Q u w hw 1 at h
    rw [one_mul] at h
    exact h.symm.trans ((ringDifference R S P Q u w hw).symm_apply_apply 1)

include hu in
/-- The constructed unit is central, without a supplied normalization equation. -/
theorem normalizationUnit_commutes (r : R) :
    (normalizationUnit R S P Q u w hw : R) * r = r * (normalizationUnit R S P Q u w hw : R) :=
  ringDifference_commutes R S P Q u hu w hw r

/-- The actual transported map on R retains the first-factor tensor value. -/
theorem ringDifference_u_mk (p : P) (q : Q) :
    ringDifference R S P Q u w hw (u (mk ℤ S P Q p q)) =
      u (mk ℤ S P Q (contractionDifference R S P Q u w hw p) q) := by
  change u (differenceTensor R S P Q u w hw
    (u.symm (u (mk ℤ S P Q p q)))) = _
  rw [LinearEquiv.symm_apply_apply, differenceTensor_mk]

include w hw in
/-- The given invertible Q–P contraction makes tensoring P-maps with Q faithful. -/
theorem tensor_detects_right_maps (f g : P →ₗ[Sᵐᵒᵖ] P)
    (h : ∀ (p : P) (q : Q), mk ℤ S P Q (f p) q = mk ℤ S P Q (g p) q) : f = g := by
  let B := sourceToPRight R S P Q w hw
  have hf : f.toAddMonoidHom.comp B.toLinearMap.toAddMonoidHom =
      g.toAddMonoidHom.comp B.toLinearMap.toAddMonoidHom := by
    apply normalizationHom_ext R S P Q
    intro p q p'
    have ht : normalizationMk R S P Q (f p) q p' =
        normalizationMk R S P Q (g p) q p' := by
      let := rightModule ℤ S R P Q
      have hh := congrArg (fun x : TensorProduct.Balanced ℤ S P Q =>
        assoc ℤ S R P Q P (mk ℤ R (TensorProduct.Balanced ℤ S P Q) P x p')) (h p q)
      simpa only [assoc_mk_mk, normalizationMk] using hh
    change f (B (normalizationMk R S P Q p q p')) =
      g (B (normalizationMk R S P Q p q p'))
    rw [sourceToPRight_mk, f.map_smul, g.map_smul]
    have hb := congrArg B ht
    exact (sourceToPRight_mk R S P Q w hw (f p) q p').symm.trans
      (hb.trans (sourceToPRight_mk R S P Q w hw (g p) q p'))
  apply LinearMap.ext
  intro p
  have hh := DFunLike.congr_fun hf (B.symm p)
  change f (B (B.symm p)) = g (B (B.symm p)) at hh
  rw [LinearEquiv.apply_symm_apply] at hh
  exact hh

include u w hw in
/-- The same actual difference with its earned right S linearity. -/
def contractionDifferenceRight : P ≃ₗ[Sᵐᵒᵖ] P :=
  (contractionDifference R S P Q u w hw).toAddEquiv.toLinearEquiv
    (fun t p => contractionDifference_right R S P Q u w hw t p)

include hu in
/-- The computed difference is multiplication by the actual central unit. -/
theorem contractionDifference_eq_smul (p : P) :
    contractionDifference R S P Q u w hw p = (normalizationUnit R S P Q u w hw : R) • p := by
  let f := (contractionDifferenceRight R S P Q u w hw).toLinearMap
  let g : P →ₗ[Sᵐᵒᵖ] P := Module.toModuleEnd Sᵐᵒᵖ P (normalizationUnit R S P Q u w hw : R)
  have h : f = g := by
    apply tensor_detects_right_maps R S P Q w hw
    intro p q
    let := leftModule ℤ S R P Q
    let := rightModule ℤ S R P Q
    apply u.injective
    change u (mk ℤ S P Q (contractionDifference R S P Q u w hw p) q) =
      u (mk ℤ S P Q ((normalizationUnit R S P Q u w hw : R) • p) q)
    rw [← ringDifference_u_mk, ringDifference_apply,
      ← leftModule_smul_mk ℤ S R P Q, hu]
    rfl
  exact LinearMap.congr_fun h p

include u w hw in
/-- Adjust the actual u by its constructed central unit, with the actual inverse retained. -/
def normalizedContraction :
    letI := leftModule ℤ S R P Q
    letI := rightModule ℤ S R P Q
    TensorProduct.Balanced ℤ S P Q ≃ₗ[Rᵐᵒᵖ] R := by
  letI := leftModule ℤ S R P Q
  letI := rightModule ℤ S R P Q
  let c := normalizationUnit R S P Q u w hw
  exact u.trans (DistribMulAction.toLinearEquiv Rᵐᵒᵖ R c)

@[simp]
theorem normalizedContraction_apply (x : TensorProduct.Balanced ℤ S P Q) :
    normalizedContraction R S P Q u w hw x =
      (normalizationUnit R S P Q u w hw : R) * u x := rfl

include hu in
/-- The adjusted contraction remains a genuine R-bimodule isomorphism. -/
theorem normalizedContraction_left (r : R) (x : TensorProduct.Balanced ℤ S P Q) :
    letI := leftModule ℤ S R P Q
    letI := rightModule ℤ S R P Q
    normalizedContraction R S P Q u w hw (r • x) =
      r * normalizedContraction R S P Q u w hw x := by
  let := leftModule ℤ S R P Q
  let := rightModule ℤ S R P Q
  rw [normalizedContraction_apply, normalizedContraction_apply, hu,
    ← mul_assoc, normalizationUnit_commutes R S P Q u hu w hw r, mul_assoc]

include hu in
/-- The normalized p equation follows from the actual difference of the two contractions. -/
theorem normalized_p (p : P) (q : Q) (p' : P) :
    op (w (mk ℤ R Q P q p')) • p =
      normalizedContraction R S P Q u w hw (mk ℤ S P Q p q) • p' := by
  have h := contractionDifference_apply_left R S P Q u w hw (normalizationMk R S P Q p q p')
  rw [sourceToPLeft_mk, sourceToPRight_mk,
    contractionDifference_eq_smul R S P Q u hu w hw, ← mul_smul] at h
  rw [normalizedContraction_apply]
  exact h.symm

include w in
/-- The actual inverse contraction also detects maps after tensoring on the left by P. -/
theorem tensor_detects_left_maps (f g : Q →ₗ[S] Q)
    (h : ∀ (p : P) (q : Q), mk ℤ S P Q p (f q) = mk ℤ S P Q p (g q)) : f = g := by
  let A := sourceToPLeft S R Q P w
  have hf : f.toAddMonoidHom.comp A.toLinearMap.toAddMonoidHom =
      g.toAddMonoidHom.comp A.toLinearMap.toAddMonoidHom := by
    apply normalizationHom_ext S R Q P
    intro q p q'
    have ht : normalizationMk S R Q P q p (f q') =
        normalizationMk S R Q P q p (g q') := by
      let := leftModule ℤ S R P Q
      exact congrArg (mk ℤ R Q (TensorProduct.Balanced ℤ S P Q) q) (h p q')
    change f (A (normalizationMk S R Q P q p q')) = g (A (normalizationMk S R Q P q p q'))
    rw [sourceToPLeft_mk, f.map_smul, g.map_smul]
    exact congrArg A ht
  apply LinearMap.ext
  intro q
  have hh := DFunLike.congr_fun hf (A.symm q)
  change f (A (A.symm q)) = g (A (A.symm q)) at hh
  rw [LinearEquiv.apply_symm_apply] at hh
  exact hh

include hu in
/-- The second normalized equation is earned by the actual faithful tensor operation. -/
theorem normalized_q (p : P) (q q' : Q) :
    op (normalizedContraction R S P Q u w hw (mk ℤ S P Q p q')) • q =
      w (mk ℤ R Q P q p) • q' := by
  let := leftModule ℤ S R P Q
  let := rightModule ℤ S R P Q
  let := leftModule ℤ R S Q P
  let := rightModule ℤ R S Q P
  let : SMulCommClass Rᵐᵒᵖ S Q := SMulCommClass.symm _ _ _
  let U := normalizedContraction R S P Q u w hw
  let f : Q →ₗ[S] Q := Module.toModuleEnd S Q (op (U (mk ℤ S P Q p q')))
  let g : Q →ₗ[S] Q :=
    { toFun := fun q => w (mk ℤ R Q P q p) • q'
      map_add' := by
        intro q₁ q₂
        rw [map_add, LinearMap.add_apply, map_add, add_smul]
      map_smul' := by
        intro s q
        have hs : w (mk ℤ R Q P (s • q) p) = s * w (mk ℤ R Q P q p) := by
          rw [← leftModule_smul_mk ℤ R S Q P]
          exact hw s (mk ℤ R Q P q p)
        rw [hs, mul_smul, RingHom.id_apply] }
  have h : f = g := by
    apply tensor_detects_left_maps R S P Q w
    intro p₀ q₀
    apply U.injective
    change U (mk ℤ S P Q p₀ (op (U (mk ℤ S P Q p q')) • q₀)) =
      U (mk ℤ S P Q p₀ (w (mk ℤ R Q P q₀ p) • q'))
    have hL : U (mk ℤ S P Q p₀ (op (U (mk ℤ S P Q p q')) • q₀)) =
        U (mk ℤ S P Q p₀ q₀) * U (mk ℤ S P Q p q') := by
      have hh := U.map_smul (op (U (mk ℤ S P Q p q'))) (mk ℤ S P Q p₀ q₀)
      rw [rightModule_smul_mk] at hh
      exact hh
    have hR : U (mk ℤ S P Q p₀ (w (mk ℤ R Q P q₀ p) • q')) =
        U (mk ℤ S P Q p₀ q₀) * U (mk ℤ S P Q p q') := by
      calc
        _ = U (mk ℤ S P Q (op (w (mk ℤ R Q P q₀ p)) • p₀) q') :=
          congrArg U (balance ℤ S P Q (w (mk ℤ R Q P q₀ p)) p₀ q').symm
        _ = U (mk ℤ S P Q (U (mk ℤ S P Q p₀ q₀) • p) q') :=
          congrArg (fun p : P => U (mk ℤ S P Q p q'))
            (normalized_p R S P Q u hu w hw p₀ q₀ p)
        _ = U ((U (mk ℤ S P Q p₀ q₀)) • mk ℤ S P Q p q') :=
          congrArg U (leftModule_smul_mk ℤ S R P Q (U (mk ℤ S P Q p₀ q₀)) p q').symm
        _ = _ := normalizedContraction_left R S P Q u hu w hw _ _
    exact hL.trans hR.symm
  exact LinearMap.congr_fun h q

end TensorProduct.Balanced.Morita
