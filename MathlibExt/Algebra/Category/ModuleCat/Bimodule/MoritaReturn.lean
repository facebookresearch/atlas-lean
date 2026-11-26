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

public import MathlibExt.Algebra.Category.ModuleCat.Bimodule.Morita
public import MathlibExt.LinearAlgebra.TensorProduct.Balanced.Contraction
public import MathlibExt.Algebra.Module.NatInt

/-!
# Contracting the bimodule tensor return

Let R,S be rings in universes r,s and P:(R,S), Q:(S,R), M:(R,R) bimodules with carriers in v.
The raw return T(M)=(P⊗_S((Q⊗_R M)⊗_R P))⊗_S Q has outer R-actions on its first P and final Q.

Suppose α:P⊗_S Q≃R is right R-linear and also satisfies α(r•b)=rα(b). Associativity and the two
α-contractions identify T(M) with M. On a five-factor class the forward map is
Γ(p₀,q₀,m,p₁,q₁)↦α(p₀⊗q₀)•m•α(p₁⊗q₁).

This contraction and its inverse are linear for R⊗_ℤRᵒᵖ. The inverse is obtained by inserting
α⁻¹(1) on both sides of M in the paired-factor tensor coordinates and then reversing the
reassociation. The resulting module isomorphism preserves the given left and right R-actions and
integer scalar action.
-/

@[expose] public section

noncomputable section

open CategoryTheory MulOpposite TensorProduct.Balanced
open scoped TensorProduct

universe r s v

namespace ModuleCat.Bimodule.Morita

attribute [local instance] ModuleCat.Bimodule.int_isScalarTower
  Module.intModule_smulCommClass

variable (R : Type r) (S : Type s) [Ring R] [Ring S]
  (P Q : Type v) [AddCommGroup P] [AddCommGroup Q]
  [Module R P] [Module Sᵐᵒᵖ P] [SMulCommClass R Sᵐᵒᵖ P]
  [Module S Q] [Module Rᵐᵒᵖ Q] [SMulCommClass S Rᵐᵒᵖ Q]
  (M : Type v) [AddCommGroup M] [givenIntegerModule : Module ℤ M]
  [Module R M] [Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M]

include R S P Q M in
/-- Let R,S be rings in independent universes r,s, P an (R,S)-bimodule and Q an (S,R)-bimodule with
carriers in v. Let M be an R-bimodule with abelian carrier and integer scalar action in v. Put
T(M)=(P⊗_S((Q⊗_R M)⊗_R P))⊗_S Q, and Γ(p₀,q₀,m,p₁,q₁) for its class with those five factors in
that order. The carrier T(M) lies in v. Its middle three-factor coefficient is (Q⊗_R M)⊗_R P,
and the two outer balancing steps are over S. -/
abbrev rawReturnTensor : Type v := by
  let C := TensorProduct.Balanced.Morita.coefficientTensor ℤ R Q M P
  let dC : Module ℤ C := inferInstance
  letI : Module ℤ C := dC
  letI := TensorProduct.Balanced.Morita.coefficientLeftModule ℤ R S Q M P
  letI := TensorProduct.Balanced.Morita.coefficientRightModule ℤ R S Q M P
  letI := TensorProduct.Balanced.Morita.coefficientActionsComm ℤ R S Q M P
  letI := TensorProduct.Balanced.Morita.coefficientLeftTower ℤ R S Q M P
  letI := TensorProduct.Balanced.Morita.coefficientRightTower ℤ R S Q M P
  exact assocSource ℤ S S P C Q

include R S P Q M in
/-- Let R,S be rings in independent universes r,s, P an (R,S)-bimodule and Q an (S,R)-bimodule with
carriers in v. Let M be an R-bimodule with abelian carrier and integer scalar action in v. Put
T(M)=(P⊗_S((Q⊗_R M)⊗_R P))⊗_S Q, and Γ(p₀,q₀,m,p₁,q₁) for its class with those five factors in
that order. The outer left R-action acts on p₀ and the outer right R-action on q₁. These
commuting actions make T(M) an object of ModuleCat_v(R⊗_ℤRᵒᵖ). -/
def rawReturnObject : ModuleCat.{v} (R ⊗[ℤ] Rᵐᵒᵖ) := by
  let C := TensorProduct.Balanced.Morita.coefficientTensor ℤ R Q M P
  let dC : Module ℤ C := inferInstance
  letI : Module ℤ C := dC
  letI := TensorProduct.Balanced.Morita.coefficientLeftModule ℤ R S Q M P
  letI := TensorProduct.Balanced.Morita.coefficientRightModule ℤ R S Q M P
  letI := TensorProduct.Balanced.Morita.coefficientActionsComm ℤ R S Q M P
  letI := TensorProduct.Balanced.Morita.coefficientLeftTower ℤ R S Q M P
  letI := TensorProduct.Balanced.Morita.coefficientRightTower ℤ R S Q M P
  exact tensorObject S R Q P C

/-- Let R,S be rings in independent universes r,s, P an (R,S)-bimodule and Q an (S,R)-bimodule with
carriers in v. Let M be an R-bimodule with abelian carrier and integer scalar action in v. For
p₀∈P,c∈(Q⊗_R M)⊗_R P,q₁∈Q, the raw outer class is (p₀⊗_S c)⊗_S q₁ in T(M). It allows any inner
coefficient c, with the computed S-actions of that tensor. -/
def rawReturnOuterMk (p₀ : P)
    (c : TensorProduct.Balanced.Morita.coefficientTensor ℤ R Q M P) (q₁ : Q) :
    rawReturnTensor R S P Q M := by
  let C := TensorProduct.Balanced.Morita.coefficientTensor ℤ R Q M P
  let dC : Module ℤ C := inferInstance
  letI : Module ℤ C := dC
  letI := TensorProduct.Balanced.Morita.coefficientLeftModule ℤ R S Q M P
  letI := TensorProduct.Balanced.Morita.coefficientRightModule ℤ R S Q M P
  letI := TensorProduct.Balanced.Morita.coefficientActionsComm ℤ R S Q M P
  letI := TensorProduct.Balanced.Morita.coefficientLeftTower ℤ R S Q M P
  letI := TensorProduct.Balanced.Morita.coefficientRightTower ℤ R S Q M P
  letI := TensorProduct.Balanced.rightModule ℤ S S P C
  exact mk ℤ S (TensorProduct.Balanced ℤ S P C) Q
    (mk ℤ S P C p₀ c) q₁

/-- Let R,S be rings in independent universes r,s, P an (R,S)-bimodule and Q an (S,R)-bimodule with
carriers in v. Let M be an R-bimodule with abelian carrier and integer scalar action in v. Put
T(M)=(P⊗_S((Q⊗_R M)⊗_R P))⊗_S Q, and Γ(p₀,q₀,m,p₁,q₁) for its class with those five factors in
that order. For p₀,p₁∈P,q₀,q₁∈Q,m∈M, Γ is the class (p₀⊗_S((q₀⊗_R m)⊗_R p₁))⊗_S q₁. The
parenthesization and the two R and two S balancing relations are fixed. -/
def rawReturnMk (p₀ : P) (q₀ : Q) (m : M) (p₁ : P) (q₁ : Q) :
    rawReturnTensor R S P Q M := by
  letI := TensorProduct.Balanced.rightModule ℤ R R Q M
  exact rawReturnOuterMk R S P Q M p₀
    (mk ℤ R (TensorProduct.Balanced ℤ R Q M) P (mk ℤ R Q M q₀ m) p₁) q₁

/-- Let R,S be rings in independent universes r,s, P an (R,S)-bimodule and Q an (S,R)-bimodule with
carriers in v. Let M be an R-bimodule with abelian carrier and integer scalar action in v. Put
T(M)=(P⊗_S((Q⊗_R M)⊗_R P))⊗_S Q, and Γ(p₀,q₀,m,p₁,q₁) for its class with those five factors in
that order. For any additive commutative monoid C' in any universe, additive maps f,g:T(M)→C'
are equal whenever f(Γ(p₀,q₀,m,p₁,q₁))=g(Γ(p₀,q₀,m,p₁,q₁)) for every choice of the five
coefficients. -/
theorem rawReturnHom_ext {C' : Type*} [AddCommMonoid C']
    {f g : rawReturnTensor R S P Q M →+ C'}
    (h : ∀ (p₀ : P) (q₀ : Q) (m : M) (p₁ : P) (q₁ : Q),
      f (rawReturnMk R S P Q M p₀ q₀ m p₁ q₁) =
        g (rawReturnMk R S P Q M p₀ q₀ m p₁ q₁)) : f = g := by
  let := TensorProduct.Balanced.rightModule ℤ R R Q M
  let C := TensorProduct.Balanced.Morita.coefficientTensor ℤ R Q M P
  let dC : Module ℤ C := inferInstance
  let : Module ℤ C := dC
  let := TensorProduct.Balanced.Morita.coefficientLeftModule ℤ R S Q M P
  let := TensorProduct.Balanced.Morita.coefficientRightModule ℤ R S Q M P
  let := TensorProduct.Balanced.Morita.coefficientActionsComm ℤ R S Q M P
  let := TensorProduct.Balanced.Morita.coefficientLeftTower ℤ R S Q M P
  let := TensorProduct.Balanced.Morita.coefficientRightTower ℤ R S Q M P
  let := TensorProduct.Balanced.rightModule ℤ S S P C
  let A := TensorProduct.Balanced ℤ S P C
  apply addHom_ext ℤ S A Q
  intro a q₁
  have ha : f.comp (((mk ℤ S A Q).flip q₁).toAddMonoidHom) =
      g.comp (((mk ℤ S A Q).flip q₁).toAddMonoidHom) := by
    apply addHom_ext ℤ S P C
    intro p₀ c
    have hc : (f.comp (((mk ℤ S A Q).flip q₁).toAddMonoidHom)).comp
        ((mk ℤ S P C p₀).toAddMonoidHom) =
      (g.comp (((mk ℤ S A Q).flip q₁).toAddMonoidHom)).comp
        ((mk ℤ S P C p₀).toAddMonoidHom) := by
      apply TensorProduct.Balanced.Morita.coefficientHom_ext ℤ R Q M P
      intro q₀ m p₁
      exact h p₀ q₀ m p₁ q₁
    exact DFunLike.congr_fun hc c
  exact DFunLike.congr_fun ha a

/-- Let R,S be rings in independent universes r,s, P an (R,S)-bimodule and Q an (S,R)-bimodule with
carriers in v. Let M be an R-bimodule with abelian carrier and integer scalar action in v. Put
T(M)=(P⊗_S((Q⊗_R M)⊗_R P))⊗_S Q, and Γ(p₀,q₀,m,p₁,q₁) for its class with those five factors in
that order. For r∈R,t∈Rᵒᵖ, the scalar action satisfies
(r⊗t)•Γ(p₀,q₀,m,p₁,q₁)=Γ(r•p₀,q₀,m,p₁,t•q₁). The inner coefficient factors are retained. -/
theorem rawReturnModule_tmul_mk (r : R) (t : Rᵐᵒᵖ)
    (p₀ : P) (q₀ : Q) (m : M) (p₁ : P) (q₁ : Q) :
    (rawReturnObject R S P Q M).isModule.smul (r ⊗ₜ[ℤ] t)
        (rawReturnMk R S P Q M p₀ q₀ m p₁ q₁) =
      rawReturnMk R S P Q M (r • p₀) q₀ m p₁ (t • q₁) := by
  let := TensorProduct.Balanced.rightModule ℤ R R Q M
  let C := TensorProduct.Balanced.Morita.coefficientTensor ℤ R Q M P
  let dC : Module ℤ C := inferInstance
  let : Module ℤ C := dC
  let := TensorProduct.Balanced.Morita.coefficientLeftModule ℤ R S Q M P
  let := TensorProduct.Balanced.Morita.coefficientRightModule ℤ R S Q M P
  let := TensorProduct.Balanced.Morita.coefficientActionsComm ℤ R S Q M P
  let := TensorProduct.Balanced.Morita.coefficientLeftTower ℤ R S Q M P
  let := TensorProduct.Balanced.Morita.coefficientRightTower ℤ R S Q M P
  exact TensorProduct.Balanced.Morita.coefficientModule_tmul_mk ℤ S R P C Q r t p₀
    (mk ℤ R (TensorProduct.Balanced ℤ R Q M) P (mk ℤ R Q M q₀ m) p₁) q₁

variable
  (u : letI := TensorProduct.Balanced.leftModule ℤ S R P Q
    letI := TensorProduct.Balanced.rightModule ℤ S R P Q
    TensorProduct.Balanced ℤ S P Q ≃ₗ[Rᵐᵒᵖ] R)
  (hu : letI := TensorProduct.Balanced.leftModule ℤ S R P Q
    letI := TensorProduct.Balanced.rightModule ℤ S R P Q
    ∀ (r : R) (b : TensorProduct.Balanced ℤ S P Q), u (r • b) = r * u b)

include u hu in
/-- Let R,S be rings in independent universes r,s, P an (R,S)-bimodule and Q an (S,R)-bimodule with
carriers in v. Let M be an R-bimodule with abelian carrier and integer scalar action in v. Put
T(M)=(P⊗_S((Q⊗_R M)⊗_R P))⊗_S Q, and Γ(p₀,q₀,m,p₁,q₁) for its class with those five factors in
that order. Let α:P⊗_S Q≃R be right R-linear and satisfy α(r•b)=rα(b) for all r∈R,b∈P⊗_S Q. Thus
α preserves both R-actions. There is an integer-linear equivalence T(M)≃M obtained by
reassociation and contracting both P⊗_S Q pairs. Its value on Γ is α(p₀⊗q₀)•m•α(p₁⊗q₁). -/
def rawReturnIso : rawReturnTensor R S P Q M ≃ₗ[ℤ] M := by
  let ringInteger : Module ℤ R := (Algebra.toModule : Module ℤ R)
  letI : Module ℤ R := ringInteger
  let I := TensorProduct.Balanced ℤ R Q M
  let dI : Module ℤ I := inferInstance
  letI : Module ℤ I := dI
  letI := TensorProduct.Balanced.rightModule ℤ R R Q M
  letI := TensorProduct.Balanced.leftModule ℤ R S Q M
  letI := leftSMulCommClass ℤ R S Q M
  letI := leftRightSMulCommClass ℤ R R Q M S
  letI := rightScalarTower ℤ R R Q M
  letI := leftScalarTower ℤ R S Q M
  let A := TensorProduct.Balanced.Morita.coefficientTensor ℤ R Q M P
  let dA : Module ℤ A := inferInstance
  letI : Module ℤ A := dA
  letI := TensorProduct.Balanced.Morita.coefficientLeftModule ℤ R S Q M P
  letI := TensorProduct.Balanced.Morita.coefficientRightModule ℤ R S Q M P
  letI := TensorProduct.Balanced.Morita.coefficientActionsComm ℤ R S Q M P
  letI := TensorProduct.Balanced.Morita.coefficientLeftTower ℤ R S Q M P
  letI := TensorProduct.Balanced.Morita.coefficientRightTower ℤ R S Q M P
  let B := TensorProduct.Balanced ℤ S P Q
  let dB : Module ℤ B := inferInstance
  letI : Module ℤ B := dB
  letI := TensorProduct.Balanced.leftModule ℤ S R P Q
  letI := TensorProduct.Balanced.rightModule ℤ S R P Q
  let e : B ≃ₗ[ℤ] R := u.toAddEquiv.toIntLinearEquiv (modM := dB) (modM₂ := ringInteger)
  have eL (r : R) (b : B) : e (r • b) = r * e b := hu r b
  have eR (r : R) (b : B) : e (op r • b) = e b * r := u.map_smul (op r) b
  let D := TensorProduct.Balanced ℤ S A Q
  letI := TensorProduct.Balanced.leftModule ℤ S S A Q
  let J := TensorProduct.Balanced ℤ R I B
  letI := TensorProduct.Balanced.leftModule ℤ R S I B
  let a₀ : rawReturnTensor R S P Q M ≃ₗ[ℤ] TensorProduct.Balanced ℤ S P D :=
    assoc ℤ S S P A Q
  let a₁ : D ≃ₗ[ℤ] J := assoc ℤ R S I P Q
  have a₁S (s : S) (x : D) : a₁ (s • x) = s • a₁ x :=
    assoc_left_smul ℤ R S I P Q S s x
  let a₂ : J ≃ₗ[ℤ] I := rightContraction R I B e eL
  have a₂S (s : S) (x : J) : a₂ (s • x) = s • a₂ x :=
    rightContraction_left_smul R I B e eL S s x
  let b₁ : TensorProduct.Balanced ℤ S P D ≃ₗ[ℤ] TensorProduct.Balanced ℤ S P J :=
    congr (LinearEquiv.refl ℤ P) a₁ (fun _ _ => rfl) a₁S
  let b₂ : TensorProduct.Balanced ℤ S P J ≃ₗ[ℤ] TensorProduct.Balanced ℤ S P I :=
    congr (LinearEquiv.refl ℤ P) a₂ (fun _ _ => rfl) a₂S
  let a₃ : TensorProduct.Balanced ℤ S P I ≃ₗ[ℤ] TensorProduct.Balanced ℤ R B M :=
    (assoc ℤ S R P Q M).symm
  let a₄ : TensorProduct.Balanced ℤ R B M ≃ₗ[ℤ] M := leftContraction R B M e eR
  exact a₀.trans (b₁.trans (b₂.trans (a₃.trans a₄)))

/-- Let R,S be rings in independent universes r,s, P an (R,S)-bimodule and Q an (S,R)-bimodule with
carriers in v. Let M be an R-bimodule with abelian carrier and integer scalar action in v. Put
T(M)=(P⊗_S((Q⊗_R M)⊗_R P))⊗_S Q, and Γ(p₀,q₀,m,p₁,q₁) for its class with those five factors in
that order. Let α:P⊗_S Q≃R be right R-linear and satisfy α(r•b)=rα(b) for all r∈R,b∈P⊗_S Q. Thus
α preserves both R-actions. For every five-factor generator,
c_α(Γ(p₀,q₀,m,p₁,q₁))=α(p₀⊗q₀)•(op(α(p₁⊗q₁))•m). The first scalar acts on the left and the
second through the given Rᵒᵖ-action. -/
@[simp]
theorem rawReturnIso_mk (p₀ : P) (q₀ : Q) (m : M) (p₁ : P) (q₁ : Q) :
    rawReturnIso R S P Q M u hu (rawReturnMk R S P Q M p₀ q₀ m p₁ q₁) =
      u (mk ℤ S P Q p₀ q₀) • (op (u (mk ℤ S P Q p₁ q₁)) • m) := by
  let ringInteger : Module ℤ R := (Algebra.toModule : Module ℤ R)
  let : Module ℤ R := ringInteger
  let I := TensorProduct.Balanced ℤ R Q M
  let dI : Module ℤ I := inferInstance
  let : Module ℤ I := dI
  let := TensorProduct.Balanced.rightModule ℤ R R Q M
  let := TensorProduct.Balanced.leftModule ℤ R S Q M
  let := leftSMulCommClass ℤ R S Q M
  let := leftRightSMulCommClass ℤ R R Q M S
  let := rightScalarTower ℤ R R Q M
  let := leftScalarTower ℤ R S Q M
  let A := TensorProduct.Balanced.Morita.coefficientTensor ℤ R Q M P
  let dA : Module ℤ A := inferInstance
  let : Module ℤ A := dA
  let := TensorProduct.Balanced.Morita.coefficientLeftModule ℤ R S Q M P
  let := TensorProduct.Balanced.Morita.coefficientRightModule ℤ R S Q M P
  let := TensorProduct.Balanced.Morita.coefficientActionsComm ℤ R S Q M P
  let := TensorProduct.Balanced.Morita.coefficientLeftTower ℤ R S Q M P
  let := TensorProduct.Balanced.Morita.coefficientRightTower ℤ R S Q M P
  let B := TensorProduct.Balanced ℤ S P Q
  let dB : Module ℤ B := inferInstance
  let : Module ℤ B := dB
  let := TensorProduct.Balanced.leftModule ℤ S R P Q
  let := TensorProduct.Balanced.rightModule ℤ S R P Q
  let e : B ≃ₗ[ℤ] R := u.toAddEquiv.toIntLinearEquiv (modM := dB) (modM₂ := ringInteger)
  have eL (r : R) (b : B) : e (r • b) = r * e b := hu r b
  have eR (r : R) (b : B) : e (op r • b) = e b * r := u.map_smul (op r) b
  let D := TensorProduct.Balanced ℤ S A Q
  let := TensorProduct.Balanced.leftModule ℤ S S A Q
  let J := TensorProduct.Balanced ℤ R I B
  let := TensorProduct.Balanced.leftModule ℤ R S I B
  let a₁ : D ≃ₗ[ℤ] J := assoc ℤ R S I P Q
  have a₁S (s : S) (x : D) : a₁ (s • x) = s • a₁ x :=
    assoc_left_smul ℤ R S I P Q S s x
  let a₂ : J ≃ₗ[ℤ] I := rightContraction R I B e eL
  have a₂S (s : S) (x : J) : a₂ (s • x) = s • a₂ x :=
    rightContraction_left_smul R I B e eL S s x
  have hP : ∀ (s : S) (p : P), (LinearEquiv.refl ℤ P) (op s • p) =
      op s • (LinearEquiv.refl ℤ P) p := fun _ _ => rfl
  let b₁ := congr (LinearEquiv.refl ℤ P) a₁ hP a₁S
  let b₂ := congr (LinearEquiv.refl ℤ P) a₂ hP a₂S
  let a₃ := (assoc ℤ S R P Q M).symm
  let a₄ := leftContraction R B M e eR
  let i : I := mk ℤ R Q M q₀ m
  let b₀ : B := mk ℤ S P Q p₀ q₀
  let b : B := mk ℤ S P Q p₁ q₁
  let d : D := mk ℤ S A Q (mk ℤ R I P i p₁) q₁
  let j : J := mk ℤ R I B i b
  let m' : M := op (u b) • m
  let i' : I := mk ℤ R Q M q₀ m'
  simp only [rawReturnIso, rawReturnMk, rawReturnOuterMk, LinearEquiv.trans_apply,
    assoc_mk_mk]
  change a₄ (a₃ (b₂ (b₁ (mk ℤ S P D p₀ d)))) = u b₀ • m'
  have ha₁ : a₁ d = j := assoc_mk_mk ℤ R S I P Q i p₁ q₁
  have hb₁ : b₁ (mk ℤ S P D p₀ d) = mk ℤ S P J p₀ j :=
    (congr_mk (k := ℤ) (R := S) (M := P) (N := D) (M' := P) (N' := J)
      (LinearEquiv.refl ℤ P) a₁ hP a₁S p₀ d).trans
      (congrArg (fun x : J => mk ℤ S P J p₀ x) ha₁)
  have ha₂ : a₂ j = i' :=
    (rightContraction_mk R I B e eL i b).trans
      (TensorProduct.Balanced.rightModule_smul_mk ℤ R R Q M (op (e b)) q₀ m)
  have hb₂ : b₂ (mk ℤ S P J p₀ j) = mk ℤ S P I p₀ i' :=
    (congr_mk (k := ℤ) (R := S) (M := P) (N := J) (M' := P) (N' := I)
      (LinearEquiv.refl ℤ P) a₂ hP a₂S p₀ j).trans
      (congrArg (fun x : I => mk ℤ S P I p₀ x) ha₂)
  have ha₃ : a₃ (mk ℤ S P I p₀ i') = mk ℤ R B M b₀ m' :=
    assoc_symm_mk_mk ℤ S R P Q M p₀ q₀ m'
  have ha₄ : a₄ (mk ℤ R B M b₀ m') = u b₀ • m' :=
    leftContraction_mk R B M e eR b₀ m'
  exact (congrArg (fun x : TensorProduct.Balanced ℤ S P J => a₄ (a₃ (b₂ x))) hb₁).trans
    ((congrArg (fun x : TensorProduct.Balanced ℤ S P I => a₄ (a₃ x)) hb₂).trans
      ((congrArg a₄ ha₃).trans ha₄))

include u hu in
/-- Let R,S be rings in independent universes r,s, P an (R,S)-bimodule and Q an (S,R)-bimodule with
carriers in v. Let M be an R-bimodule with abelian carrier and integer scalar action in v. Put
T(M)=(P⊗_S((Q⊗_R M)⊗_R P))⊗_S Q, and Γ(p₀,q₀,m,p₁,q₁) for its class with those five factors in
that order. Let α:P⊗_S Q≃R be right R-linear and satisfy α(r•b)=rα(b) for all r∈R,b∈P⊗_S Q. Thus
α preserves both R-actions. Combine the given R and Rᵒᵖ-actions on M into an E_R=R⊗_ℤRᵒᵖ-module.
The return contraction c_α:T(M)→M is E_R-linear, so it commutes with every enveloping scalar as
well as both endpoint actions. -/
def rawReturnLinear :
    letI : Module (R ⊗[ℤ] Rᵐᵒᵖ) M := @TensorProduct.Algebra.module ℤ R Rᵐᵒᵖ M
      inferInstance (inferInstance : AddCommMonoid M) givenIntegerModule
      inferInstance inferInstance (inferInstance : Module R M)
      (inferInstance : Module Rᵐᵒᵖ M) inferInstance inferInstance
      (Module.intModule_isScalarTower (R := R) (M := M)
        (Algebra.toModule : Module ℤ R) givenIntegerModule)
      (Module.intModule_isScalarTower (R := Rᵐᵒᵖ) (M := M)
        (Algebra.toModule : Module ℤ Rᵐᵒᵖ) givenIntegerModule) inferInstance
    rawReturnObject R S P Q M →ₗ[R ⊗[ℤ] Rᵐᵒᵖ] M := by
  letI : Module (R ⊗[ℤ] Rᵐᵒᵖ) M := @TensorProduct.Algebra.module ℤ R Rᵐᵒᵖ M
    inferInstance (inferInstance : AddCommMonoid M) givenIntegerModule
    inferInstance inferInstance (inferInstance : Module R M)
    (inferInstance : Module Rᵐᵒᵖ M) inferInstance inferInstance
    (Module.intModule_isScalarTower (R := R) (M := M)
      (Algebra.toModule : Module ℤ R) givenIntegerModule)
    (Module.intModule_isScalarTower (R := Rᵐᵒᵖ) (M := M)
      (Algebra.toModule : Module ℤ Rᵐᵒᵖ) givenIntegerModule) inferInstance
  letI := TensorProduct.Balanced.leftModule ℤ S R P Q
  letI := TensorProduct.Balanced.rightModule ℤ S R P Q
  refine
    { toFun := rawReturnIso R S P Q M u hu
      map_add' := (rawReturnIso R S P Q M u hu).map_add
      map_smul' := ?_ }
  intro z x
  change rawReturnIso R S P Q M u hu
      ((rawReturnObject R S P Q M).isModule.smul z x) =
    z • rawReturnIso R S P Q M u hu x
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    have h : (rawReturnIso R S P Q M u hu).toLinearMap.toAddMonoidHom.comp
        (DistribSMul.toAddMonoidHom (rawReturnObject R S P Q M) (a ⊗ₜ[ℤ] b)) =
      (DistribSMul.toAddMonoidHom M (a ⊗ₜ[ℤ] b)).comp
        (rawReturnIso R S P Q M u hu).toLinearMap.toAddMonoidHom := by
      apply rawReturnHom_ext R S P Q M
      intro p₀ q₀ m p₁ q₁
      change rawReturnIso R S P Q M u hu
        ((rawReturnObject R S P Q M).isModule.smul (a ⊗ₜ[ℤ] b)
          (rawReturnMk R S P Q M p₀ q₀ m p₁ q₁)) =
        (a ⊗ₜ[ℤ] b) • rawReturnIso R S P Q M u hu
          (rawReturnMk R S P Q M p₀ q₀ m p₁ q₁)
      rw [rawReturnModule_tmul_mk, rawReturnIso_mk, rawReturnIso_mk]
      have hL : u (mk ℤ S P Q (a • p₀) q₀) = a * u (mk ℤ S P Q p₀ q₀) := by
        rw [← TensorProduct.Balanced.leftModule_smul_mk ℤ S R P Q]
        exact hu a (mk ℤ S P Q p₀ q₀)
      have hR : u (mk ℤ S P Q p₁ (b • q₁)) = u (mk ℤ S P Q p₁ q₁) * b.unop := by
        rw [← TensorProduct.Balanced.rightModule_smul_mk ℤ S R P Q]
        exact u.map_smul b (mk ℤ S P Q p₁ q₁)
      rw [hL, hR, TensorProduct.Algebra.smul_def, op_mul, op_unop,
        mul_smul, mul_smul]
      exact congrArg (fun y : M => a • y)
        (smul_comm (u (mk ℤ S P Q p₀ q₀)) b
          (op (u (mk ℤ S P Q p₁ q₁)) • m))
    exact DFunLike.congr_fun h x
  | add z w hz hw =>
    let F := rawReturnIso R S P Q M u hu
    have hSource : (rawReturnObject R S P Q M).isModule.smul (z + w) x =
        (rawReturnObject R S P Q M).isModule.smul z x +
          (rawReturnObject R S P Q M).isModule.smul w x :=
      (rawReturnObject R S P Q M).isModule.add_smul z w x
    have hAdd : F ((rawReturnObject R S P Q M).isModule.smul z x +
        (rawReturnObject R S P Q M).isModule.smul w x) =
        F ((rawReturnObject R S P Q M).isModule.smul z x) +
          F ((rawReturnObject R S P Q M).isModule.smul w x) := F.map_add _ _
    exact (congrArg (fun y : rawReturnObject R S P Q M => F y) hSource).trans
      (hAdd.trans ((congrArg₂ (fun a b : M => a + b) hz hw).trans
        (add_smul z w (F x)).symm))

include u hu in
/-- Let R,S be rings in independent universes r,s, P an (R,S)-bimodule and Q an (S,R)-bimodule with
carriers in v. Let M be an R-bimodule with abelian carrier and integer scalar action in v. Put
T(M)=(P⊗_S((Q⊗_R M)⊗_R P))⊗_S Q, and Γ(p₀,q₀,m,p₁,q₁) for its class with those five factors in
that order. Let α:P⊗_S Q≃R be right R-linear and satisfy α(r•b)=rα(b) for all r∈R,b∈P⊗_S Q. Thus
α preserves both R-actions. For M with the enveloping action reconstructed from its given
endpoints, c_α⁻¹:M→T(M) is E_R-linear. In paired tensor coordinates it inserts α⁻¹(1) on the
left and on the right of m, then reassociates to the raw five-factor carrier. -/
def rawReturnInverseLinear :
    letI : Module (R ⊗[ℤ] Rᵐᵒᵖ) M := @TensorProduct.Algebra.module ℤ R Rᵐᵒᵖ M
      inferInstance (inferInstance : AddCommMonoid M) givenIntegerModule
      inferInstance inferInstance (inferInstance : Module R M)
      (inferInstance : Module Rᵐᵒᵖ M) inferInstance inferInstance
      (Module.intModule_isScalarTower (R := R) (M := M)
        (Algebra.toModule : Module ℤ R) givenIntegerModule)
      (Module.intModule_isScalarTower (R := Rᵐᵒᵖ) (M := M)
        (Algebra.toModule : Module ℤ Rᵐᵒᵖ) givenIntegerModule) inferInstance
    M →ₗ[R ⊗[ℤ] Rᵐᵒᵖ] rawReturnObject R S P Q M := by
  letI : Module (R ⊗[ℤ] Rᵐᵒᵖ) M := @TensorProduct.Algebra.module ℤ R Rᵐᵒᵖ M
    inferInstance (inferInstance : AddCommMonoid M) givenIntegerModule
    inferInstance inferInstance (inferInstance : Module R M)
    (inferInstance : Module Rᵐᵒᵖ M) inferInstance inferInstance
    (Module.intModule_isScalarTower (R := R) (M := M)
      (Algebra.toModule : Module ℤ R) givenIntegerModule)
    (Module.intModule_isScalarTower (R := Rᵐᵒᵖ) (M := M)
      (Algebra.toModule : Module ℤ Rᵐᵒᵖ) givenIntegerModule) inferInstance
  let e := rawReturnIso R S P Q M u hu
  refine { toFun := e.symm, map_add' := e.symm.map_add, map_smul' := ?_ }
  intro z m
  apply e.injective
  have h := (rawReturnLinear R S P Q M u hu).map_smul z (e.symm m)
  change e ((rawReturnObject R S P Q M).isModule.smul z (e.symm m)) =
    z • e (e.symm m) at h
  rw [LinearEquiv.apply_symm_apply] at h
  exact (e.apply_symm_apply (z • m)).trans h.symm

include u hu in
/-- Let R,S be rings in independent universes r,s, P an (R,S)-bimodule and Q an (S,R)-bimodule with
carriers in v. Let M be an R-bimodule with abelian carrier and integer scalar action in v. Put
T(M)=(P⊗_S((Q⊗_R M)⊗_R P))⊗_S Q, and Γ(p₀,q₀,m,p₁,q₁) for its class with those five factors in
that order. Let α:P⊗_S Q≃R be right R-linear and satisfy α(r•b)=rα(b) for all r∈R,b∈P⊗_S Q. Thus
α preserves both R-actions. The mutually inverse E_R-linear contraction maps give T(M)≅M in
ModuleCat_v(E_R), where E_R=R⊗_ℤRᵒᵖ and the target uses its combined given R-actions. The
forward map has value α(p₀⊗q₀)•m•α(p₁⊗q₁) on Γ. -/
def rawReturnModuleIso :
    letI : Module (R ⊗[ℤ] Rᵐᵒᵖ) M := @TensorProduct.Algebra.module ℤ R Rᵐᵒᵖ M
      inferInstance (inferInstance : AddCommMonoid M) givenIntegerModule
      inferInstance inferInstance (inferInstance : Module R M)
      (inferInstance : Module Rᵐᵒᵖ M) inferInstance inferInstance
      (Module.intModule_isScalarTower (R := R) (M := M)
        (Algebra.toModule : Module ℤ R) givenIntegerModule)
      (Module.intModule_isScalarTower (R := Rᵐᵒᵖ) (M := M)
        (Algebra.toModule : Module ℤ Rᵐᵒᵖ) givenIntegerModule) inferInstance
    rawReturnObject R S P Q M ≅ ModuleCat.of (R ⊗[ℤ] Rᵐᵒᵖ) M := by
  letI : Module (R ⊗[ℤ] Rᵐᵒᵖ) M := @TensorProduct.Algebra.module ℤ R Rᵐᵒᵖ M
    inferInstance (inferInstance : AddCommMonoid M) givenIntegerModule
    inferInstance inferInstance (inferInstance : Module R M)
    (inferInstance : Module Rᵐᵒᵖ M) inferInstance inferInstance
    (Module.intModule_isScalarTower (R := R) (M := M)
      (Algebra.toModule : Module ℤ R) givenIntegerModule)
    (Module.intModule_isScalarTower (R := Rᵐᵒᵖ) (M := M)
      (Algebra.toModule : Module ℤ Rᵐᵒᵖ) givenIntegerModule) inferInstance
  let X := rawReturnObject R S P Q M
  let Y := ModuleCat.of (R ⊗[ℤ] Rᵐᵒᵖ) M
  refine
    { hom := @ModuleCat.ofHom (R ⊗[ℤ] Rᵐᵒᵖ) _ X.carrier Y.carrier
        X.isAddCommGroup X.isModule Y.isAddCommGroup Y.isModule
        (rawReturnLinear R S P Q M u hu)
      inv := @ModuleCat.ofHom (R ⊗[ℤ] Rᵐᵒᵖ) _ Y.carrier X.carrier
        Y.isAddCommGroup Y.isModule X.isAddCommGroup X.isModule
        (rawReturnInverseLinear R S P Q M u hu)
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (rawReturnIso R S P Q M u hu).symm_apply_apply x
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (rawReturnIso R S P Q M u hu).apply_symm_apply x

/-- Let R,S be rings in independent universes r,s, P an (R,S)-bimodule and Q an (S,R)-bimodule with
carriers in v. Let M be an R-bimodule with abelian carrier and integer scalar action in v. Put
T(M)=(P⊗_S((Q⊗_R M)⊗_R P))⊗_S Q, and Γ(p₀,q₀,m,p₁,q₁) for its class with those five factors in
that order. Let α:P⊗_S Q≃R be right R-linear and satisfy α(r•b)=rα(b) for all r∈R,b∈P⊗_S Q. Thus
α preserves both R-actions. For every ξ∈T(M), the forward morphism of the E_R-module isomorphism
sends ξ to c_α(ξ), where c_α is the integer-linear raw return equivalence. Both maps use the
same contraction and coefficient carrier. -/
@[simp]
theorem rawReturnModuleIso_hom_apply (x : rawReturnTensor R S P Q M) :
    ((rawReturnModuleIso R S P Q M u hu).hom).hom x =
      rawReturnIso R S P Q M u hu x := rfl

/-- Let R,S be rings in independent universes r,s, P an (R,S)-bimodule and Q an (S,R)-bimodule with
carriers in v. Let M be an R-bimodule with abelian carrier and integer scalar action in v. Put
T(M)=(P⊗_S((Q⊗_R M)⊗_R P))⊗_S Q, and Γ(p₀,q₀,m,p₁,q₁) for its class with those five factors in
that order. Let α:P⊗_S Q≃R be right R-linear and satisfy α(r•b)=rα(b) for all r∈R,b∈P⊗_S Q. Thus
α preserves both R-actions. For Γ(p₀,q₀,m,p₁,q₁), the forward module isomorphism evaluates to
α(p₀⊗q₀)•(op(α(p₁⊗q₁))•m), in the module M with its given left and right actions. -/
@[simp]
theorem rawReturnModuleIso_hom_mk (p₀ : P) (q₀ : Q) (m : M) (p₁ : P) (q₁ : Q) :
    ((rawReturnModuleIso R S P Q M u hu).hom).hom
        (rawReturnMk R S P Q M p₀ q₀ m p₁ q₁) =
      u (mk ℤ S P Q p₀ q₀) • (op (u (mk ℤ S P Q p₁ q₁)) • m) :=
  rawReturnIso_mk R S P Q M u hu p₀ q₀ m p₁ q₁

end ModuleCat.Bimodule.Morita
