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

public import MathlibExt.Algebra.Category.ModuleCat.Bimodule.Over.Morita
public import MathlibExt.LinearAlgebra.TensorProduct.Balanced.Contraction

/-!
# Relative tensor-return contractions and their coefficient values

Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) k-compatible
bimodules with independent carriers p,q. For a k-compatible R-bimodule M in m, the raw return
T(M)=(P⊗_S((Q⊗_R M)⊗_R P))⊗_S Q has carrier max(p,q,m).

A right R-linear isomorphism α:P⊗_S Q≃R that also preserves the left R-action gives a k-linear
equivalence T(M)≃M. The coefficient formula is Γ(p₀,q₀,m,p₁,q₁)↦α(p₀⊗q₀)•m•α(p₁⊗q₁). The forward
and inverse maps are linear for R⊗_kRᵒᵖ and preserve the chosen ground k-action.

At a common carrier height W=max(p,q,v), the same maps give an isomorphism of relative
enveloping-module objects. The coefficient-object value, raw tensor value, and ordered
scalar-action value coincide. The scalar-function formula uses the right-linear contraction
alone; left compatibility is used for the complete return equivalence.
-/

@[expose] public section

noncomputable section

open CategoryTheory MulOpposite TensorProduct.Balanced
open scoped TensorProduct

universe u r s p q m v

namespace ModuleCat.Bimodule.Over.Morita

variable (k : Type u) [CommRing k]
  (R : Type r) [Ring R] [Algebra k R] (S : Type s) [Ring S] [Algebra k S]
  (P : Type p) [AddCommGroup P] [Module k P]
  [Module R P] [Module Sᵐᵒᵖ P] [SMulCommClass R Sᵐᵒᵖ P]
  [IsScalarTower k R P] [IsScalarTower k Sᵐᵒᵖ P]
  (Q : Type q) [AddCommGroup Q] [Module k Q]
  [Module S Q] [Module Rᵐᵒᵖ Q] [SMulCommClass S Rᵐᵒᵖ Q]
  [IsScalarTower k S Q] [IsScalarTower k Rᵐᵒᵖ Q]

section Raw

variable (M : Type m) [AddCommGroup M] [givenGroundModule : Module k M]
  [Module R M] [Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M]
  [IsScalarTower k R M] [IsScalarTower k Rᵐᵒᵖ M]

include R S P Q M in
/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) bimodules in
independent carrier universes p,q. Both endpoint actions on each module commute and restrict to
its given k-action. Let M be a k-module in m with commuting left and right R-actions compatible
with its k-action. Write T(M)=(P⊗_S((Q⊗_R M)⊗_R P))⊗_S Q and Γ(p₀,q₀,m,p₁,q₁) for its
five-factor class. The carrier T(M) is in max(p,q,m), with two balancing steps over R in its
middle coefficient and two outer steps over S. -/
abbrev rawReturnTensor : Type (max p q m) := by
  let C := TensorProduct.Balanced.Morita.coefficientTensor k R Q M P
  let dC : Module k C := inferInstance
  letI : Module k C := dC
  letI := TensorProduct.Balanced.Morita.coefficientLeftModule k R S Q M P
  letI := TensorProduct.Balanced.Morita.coefficientRightModule k R S Q M P
  letI := TensorProduct.Balanced.Morita.coefficientActionsComm k R S Q M P
  letI := TensorProduct.Balanced.Morita.coefficientLeftTower k R S Q M P
  letI := TensorProduct.Balanced.Morita.coefficientRightTower k R S Q M P
  exact TensorProduct.Balanced.assocSource k S S P C Q

include R S P Q M in
/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) bimodules in
independent carrier universes p,q. Both endpoint actions on each module commute and restrict to
its given k-action. Let M be a k-module in m with commuting left and right R-actions compatible
with its k-action. Write T(M)=(P⊗_S((Q⊗_R M)⊗_R P))⊗_S Q and Γ(p₀,q₀,m,p₁,q₁) for its
five-factor class. The left R-action acts on p₀ and the right R-action on q₁. Together with the
balanced ground k-action, these give an object of ModuleCat_{max(p,q,m)}(R⊗_kRᵒᵖ). -/
def rawReturnObject : ModuleCat.{max p q m} (R ⊗[k] Rᵐᵒᵖ) := by
  let C := TensorProduct.Balanced.Morita.coefficientTensor k R Q M P
  let dC : Module k C := inferInstance
  letI : Module k C := dC
  letI := TensorProduct.Balanced.Morita.coefficientLeftModule k R S Q M P
  letI := TensorProduct.Balanced.Morita.coefficientRightModule k R S Q M P
  letI := TensorProduct.Balanced.Morita.coefficientActionsComm k R S Q M P
  letI := TensorProduct.Balanced.Morita.coefficientLeftTower k R S Q M P
  letI := TensorProduct.Balanced.Morita.coefficientRightTower k R S Q M P
  exact tensorObject k S R Q P C

/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) bimodules in
independent carrier universes p,q. Both endpoint actions on each module commute and restrict to
its given k-action. Let M be a k-module in m with commuting left and right R-actions compatible
with its k-action. For p₀∈P,c∈(Q⊗_R M)⊗_R P,q₁∈Q, the class (p₀⊗_S c)⊗_S q₁ belongs to T(M). Its
carrier height is max(p,q,m), and c may be any element of the intermediate tensor. -/
def rawReturnOuterMk (p₀ : P)
    (c : TensorProduct.Balanced.Morita.coefficientTensor k R Q M P) (q₁ : Q) :
    rawReturnTensor k R S P Q M := by
  let C := TensorProduct.Balanced.Morita.coefficientTensor k R Q M P
  let dC : Module k C := inferInstance
  letI : Module k C := dC
  letI := TensorProduct.Balanced.Morita.coefficientLeftModule k R S Q M P
  letI := TensorProduct.Balanced.Morita.coefficientRightModule k R S Q M P
  letI := TensorProduct.Balanced.Morita.coefficientActionsComm k R S Q M P
  letI := TensorProduct.Balanced.Morita.coefficientLeftTower k R S Q M P
  letI := TensorProduct.Balanced.Morita.coefficientRightTower k R S Q M P
  letI := TensorProduct.Balanced.rightModule k S S P C
  exact TensorProduct.Balanced.mk k S (TensorProduct.Balanced k S P C) Q
    (TensorProduct.Balanced.mk k S P C p₀ c) q₁

/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) bimodules in
independent carrier universes p,q. Both endpoint actions on each module commute and restrict to
its given k-action. Let M be a k-module in m with commuting left and right R-actions compatible
with its k-action. Write T(M)=(P⊗_S((Q⊗_R M)⊗_R P))⊗_S Q and Γ(p₀,q₀,m,p₁,q₁) for its
five-factor class. For p₀,p₁∈P,q₀,q₁∈Q,m∈M, Γ=(p₀⊗_S((q₀⊗_R m)⊗_R p₁))⊗_S q₁. The ordered
factors and their R- and S-balancing are retained. -/
def rawReturnMk (p₀ : P) (q₀ : Q) (m : M) (p₁ : P) (q₁ : Q) :
    rawReturnTensor k R S P Q M := by
  letI := TensorProduct.Balanced.rightModule k R R Q M
  exact rawReturnOuterMk k R S P Q M p₀
    (TensorProduct.Balanced.mk k R (TensorProduct.Balanced k R Q M) P
        (TensorProduct.Balanced.mk k R Q M q₀ m) p₁) q₁

/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) bimodules in
independent carrier universes p,q. Both endpoint actions on each module commute and restrict to
its given k-action. Let M be a k-module in m with commuting left and right R-actions compatible
with its k-action. Write T(M)=(P⊗_S((Q⊗_R M)⊗_R P))⊗_S Q and Γ(p₀,q₀,m,p₁,q₁) for its
five-factor class. For an additive commutative monoid C' in any universe, additive maps
f,g:T(M)→C' are equal if they agree on Γ(p₀,q₀,m,p₁,q₁) for every five inputs. No coefficient
scalar action on C' is needed. -/
theorem rawReturnHom_ext {C' : Type*} [AddCommMonoid C']
    {f g : rawReturnTensor k R S P Q M →+ C'}
    (h : ∀ (p₀ : P) (q₀ : Q) (m : M) (p₁ : P) (q₁ : Q),
      f (rawReturnMk k R S P Q M p₀ q₀ m p₁ q₁) =
        g (rawReturnMk k R S P Q M p₀ q₀ m p₁ q₁)) : f = g := by
  let := TensorProduct.Balanced.rightModule k R R Q M
  let C := TensorProduct.Balanced.Morita.coefficientTensor k R Q M P
  let dC : Module k C := inferInstance
  let : Module k C := dC
  let := TensorProduct.Balanced.Morita.coefficientLeftModule k R S Q M P
  let := TensorProduct.Balanced.Morita.coefficientRightModule k R S Q M P
  let := TensorProduct.Balanced.Morita.coefficientActionsComm k R S Q M P
  let := TensorProduct.Balanced.Morita.coefficientLeftTower k R S Q M P
  let := TensorProduct.Balanced.Morita.coefficientRightTower k R S Q M P
  let := TensorProduct.Balanced.rightModule k S S P C
  let A := TensorProduct.Balanced k S P C
  apply TensorProduct.Balanced.addHom_ext k S A Q
  intro a q₁
  have ha : f.comp (((TensorProduct.Balanced.mk k S A Q).flip q₁).toAddMonoidHom) =
      g.comp (((TensorProduct.Balanced.mk k S A Q).flip q₁).toAddMonoidHom) := by
    apply TensorProduct.Balanced.addHom_ext k S P C
    intro p₀ c
    have hc : (f.comp (((TensorProduct.Balanced.mk k S A Q).flip q₁).toAddMonoidHom)).comp
        ((TensorProduct.Balanced.mk k S P C p₀).toAddMonoidHom) =
      (g.comp (((TensorProduct.Balanced.mk k S A Q).flip q₁).toAddMonoidHom)).comp
        ((TensorProduct.Balanced.mk k S P C p₀).toAddMonoidHom) := by
      apply TensorProduct.Balanced.Morita.coefficientHom_ext k R Q M P
      intro q₀ m p₁
      exact h p₀ q₀ m p₁ q₁
    exact DFunLike.congr_fun hc c
  exact DFunLike.congr_fun ha a

/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) bimodules in
independent carrier universes p,q. Both endpoint actions on each module commute and restrict to
its given k-action. Let M be a k-module in m with commuting left and right R-actions compatible
with its k-action. Write T(M)=(P⊗_S((Q⊗_R M)⊗_R P))⊗_S Q and Γ(p₀,q₀,m,p₁,q₁) for its
five-factor class. For r∈R,t∈Rᵒᵖ, (r⊗_k t)•Γ(p₀,q₀,m,p₁,q₁)=Γ(r•p₀,q₀,m,p₁,t•q₁). The middle
three factors are retained. -/
theorem rawReturnModule_tmul_mk (r : R) (t : Rᵐᵒᵖ)
    (p₀ : P) (q₀ : Q) (m : M) (p₁ : P) (q₁ : Q) :
    (rawReturnObject k R S P Q M).isModule.smul (r ⊗ₜ[k] t)
        (rawReturnMk k R S P Q M p₀ q₀ m p₁ q₁) =
      rawReturnMk k R S P Q M (r • p₀) q₀ m p₁ (t • q₁) := by
  let := TensorProduct.Balanced.rightModule k R R Q M
  let C := TensorProduct.Balanced.Morita.coefficientTensor k R Q M P
  let dC : Module k C := inferInstance
  let : Module k C := dC
  let := TensorProduct.Balanced.Morita.coefficientLeftModule k R S Q M P
  let := TensorProduct.Balanced.Morita.coefficientRightModule k R S Q M P
  let := TensorProduct.Balanced.Morita.coefficientActionsComm k R S Q M P
  let := TensorProduct.Balanced.Morita.coefficientLeftTower k R S Q M P
  let := TensorProduct.Balanced.Morita.coefficientRightTower k R S Q M P
  exact TensorProduct.Balanced.Morita.coefficientModule_tmul_mk k S R P C Q r t p₀
    (TensorProduct.Balanced.mk k R (TensorProduct.Balanced k R Q M) P
        (TensorProduct.Balanced.mk k R Q M q₀ m) p₁) q₁

variable
  (u : letI := TensorProduct.Balanced.leftModule k S R P Q
    letI := TensorProduct.Balanced.rightModule k S R P Q
    TensorProduct.Balanced k S P Q ≃ₗ[Rᵐᵒᵖ] R)
  (hu : letI := TensorProduct.Balanced.leftModule k S R P Q
    letI := TensorProduct.Balanced.rightModule k S R P Q
    ∀ (r : R) (b : TensorProduct.Balanced k S P Q), u (r • b) = r * u b)

include u hu in
/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) bimodules in
independent carrier universes p,q. Both endpoint actions on each module commute and restrict to
its given k-action. Let M be a k-module in m with commuting left and right R-actions compatible
with its k-action. Write T(M)=(P⊗_S((Q⊗_R M)⊗_R P))⊗_S Q and Γ(p₀,q₀,m,p₁,q₁) for its
five-factor class. Let α:P⊗_S Q≃R be right R-linear and satisfy α(r•b)=rα(b). The equivalence
c_α:T(M)≃_k M is obtained by reassociation and two α-contractions. Its pure value is
α(p₀⊗q₀)•(op(α(p₁⊗q₁))•m), with source carrier max(p,q,m) and target carrier m. -/
def rawReturnIso : rawReturnTensor k R S P Q M ≃ₗ[k] M := by
  let I := TensorProduct.Balanced k R Q M
  let dI : Module k I := inferInstance
  letI : Module k I := dI
  letI := TensorProduct.Balanced.rightModule k R R Q M
  letI := TensorProduct.Balanced.leftModule k R S Q M
  letI := TensorProduct.Balanced.leftSMulCommClass k R S Q M
  letI := TensorProduct.Balanced.leftRightSMulCommClass k R R Q M S
  letI := TensorProduct.Balanced.rightScalarTower k R R Q M
  letI := TensorProduct.Balanced.leftScalarTower k R S Q M
  let A := TensorProduct.Balanced.Morita.coefficientTensor k R Q M P
  let dA : Module k A := inferInstance
  letI : Module k A := dA
  letI := TensorProduct.Balanced.Morita.coefficientLeftModule k R S Q M P
  letI := TensorProduct.Balanced.Morita.coefficientRightModule k R S Q M P
  letI := TensorProduct.Balanced.Morita.coefficientActionsComm k R S Q M P
  letI := TensorProduct.Balanced.Morita.coefficientLeftTower k R S Q M P
  letI := TensorProduct.Balanced.Morita.coefficientRightTower k R S Q M P
  let B := TensorProduct.Balanced k S P Q
  let dB : Module k B := inferInstance
  letI : Module k B := dB
  letI := TensorProduct.Balanced.leftModule k S R P Q
  letI := TensorProduct.Balanced.rightModule k S R P Q
  letI := TensorProduct.Balanced.leftScalarTower k S R P Q
  letI := TensorProduct.Balanced.rightScalarTower k S R P Q
  let eLeft : B ≃ₗ[R] R := u.toAddEquiv.toLinearEquiv (by
    intro r b
    change u (r • b) = r * u b
    exact hu r b)
  let e : B ≃ₗ[k] R := eLeft.restrictScalars k
  have eL (r : R) (b : B) : e (r • b) = r * e b := hu r b
  have eR (r : R) (b : B) : e (op r • b) = e b * r := u.map_smul (op r) b
  let D := TensorProduct.Balanced k S A Q
  letI := TensorProduct.Balanced.leftModule k S S A Q
  let J := TensorProduct.Balanced k R I B
  letI := TensorProduct.Balanced.leftModule k R S I B
  let a₀ : rawReturnTensor k R S P Q M ≃ₗ[k] TensorProduct.Balanced k S P D :=
    TensorProduct.Balanced.assoc k S S P A Q
  let a₁ : D ≃ₗ[k] J := TensorProduct.Balanced.assoc k R S I P Q
  have a₁S (s : S) (x : D) : a₁ (s • x) = s • a₁ x :=
    TensorProduct.Balanced.assoc_left_smul k R S I P Q S s x
  let a₂ : J ≃ₗ[k] I := TensorProduct.Balanced.Over.rightContraction k R I B e eL
  have a₂S (s : S) (x : J) : a₂ (s • x) = s • a₂ x :=
    TensorProduct.Balanced.Over.rightContraction_left_smul k R I B e eL S s x
  let b₁ : TensorProduct.Balanced k S P D ≃ₗ[k] TensorProduct.Balanced k S P J :=
    TensorProduct.Balanced.congr (LinearEquiv.refl k P) a₁ (fun _ _ => rfl) a₁S
  let b₂ : TensorProduct.Balanced k S P J ≃ₗ[k] TensorProduct.Balanced k S P I :=
    TensorProduct.Balanced.congr (LinearEquiv.refl k P) a₂ (fun _ _ => rfl) a₂S
  let a₃ : TensorProduct.Balanced k S P I ≃ₗ[k] TensorProduct.Balanced k R B M :=
    (TensorProduct.Balanced.assoc k S R P Q M).symm
  let a₄ : TensorProduct.Balanced k R B M ≃ₗ[k] M :=
      TensorProduct.Balanced.Over.leftContraction k R B M e eR
  exact a₀.trans (b₁.trans (b₂.trans (a₃.trans a₄)))

/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) bimodules in
independent carrier universes p,q. Both endpoint actions on each module commute and restrict to
its given k-action. Let M be a k-module in m with commuting left and right R-actions compatible
with its k-action. Write T(M)=(P⊗_S((Q⊗_R M)⊗_R P))⊗_S Q and Γ(p₀,q₀,m,p₁,q₁) for its
five-factor class. Let α:P⊗_S Q≃R be right R-linear and satisfy α(r•b)=rα(b). For every
five-factor class, c_α(Γ(p₀,q₀,m,p₁,q₁))=α(p₀⊗q₀)•(op(α(p₁⊗q₁))•m). The scalar actions on the
result are the given left and right R-actions on M. -/
@[simp]
theorem rawReturnIso_mk (p₀ : P) (q₀ : Q) (m : M) (p₁ : P) (q₁ : Q) :
    rawReturnIso k R S P Q M u hu (rawReturnMk k R S P Q M p₀ q₀ m p₁ q₁) =
      u (TensorProduct.Balanced.mk k S P Q p₀ q₀) •
          (op (u (TensorProduct.Balanced.mk k S P Q p₁ q₁)) • m) := by
  let I := TensorProduct.Balanced k R Q M
  let dI : Module k I := inferInstance
  let : Module k I := dI
  let := TensorProduct.Balanced.rightModule k R R Q M
  let := TensorProduct.Balanced.leftModule k R S Q M
  let := TensorProduct.Balanced.leftSMulCommClass k R S Q M
  let := TensorProduct.Balanced.leftRightSMulCommClass k R R Q M S
  let := TensorProduct.Balanced.rightScalarTower k R R Q M
  let := TensorProduct.Balanced.leftScalarTower k R S Q M
  let A := TensorProduct.Balanced.Morita.coefficientTensor k R Q M P
  let dA : Module k A := inferInstance
  let : Module k A := dA
  let := TensorProduct.Balanced.Morita.coefficientLeftModule k R S Q M P
  let := TensorProduct.Balanced.Morita.coefficientRightModule k R S Q M P
  let := TensorProduct.Balanced.Morita.coefficientActionsComm k R S Q M P
  let := TensorProduct.Balanced.Morita.coefficientLeftTower k R S Q M P
  let := TensorProduct.Balanced.Morita.coefficientRightTower k R S Q M P
  let B := TensorProduct.Balanced k S P Q
  let dB : Module k B := inferInstance
  let : Module k B := dB
  let := TensorProduct.Balanced.leftModule k S R P Q
  let := TensorProduct.Balanced.rightModule k S R P Q
  let := TensorProduct.Balanced.leftScalarTower k S R P Q
  let := TensorProduct.Balanced.rightScalarTower k S R P Q
  let eLeft : B ≃ₗ[R] R := u.toAddEquiv.toLinearEquiv (by
    intro r b
    change u (r • b) = r * u b
    exact hu r b)
  let e : B ≃ₗ[k] R := eLeft.restrictScalars k
  have eL (r : R) (b : B) : e (r • b) = r * e b := hu r b
  have eR (r : R) (b : B) : e (op r • b) = e b * r := u.map_smul (op r) b
  let D := TensorProduct.Balanced k S A Q
  let := TensorProduct.Balanced.leftModule k S S A Q
  let J := TensorProduct.Balanced k R I B
  let := TensorProduct.Balanced.leftModule k R S I B
  let a₁ : D ≃ₗ[k] J := TensorProduct.Balanced.assoc k R S I P Q
  have a₁S (s : S) (x : D) : a₁ (s • x) = s • a₁ x :=
    TensorProduct.Balanced.assoc_left_smul k R S I P Q S s x
  let a₂ : J ≃ₗ[k] I := TensorProduct.Balanced.Over.rightContraction k R I B e eL
  have a₂S (s : S) (x : J) : a₂ (s • x) = s • a₂ x :=
    TensorProduct.Balanced.Over.rightContraction_left_smul k R I B e eL S s x
  have hP : ∀ (s : S) (p : P), (LinearEquiv.refl k P) (op s • p) =
      op s • (LinearEquiv.refl k P) p := fun _ _ => rfl
  let b₁ := TensorProduct.Balanced.congr (LinearEquiv.refl k P) a₁ hP a₁S
  let b₂ := TensorProduct.Balanced.congr (LinearEquiv.refl k P) a₂ hP a₂S
  let a₃ := (TensorProduct.Balanced.assoc k S R P Q M).symm
  let a₄ := TensorProduct.Balanced.Over.leftContraction k R B M e eR
  let i : I := TensorProduct.Balanced.mk k R Q M q₀ m
  let b₀ : B := TensorProduct.Balanced.mk k S P Q p₀ q₀
  let b : B := TensorProduct.Balanced.mk k S P Q p₁ q₁
  let d : D := TensorProduct.Balanced.mk k S A Q (TensorProduct.Balanced.mk k R I P i p₁) q₁
  let j : J := TensorProduct.Balanced.mk k R I B i b
  let m' : M := op (u b) • m
  let i' : I := TensorProduct.Balanced.mk k R Q M q₀ m'
  simp only [rawReturnIso, rawReturnMk, rawReturnOuterMk, LinearEquiv.trans_apply,
    TensorProduct.Balanced.assoc_mk_mk]
  change a₄ (a₃ (b₂ (b₁ (TensorProduct.Balanced.mk k S P D p₀ d)))) = u b₀ • m'
  have ha₁ : a₁ d = j := TensorProduct.Balanced.assoc_mk_mk k R S I P Q i p₁ q₁
  have hb₁ : b₁ (TensorProduct.Balanced.mk k S P D p₀ d) = TensorProduct.Balanced.mk k S P J p₀ j :=
    (TensorProduct.Balanced.congr_mk (k := k) (R := S) (M := P) (N := D) (M' := P) (N' := J)
      (LinearEquiv.refl k P) a₁ hP a₁S p₀ d).trans
      (congrArg (fun x : J => TensorProduct.Balanced.mk k S P J p₀ x) ha₁)
  have ha₂ : a₂ j = i' :=
    (TensorProduct.Balanced.Over.rightContraction_mk k R I B e eL i b).trans
      (TensorProduct.Balanced.rightModule_smul_mk k R R Q M (op (e b)) q₀ m)
  have hb₂ : b₂ (TensorProduct.Balanced.mk k S P J p₀ j) =
      TensorProduct.Balanced.mk k S P I p₀ i' :=
    (TensorProduct.Balanced.congr_mk (k := k) (R := S) (M := P) (N := J) (M' := P) (N' := I)
      (LinearEquiv.refl k P) a₂ hP a₂S p₀ j).trans
      (congrArg (fun x : I => TensorProduct.Balanced.mk k S P I p₀ x) ha₂)
  have ha₃ : a₃ (TensorProduct.Balanced.mk k S P I p₀ i') =
      TensorProduct.Balanced.mk k R B M b₀ m' :=
    TensorProduct.Balanced.assoc_symm_mk_mk k S R P Q M p₀ q₀ m'
  have ha₄ : a₄ (TensorProduct.Balanced.mk k R B M b₀ m') = u b₀ • m' :=
    TensorProduct.Balanced.Over.leftContraction_mk k R B M e eR b₀ m'
  exact (congrArg (fun x : TensorProduct.Balanced k S P J => a₄ (a₃ (b₂ x))) hb₁).trans
    ((congrArg (fun x : TensorProduct.Balanced k S P I => a₄ (a₃ x)) hb₂).trans
      ((congrArg a₄ ha₃).trans ha₄))

include u hu in
/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) bimodules in
independent carrier universes p,q. Both endpoint actions on each module commute and restrict to
its given k-action. Let M be a k-module in m with commuting left and right R-actions compatible
with its k-action. Write T(M)=(P⊗_S((Q⊗_R M)⊗_R P))⊗_S Q and Γ(p₀,q₀,m,p₁,q₁) for its
five-factor class. Let α:P⊗_S Q≃R be right R-linear and satisfy α(r•b)=rα(b). Endow M with the
R⊗_kRᵒᵖ-action combined from its given ground and endpoint actions. Then c_α:T(M)→M is
R⊗_kRᵒᵖ-linear, for the computed enveloping action on T(M). -/
def rawReturnLinear :
    letI : Module (R ⊗[k] Rᵐᵒᵖ) M := TensorProduct.Algebra.module
    rawReturnObject k R S P Q M →ₗ[R ⊗[k] Rᵐᵒᵖ] M := by
  letI : Module (R ⊗[k] Rᵐᵒᵖ) M := TensorProduct.Algebra.module
  letI := TensorProduct.Balanced.leftModule k S R P Q
  letI := TensorProduct.Balanced.rightModule k S R P Q
  refine
    { toFun := rawReturnIso k R S P Q M u hu
      map_add' := (rawReturnIso k R S P Q M u hu).map_add
      map_smul' := ?_ }
  intro z x
  change rawReturnIso k R S P Q M u hu
      ((rawReturnObject k R S P Q M).isModule.smul z x) =
    z • rawReturnIso k R S P Q M u hu x
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    have h : (rawReturnIso k R S P Q M u hu).toLinearMap.toAddMonoidHom.comp
        (DistribSMul.toAddMonoidHom (rawReturnObject k R S P Q M) (a ⊗ₜ[k] b)) =
      (DistribSMul.toAddMonoidHom M (a ⊗ₜ[k] b)).comp
        (rawReturnIso k R S P Q M u hu).toLinearMap.toAddMonoidHom := by
      apply rawReturnHom_ext k R S P Q M
      intro p₀ q₀ m p₁ q₁
      change rawReturnIso k R S P Q M u hu
        ((rawReturnObject k R S P Q M).isModule.smul (a ⊗ₜ[k] b)
          (rawReturnMk k R S P Q M p₀ q₀ m p₁ q₁)) =
        (a ⊗ₜ[k] b) • rawReturnIso k R S P Q M u hu
          (rawReturnMk k R S P Q M p₀ q₀ m p₁ q₁)
      rw [rawReturnModule_tmul_mk, rawReturnIso_mk, rawReturnIso_mk]
      have hL : u (TensorProduct.Balanced.mk k S P Q (a • p₀) q₀) =
          a * u (TensorProduct.Balanced.mk k S P Q p₀ q₀) := by
        rw [← TensorProduct.Balanced.leftModule_smul_mk k S R P Q]
        exact hu a (TensorProduct.Balanced.mk k S P Q p₀ q₀)
      have hR : u (TensorProduct.Balanced.mk k S P Q p₁ (b • q₁)) =
          u (TensorProduct.Balanced.mk k S P Q p₁ q₁) * b.unop := by
        rw [← TensorProduct.Balanced.rightModule_smul_mk k S R P Q]
        exact u.map_smul b (TensorProduct.Balanced.mk k S P Q p₁ q₁)
      rw [hL, hR, TensorProduct.Algebra.smul_def, op_mul, op_unop,
        mul_smul, mul_smul]
      exact congrArg (fun y : M => a • y)
        (smul_comm (u (TensorProduct.Balanced.mk k S P Q p₀ q₀)) b
          (op (u (TensorProduct.Balanced.mk k S P Q p₁ q₁)) • m))
    exact DFunLike.congr_fun h x
  | add z w hz hw =>
    let F := rawReturnIso k R S P Q M u hu
    have hSource : (rawReturnObject k R S P Q M).isModule.smul (z + w) x =
        (rawReturnObject k R S P Q M).isModule.smul z x +
          (rawReturnObject k R S P Q M).isModule.smul w x :=
      (rawReturnObject k R S P Q M).isModule.add_smul z w x
    have hAdd : F ((rawReturnObject k R S P Q M).isModule.smul z x +
        (rawReturnObject k R S P Q M).isModule.smul w x) =
        F ((rawReturnObject k R S P Q M).isModule.smul z x) +
          F ((rawReturnObject k R S P Q M).isModule.smul w x) := F.map_add _ _
    exact (congrArg (fun y : rawReturnObject k R S P Q M => F y) hSource).trans
      (hAdd.trans ((congrArg₂ (fun a b : M => a + b) hz hw).trans
        (add_smul z w (F x)).symm))

include u hu in
/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) bimodules in
independent carrier universes p,q. Both endpoint actions on each module commute and restrict to
its given k-action. Let M be a k-module in m with commuting left and right R-actions compatible
with its k-action. Write T(M)=(P⊗_S((Q⊗_R M)⊗_R P))⊗_S Q and Γ(p₀,q₀,m,p₁,q₁) for its
five-factor class. Let α:P⊗_S Q≃R be right R-linear and satisfy α(r•b)=rα(b). The inverse
c_α⁻¹:M→T(M) is linear over R⊗_kRᵒᵖ. In paired tensor coordinates it inserts α⁻¹(1) on each side
of m, then reverses the reassociation to T(M). -/
def rawReturnInverseLinear :
    letI : Module (R ⊗[k] Rᵐᵒᵖ) M := TensorProduct.Algebra.module
    M →ₗ[R ⊗[k] Rᵐᵒᵖ] rawReturnObject k R S P Q M := by
  letI : Module (R ⊗[k] Rᵐᵒᵖ) M := TensorProduct.Algebra.module
  let e := rawReturnIso k R S P Q M u hu
  refine { toFun := e.symm, map_add' := e.symm.map_add, map_smul' := ?_ }
  intro z m
  apply e.injective
  have h := (rawReturnLinear k R S P Q M u hu).map_smul z (e.symm m)
  change e ((rawReturnObject k R S P Q M).isModule.smul z (e.symm m)) =
    z • e (e.symm m) at h
  rw [LinearEquiv.apply_symm_apply] at h
  exact (e.apply_symm_apply (z • m)).trans h.symm

end Raw

section Scalar

variable
  (u : letI := TensorProduct.Balanced.leftModule k S R P Q
    letI := TensorProduct.Balanced.rightModule k S R P Q
    TensorProduct.Balanced k S P Q ≃ₗ[Rᵐᵒᵖ] R)

/-- Let k be a commutative ring in u, R a k-algebra ring in r, S a ring in s, P a k-module in p with
a right S-action, and Q a k-module in q with commuting left S and right R-actions whose right
R-action is compatible with k. Let α:P⊗_S Q≃R be right R-linear. For p₀∈P,q₀∈Q, the contraction
scalar a(p₀,q₀) is α(p₀⊗_S q₀)∈R. This scalar is used in the ordered return-value formula. -/
def contractionScalar (p₀ : P) (q₀ : Q) : R := by
  let f : TensorProduct.Balanced k S P Q → R := u.toFun
  exact f (TensorProduct.Balanced.mk k S P Q p₀ q₀)
omit [SMulCommClass R Sᵐᵒᵖ P] [IsScalarTower k R P] [IsScalarTower k Sᵐᵒᵖ P]
  [IsScalarTower k S Q] [Algebra k S] [Module R P] in
/-- Let k be a commutative ring in u, R a k-algebra ring in r, S a ring in s, P a k-module in p with
a right S-action, and Q a k-module in q with commuting left S and right R-actions whose right
R-action is compatible with k. Let α:P⊗_S Q≃R be right R-linear. For every p₀,q₀,
a(p₀,q₀)=α(p₀⊗_S q₀). The equality uses the same right-R-linear contraction and the S-balanced
pair class. -/
@[simp]
theorem contractionScalar_mk (p₀ : P) (q₀ : Q) :
    contractionScalar k R S P Q u p₀ q₀ =
      u (TensorProduct.Balanced.mk k S P Q p₀ q₀) := rfl

end Scalar

section Native

variable (M : Type (max p q v)) [AddCommGroup M] [Module k M]
  [Module R M] [Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M]
  [IsScalarTower k R M] [IsScalarTower k Rᵐᵒᵖ M]
  (u : letI := TensorProduct.Balanced.leftModule k S R P Q
    letI := TensorProduct.Balanced.rightModule k S R P Q
    TensorProduct.Balanced k S P Q ≃ₗ[Rᵐᵒᵖ] R)
  (hu : letI := TensorProduct.Balanced.leftModule k S R P Q
    letI := TensorProduct.Balanced.rightModule k S R P Q
    ∀ (r : R) (b : TensorProduct.Balanced k S P Q), u (r • b) = r * u b)

include u hu in
/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) bimodules in
independent carrier universes p,q. Both endpoint actions on each module commute and restrict to
its given k-action. Choose W=max(p,q,v), and let M be a k-module with carrier W and commuting
left and right R-actions compatible with k. Write T(M)=(P⊗_S((Q⊗_R M)⊗_R P))⊗_S Q and
Γ(p₀,q₀,m,p₁,q₁) for its five-factor class. Let α:P⊗_S Q≃R be right R-linear and satisfy
α(r•b)=rα(b). The E_R^k-linear forward and inverse return maps give T(M)≅M in
ModuleCat_W(E_R^k), E_R^k=R⊗_kRᵒᵖ. The target uses the combined given ground and endpoint
actions of M. -/
def rawReturnModuleIso :
    letI : Module (R ⊗[k] Rᵐᵒᵖ) M := TensorProduct.Algebra.module
    rawReturnObject k R S P Q M ≅ ModuleCat.of (R ⊗[k] Rᵐᵒᵖ) M := by
  letI : Module (R ⊗[k] Rᵐᵒᵖ) M := TensorProduct.Algebra.module
  let X := rawReturnObject k R S P Q M
  let Y := ModuleCat.of (R ⊗[k] Rᵐᵒᵖ) M
  refine
    { hom := @ModuleCat.ofHom (R ⊗[k] Rᵐᵒᵖ) _ X.carrier Y.carrier
        X.isAddCommGroup X.isModule Y.isAddCommGroup Y.isModule
        (rawReturnLinear k R S P Q M u hu)
      inv := @ModuleCat.ofHom (R ⊗[k] Rᵐᵒᵖ) _ Y.carrier X.carrier
        Y.isAddCommGroup Y.isModule X.isAddCommGroup X.isModule
        (rawReturnInverseLinear k R S P Q M u hu)
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (rawReturnIso k R S P Q M u hu).symm_apply_apply x
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (rawReturnIso k R S P Q M u hu).apply_symm_apply x

/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) bimodules in
independent carrier universes p,q. Both endpoint actions on each module commute and restrict to
its given k-action. Choose W=max(p,q,v), and let M be a k-module with carrier W and commuting
left and right R-actions compatible with k. Write T(M)=(P⊗_S((Q⊗_R M)⊗_R P))⊗_S Q and
Γ(p₀,q₀,m,p₁,q₁) for its five-factor class. The module-object point associated to p₀,q₀,m,p₁,q₁
is the class Γ in the underlying carrier of the raw return object. Both carriers lie in W. -/
def rawReturnModuleMk (p₀ : P) (q₀ : Q) (m : M) (p₁ : P) (q₁ : Q) :
    rawReturnObject k R S P Q M :=
  rawReturnMk k R S P Q M p₀ q₀ m p₁ q₁

/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) bimodules in
independent carrier universes p,q. Both endpoint actions on each module commute and restrict to
its given k-action. Choose W=max(p,q,v), and let M be a k-module with carrier W and commuting
left and right R-actions compatible with k. Write T(M)=(P⊗_S((Q⊗_R M)⊗_R P))⊗_S Q and
Γ(p₀,q₀,m,p₁,q₁) for its five-factor class. The five-factor point in the relative return module
object is heterogeneously equal to Γ(p₀,q₀,m,p₁,q₁) in the raw tensor carrier. This is the
carrier identification between the two presentations of T(M). -/
@[simp]
theorem rawReturnModuleMk_eq (p₀ : P) (q₀ : Q) (m : M) (p₁ : P) (q₁ : Q) :
    HEq (rawReturnModuleMk k R S P Q M p₀ q₀ m p₁ q₁)
      (rawReturnMk k R S P Q M p₀ q₀ m p₁ q₁) := HEq.rfl

include u hu in
/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) bimodules in
independent carrier universes p,q. Both endpoint actions on each module commute and restrict to
its given k-action. Choose W=max(p,q,v), and let M be a k-module with carrier W and commuting
left and right R-actions compatible with k. Write T(M)=(P⊗_S((Q⊗_R M)⊗_R P))⊗_S Q and
Γ(p₀,q₀,m,p₁,q₁) for its five-factor class. Let α:P⊗_S Q≃R be right R-linear and satisfy
α(r•b)=rα(b). Let H_α:T(M)→M be the coefficient function of the forward E_R^k-module
isomorphism. It is the return contraction on the module-object carrier, taking Γ to
α(p₀⊗q₀)•(op(α(p₁⊗q₁))•m). -/
def rawReturnModuleHom : rawReturnObject k R S P Q M → M := by
  letI : Module (R ⊗[k] Rᵐᵒᵖ) M := TensorProduct.Algebra.module
  let X : ModuleCat (R ⊗[k] Rᵐᵒᵖ) := rawReturnObject k R S P Q M
  let Y : ModuleCat (R ⊗[k] Rᵐᵒᵖ) := ModuleCat.of (R ⊗[k] Rᵐᵒᵖ) M
  let f : X →ₗ[R ⊗[k] Rᵐᵒᵖ] Y := @ModuleCat.Hom.hom (R ⊗[k] Rᵐᵒᵖ) _ X Y
    (show X ⟶ Y from (rawReturnModuleIso k R S P Q M u hu).hom)
  exact fun x => f x

/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) bimodules in
independent carrier universes p,q. Both endpoint actions on each module commute and restrict to
its given k-action. Choose W=max(p,q,v), and let M be a k-module with carrier W and commuting
left and right R-actions compatible with k. Write T(M)=(P⊗_S((Q⊗_R M)⊗_R P))⊗_S Q and
Γ(p₀,q₀,m,p₁,q₁) for its five-factor class. Let α:P⊗_S Q≃R be right R-linear and satisfy
α(r•b)=rα(b). For ξ in the return module-object carrier, H_α(ξ)=c_α(ξ) after identifying that
carrier with T(M). The source identification leaves the raw tensor coefficient unchanged. -/
@[simp]
theorem rawReturnModuleHom_apply (x : rawReturnObject k R S P Q M) :
    rawReturnModuleHom k R S P Q M u hu x =
      rawReturnIso k R S P Q M u hu
        (show rawReturnTensor k R S P Q M from x) := rfl

/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) bimodules in
independent carrier universes p,q. Both endpoint actions on each module commute and restrict to
its given k-action. Choose W=max(p,q,v), and let M be a k-module with carrier W and commuting
left and right R-actions compatible with k. Write T(M)=(P⊗_S((Q⊗_R M)⊗_R P))⊗_S Q and
Γ(p₀,q₀,m,p₁,q₁) for its five-factor class. Let α:P⊗_S Q≃R be right R-linear and satisfy
α(r•b)=rα(b). For every ξ∈T(M), the forward morphism of the E_R^k-module isomorphism has value
c_α(ξ)∈M. The statement applies to all tensor coefficients, in the same ground and endpoint
module structures. -/
@[simp]
theorem rawReturnModuleIso_hom_apply (x : rawReturnTensor k R S P Q M) :
    letI : Module (R ⊗[k] Rᵐᵒᵖ) M := TensorProduct.Algebra.module
    let X : ModuleCat (R ⊗[k] Rᵐᵒᵖ) := rawReturnObject k R S P Q M
    let Y : ModuleCat (R ⊗[k] Rᵐᵒᵖ) := ModuleCat.of (R ⊗[k] Rᵐᵒᵖ) M
    (@ModuleCat.Hom.hom (R ⊗[k] Rᵐᵒᵖ) _ X Y
      (show X ⟶ Y from (rawReturnModuleIso k R S P Q M u hu).hom)) x =
      rawReturnIso k R S P Q M u hu x := rfl

/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) bimodules in
independent carrier universes p,q. Both endpoint actions on each module commute and restrict to
its given k-action. Choose W=max(p,q,v), and let M be a k-module with carrier W and commuting
left and right R-actions compatible with k. Write T(M)=(P⊗_S((Q⊗_R M)⊗_R P))⊗_S Q and
Γ(p₀,q₀,m,p₁,q₁) for its five-factor class. Let α:P⊗_S Q≃R be right R-linear and satisfy
α(r•b)=rα(b). Define N_α:P→Q→M→P→Q→M by N_α(p₀,q₀,m,p₁,q₁)=H_α(Γ_obj(p₀,q₀,m,p₁,q₁)), where
Γ_obj is the five-factor point in the return module object. -/
def nativeReturnValue : P → Q → M → P → Q → M := by
  let F : rawReturnObject k R S P Q M → M := rawReturnModuleHom k R S P Q M u hu
  let η : P → Q → M → P → Q → rawReturnObject k R S P Q M :=
    rawReturnModuleMk k R S P Q M
  exact fun p₀ q₀ m p₁ q₁ => F (η p₀ q₀ m p₁ q₁)

/-- Let k be a commutative ring in u, R a k-algebra ring in r, S a ring in s, P a k-module in p with
a right S-action, and Q a k-module in q with commuting left S and right R-actions whose right
R-action is compatible with k. Let α:P⊗_S Q≃R be right R-linear. Let M be an abelian group with
left R and Rᵒᵖ-module actions at carrier height W=max(p,q,v). The five-argument function is
O_α(p₀,q₀,m,p₁,q₁)=α(p₀⊗q₀)•(op(α(p₁⊗q₁))•m). This expression uses the right scalar action
first, then the left. -/
def orderedReturnValue : P → Q → M → P → Q → M := by
  let l : R → M → M := (inferInstance : Module R M).smul
  let r : Rᵐᵒᵖ → M → M := (inferInstance : Module Rᵐᵒᵖ M).smul
  let c : P → Q → R := contractionScalar k R S P Q u
  exact fun p₀ q₀ m p₁ q₁ => l (c p₀ q₀) (r (op (c p₁ q₁)) m)

/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) bimodules in
independent carrier universes p,q. Both endpoint actions on each module commute and restrict to
its given k-action. Choose W=max(p,q,v), and let M be a k-module with carrier W and commuting
left and right R-actions compatible with k. Write T(M)=(P⊗_S((Q⊗_R M)⊗_R P))⊗_S Q and
Γ(p₀,q₀,m,p₁,q₁) for its five-factor class. Let α:P⊗_S Q≃R be right R-linear and satisfy
α(r•b)=rα(b). Define V_α:P→Q→M→P→Q→M by V_α(p₀,q₀,m,p₁,q₁)=c_α(Γ(p₀,q₀,m,p₁,q₁)). Its target is
the same middle coefficient module M. -/
def rawReturnValue : P → Q → M → P → Q → M := by
  let G : rawReturnTensor k R S P Q M → M := (rawReturnIso k R S P Q M u hu).toFun
  let ζ : P → Q → M → P → Q → rawReturnTensor k R S P Q M :=
    rawReturnMk k R S P Q M
  exact fun p₀ q₀ m p₁ q₁ => G (ζ p₀ q₀ m p₁ q₁)

/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) bimodules in
independent carrier universes p,q. Both endpoint actions on each module commute and restrict to
its given k-action. Choose W=max(p,q,v), and let M be a k-module with carrier W and commuting
left and right R-actions compatible with k. Write T(M)=(P⊗_S((Q⊗_R M)⊗_R P))⊗_S Q and
Γ(p₀,q₀,m,p₁,q₁) for its five-factor class. Let α:P⊗_S Q≃R be right R-linear and satisfy
α(r•b)=rα(b). The entire five-argument function V_α equals O_α, where V_α evaluates c_α on Γ and
O_α(p₀,q₀,m,p₁,q₁)=α(p₀⊗q₀)•(op(α(p₁⊗q₁))•m). -/
theorem rawReturnValue_eq :
    rawReturnValue k R S P Q M u hu = orderedReturnValue k R S P Q M u := by
  funext p₀ q₀ m p₁ q₁
  exact rawReturnIso_mk k R S P Q M u hu p₀ q₀ m p₁ q₁

/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) bimodules in
independent carrier universes p,q. Both endpoint actions on each module commute and restrict to
its given k-action. Choose W=max(p,q,v), and let M be a k-module with carrier W and commuting
left and right R-actions compatible with k. Write T(M)=(P⊗_S((Q⊗_R M)⊗_R P))⊗_S Q and
Γ(p₀,q₀,m,p₁,q₁) for its five-factor class. Let α:P⊗_S Q≃R be right R-linear and satisfy
α(r•b)=rα(b). The underlying coefficient function H_α of the return module morphism is
heterogeneously equal to c_α.toFun. Their source presentations are the module-object carrier and
raw T(M), identified by the same tensor coefficients. -/
theorem rawReturnModuleHom_heq :
    HEq (rawReturnModuleHom k R S P Q M u hu)
      (rawReturnIso k R S P Q M u hu).toFun := HEq.rfl

/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) bimodules in
independent carrier universes p,q. Both endpoint actions on each module commute and restrict to
its given k-action. Choose W=max(p,q,v), and let M be a k-module with carrier W and commuting
left and right R-actions compatible with k. Write T(M)=(P⊗_S((Q⊗_R M)⊗_R P))⊗_S Q and
Γ(p₀,q₀,m,p₁,q₁) for its five-factor class. Let α:P⊗_S Q≃R be right R-linear and satisfy
α(r•b)=rα(b). As five-argument functions P→Q→M→P→Q→M, N_α=V_α. The module-object point and raw
point represent the same Γ, and the module-object return map has the raw equivalence function. -/
theorem nativeReturnValue_eq_raw :
    nativeReturnValue k R S P Q M u hu = rawReturnValue k R S P Q M u hu := by
  have hApp {A B : Type (max p q v)} {f : A → M} {g : B → M}
      {x : A} {y : B} (hf : HEq f g) (hx : HEq x y) : f x = g y := by
    cases hx
    exact congrFun (eq_of_heq hf) x
  funext p₀ q₀ m p₁ q₁
  exact @hApp (rawReturnObject k R S P Q M) (rawReturnTensor k R S P Q M)
    (rawReturnModuleHom k R S P Q M u hu) (rawReturnIso k R S P Q M u hu).toFun
    (rawReturnModuleMk k R S P Q M p₀ q₀ m p₁ q₁)
    (rawReturnMk k R S P Q M p₀ q₀ m p₁ q₁)
    (rawReturnModuleHom_heq k R S P Q M u hu)
    (rawReturnModuleMk_eq k R S P Q M p₀ q₀ m p₁ q₁)

/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) bimodules in
independent carrier universes p,q. Both endpoint actions on each module commute and restrict to
its given k-action. Choose W=max(p,q,v), and let M be a k-module with carrier W and commuting
left and right R-actions compatible with k. Write T(M)=(P⊗_S((Q⊗_R M)⊗_R P))⊗_S Q and
Γ(p₀,q₀,m,p₁,q₁) for its five-factor class. Let α:P⊗_S Q≃R be right R-linear and satisfy
α(r•b)=rα(b). As five-argument functions, N_α=O_α. Thus its value on p₀,q₀,m,p₁,q₁ is
α(p₀⊗q₀)•(op(α(p₁⊗q₁))•m), with all chosen ground and endpoint actions retained. -/
theorem nativeReturnValue_eq :
    nativeReturnValue k R S P Q M u hu = orderedReturnValue k R S P Q M u :=
  (nativeReturnValue_eq_raw k R S P Q M u hu).trans
    (rawReturnValue_eq k R S P Q M u hu)

/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) bimodules in
independent carrier universes p,q. Both endpoint actions on each module commute and restrict to
its given k-action. Choose W=max(p,q,v), and let M be a k-module with carrier W and commuting
left and right R-actions compatible with k. Write T(M)=(P⊗_S((Q⊗_R M)⊗_R P))⊗_S Q and
Γ(p₀,q₀,m,p₁,q₁) for its five-factor class. Let α:P⊗_S Q≃R be right R-linear and satisfy
α(r•b)=rα(b). For any p₀,q₀,m,p₁,q₁, N_α(p₀,q₀,m,p₁,q₁)=H_α(Γ_obj(p₀,q₀,m,p₁,q₁)). Both source
and target use their module-object coefficient carriers in W. -/
theorem nativeReturnValue_apply (p₀ : P) (q₀ : Q) (m : M) (p₁ : P) (q₁ : Q) :
    nativeReturnValue k R S P Q M u hu p₀ q₀ m p₁ q₁ =
      rawReturnModuleHom k R S P Q M u hu
        (rawReturnModuleMk k R S P Q M p₀ q₀ m p₁ q₁) := rfl
omit [SMulCommClass R Sᵐᵒᵖ P] [IsScalarTower k R P] [IsScalarTower k Sᵐᵒᵖ P]
  [IsScalarTower k S Q] [SMulCommClass R Rᵐᵒᵖ M] [IsScalarTower k R M]
  [IsScalarTower k Rᵐᵒᵖ M] [Algebra k S] [Module R P] [Module k M] in
/-- Let k be a commutative ring in u, R a k-algebra ring in r, S a ring in s, P a k-module in p with
a right S-action, and Q a k-module in q with commuting left S and right R-actions whose right
R-action is compatible with k. Let α:P⊗_S Q≃R be right R-linear. For an abelian group M with
left R and Rᵒᵖ-actions at height W=max(p,q,v), O_α(p₀,q₀,m,p₁,q₁)=α(p₀⊗_S q₀)•(op(α(p₁⊗_S
q₁))•m). The formula evaluates the right scalar action before the left scalar action. -/
theorem orderedReturnValue_apply (p₀ : P) (q₀ : Q) (m : M) (p₁ : P) (q₁ : Q) :
    orderedReturnValue k R S P Q M u p₀ q₀ m p₁ q₁ =
      u (TensorProduct.Balanced.mk k S P Q p₀ q₀) •
        (op (u (TensorProduct.Balanced.mk k S P Q p₁ q₁)) • m) := rfl

/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) bimodules in
independent carrier universes p,q. Both endpoint actions on each module commute and restrict to
its given k-action. Choose W=max(p,q,v), and let M be a k-module with carrier W and commuting
left and right R-actions compatible with k. Write T(M)=(P⊗_S((Q⊗_R M)⊗_R P))⊗_S Q and
Γ(p₀,q₀,m,p₁,q₁) for its five-factor class. Let α:P⊗_S Q≃R be right R-linear and satisfy
α(r•b)=rα(b). On the five-factor point, the module isomorphism value N_α equals O_α: it sends
Γ_obj(p₀,q₀,m,p₁,q₁) to α(p₀⊗q₀)•(op(α(p₁⊗q₁))•m). The equality is in the given middle module M. -/
@[simp]
theorem rawReturnModuleIso_hom_mk (p₀ : P) (q₀ : Q) (m : M) (p₁ : P) (q₁ : Q) :
    nativeReturnValue k R S P Q M u hu p₀ q₀ m p₁ q₁ =
      orderedReturnValue k R S P Q M u p₀ q₀ m p₁ q₁ :=
  congrFun (congrFun (congrFun (congrFun (congrFun
    (nativeReturnValue_eq k R S P Q M u hu) p₀) q₀) m) p₁) q₁

end Native

end ModuleCat.Bimodule.Over.Morita
