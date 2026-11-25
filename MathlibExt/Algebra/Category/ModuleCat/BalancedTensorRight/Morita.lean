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

public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.Algebra.Module.Equiv.Basic
public import MathlibExt.Algebra.Module.NatInt
public import MathlibExt.Algebra.Category.ModuleCat.BalancedTensorRight
public import MathlibExt.LinearAlgebra.TensorProduct.Balanced.Associator
public import MathlibExt.LinearAlgebra.TensorProduct.Balanced.Unitors
public import MathlibExt.LinearAlgebra.TensorProduct.Balanced.Contraction

/-!
# Module equivalences from invertible bimodule contractions

The comparison maps are the balanced tensor associator followed by a
bimodule contraction and a unitor. The scalar rings may be noncommutative
and have independent universes; the coefficient carriers and module
categories use the common carrier universe `v`.

The contractions are bimodule isomorphisms. Adjointification constructs
the triangle identity while retaining the tensor functors and specified
counit.
-/

@[expose] public section

noncomputable section

open CategoryTheory MulOpposite
open TensorProduct.Balanced

universe r s v

namespace ModuleCat.BalancedTensorRight

section Contraction

variable (R : Type r) [Ring R]
  (B : Type v) [AddCommGroup B] [Module R B] [Module Rᵐᵒᵖ B]
  [SMulCommClass R Rᵐᵒᵖ B]

section GivenIntegerAction

variable [givenIntegerModule : Module ℤ B]
  (e : B ≃ₗ[Rᵐᵒᵖ] R)
  (he : ∀ (r : R) (b : B), e (r • b) = r * e b)

include e he in
/-- Contract the original quotient, retaining its given integer action. -/
def contractionLinearRaw (A : ModuleCat.{v} Rᵐᵒᵖ) :
    letI := Module.intModule_smulCommClass (S := Rᵐᵒᵖ) (M := B) (dM := givenIntegerModule)
    letI := rightModule ℤ R R A B
    TensorProduct.Balanced ℤ R A B ≃ₗ[Rᵐᵒᵖ] A := by
  let integerA : Module ℤ A := inferInstance
  letI := Module.intModule_smulCommClass (S := Rᵐᵒᵖ) (M := A) (dM := integerA)
  letI := Module.intModule_smulCommClass (S := Rᵐᵒᵖ) (M := B) (dM := givenIntegerModule)
  letI := rightModule ℤ R R A B
  let ringInteger : Module ℤ R := Algebra.toModule
  let eZ := e.toAddEquiv.toIntLinearEquiv
    (modM := givenIntegerModule) (modM₂ := ringInteger)
  have heZ : ∀ (r : R) (b : B), eZ (r • b) = r * eZ b := by
    intro r b
    exact he r b
  let E : TensorProduct.Balanced ℤ R A B ≃ₗ[ℤ] A :=
    rightContraction R A B eZ heZ
  apply E.toAddEquiv.toLinearEquiv
  intro t x
  have h : E.toLinearMap.toAddMonoidHom.comp (rightAction ℤ R R A B t).toAddMonoidHom =
      (DistribSMul.toAddMonoidHom A t).comp E.toLinearMap.toAddMonoidHom := by
    apply TensorProduct.Balanced.addHom_ext ℤ R A B
    intro a b
    change E (rightAction ℤ R R A B t (mk ℤ R A B a b)) =
      t • E (mk ℤ R A B a b)
    rw [rightAction_mk]
    change rightContraction R A B eZ heZ (mk ℤ R A B a (t • b)) =
      t • rightContraction R A B eZ heZ (mk ℤ R A B a b)
    rw [rightContraction_mk, rightContraction_mk]
    change op (e (t • b)) • a = t • (op (e b) • a)
    rw [e.map_smul]
    change op (e b * t.unop) • a = t • (op (e b) • a)
    rw [op_mul, op_unop, mul_smul]
  change E (rightAction ℤ R R A B t x) = t • E x
  exact DFunLike.congr_fun h x

/-- The contraction has the original right-action value on pure classes. -/
@[simp, nolint simpNF] -- stated with Balanced.mk for rw; Balanced.mk_apply simplifies LHS
theorem contractionLinearRaw_mk (A : ModuleCat.{v} Rᵐᵒᵖ) (a : A) (b : B) :
    letI := Module.intModule_smulCommClass (S := Rᵐᵒᵖ) (M := B) (dM := givenIntegerModule)
    letI := rightModule ℤ R R A B
    contractionLinearRaw R B e he A (mk ℤ R A B a b) = op (e b) • a := by
  let integerA : Module ℤ A := inferInstance
  let := Module.intModule_smulCommClass (S := Rᵐᵒᵖ) (M := A) (dM := integerA)
  let := Module.intModule_smulCommClass (S := Rᵐᵒᵖ) (M := B) (dM := givenIntegerModule)
  let := rightModule ℤ R R A B
  let ringInteger : Module ℤ R := Algebra.toModule
  let eZ := e.toAddEquiv.toIntLinearEquiv
    (modM := givenIntegerModule) (modM₂ := ringInteger)
  have heZ : ∀ (r : R) (b : B), eZ (r • b) = r * eZ b := by
    intro r b
    exact he r b
  change rightContraction R A B eZ heZ (mk ℤ R A B a b) = op (e b) • a
  exact rightContraction_mk R A B eZ heZ a b

end GivenIntegerAction

variable (e : B ≃ₗ[Rᵐᵒᵖ] R)
  (he : ∀ (r : R) (b : B), e (r • b) = r * e b)

include e he in
/-- Contract the actual tensor-functor object, with its canonical integer action. -/
def contractionLinear (A : ModuleCat.{v} Rᵐᵒᵖ) :
    tensorObj R R B A ≃ₗ[Rᵐᵒᵖ] A :=
  contractionLinearRaw R B e he A

@[simp, nolint simpNF] -- stated with Balanced.mk for rw; Balanced.mk_apply simplifies LHS
theorem contractionLinear_mk (A : ModuleCat.{v} Rᵐᵒᵖ) (a : A) (b : B) :
    contractionLinear R B e he A (mk ℤ R A B a b) = op (e b) • a :=
  contractionLinearRaw_mk R B e he A a b

include e he in
/-- The actual component iso does not require the regular ring object to
live in the module carrier universe. -/
def contractionIso (A : ModuleCat.{v} Rᵐᵒᵖ) : tensorObj R R B A ≅ A :=
  (contractionLinear R B e he A).toModuleIso

@[simp, nolint simpNF] -- stated with Balanced.mk for rw; Balanced.mk_apply simplifies LHS
theorem contractionIso_hom_mk (A : ModuleCat.{v} Rᵐᵒᵖ) (a : A) (b : B) :
    (contractionIso R B e he A).hom.hom (mk ℤ R A B a b) = op (e b) • a :=
  contractionLinear_mk R B e he A a b

include e he in
/-- Bimodule contraction is natural in the original right-module variable. -/
def contractionNatIso : tensorFunctor R R B ≅ 𝟭 (ModuleCat.{v} Rᵐᵒᵖ) :=
  NatIso.ofComponents (contractionIso R B e he) (by
    intro A A' f
    apply ModuleCat.hom_ext
    apply LinearMap.toAddMonoidHom_injective
    apply TensorProduct.Balanced.addHom_ext ℤ R A B
    intro a b
    change (contractionIso R B e he A').hom.hom
        ((tensorMap R R B f).hom (mk ℤ R A B a b)) =
      f.hom ((contractionIso R B e he A).hom.hom (mk ℤ R A B a b))
    rw [tensorMap_mk, contractionIso_hom_mk, contractionIso_hom_mk]
    exact (f.hom.map_smul (op (e b)) a).symm)

end Contraction

section Composite

variable (R : Type r) (S : Type s) [Ring R] [Ring S]
  (P Q : Type v) [AddCommGroup P] [AddCommGroup Q]
  [Module R P] [Module Sᵐᵒᵖ P] [SMulCommClass R Sᵐᵒᵖ P]
  [Module S Q] [Module Rᵐᵒᵖ Q] [SMulCommClass S Rᵐᵒᵖ Q]

/-- The pure triple class in the actual composite tensor functor. The
integer action on its bundled inner factor is the native canonical action. -/
def compositeMk (A : ModuleCat.{v} Rᵐᵒᵖ) (a : A) (p : P) (q : Q) :
    ((tensorFunctor R S P) ⋙ (tensorFunctor S R Q)).obj A := by
  let X := tensorObj R S P A
  letI : Module ℤ X := AddCommGroup.toIntModule X
  exact mk ℤ S X Q (mk ℤ R A P a p) q

/-- Bundle the original left parentheses with their computed right action. -/
def assocSourceObj (A : ModuleCat.{v} Rᵐᵒᵖ) : ModuleCat.{v} Rᵐᵒᵖ :=
  letI := rightModule ℤ R S A P
  letI := rightModule ℤ S R (TensorProduct.Balanced ℤ R A P) Q
  ModuleCat.of Rᵐᵒᵖ (assocSource ℤ R S A P Q)

/-- Bundle the original right parentheses with the twice-computed action. -/
def assocTargetObj (A : ModuleCat.{v} Rᵐᵒᵖ) : ModuleCat.{v} Rᵐᵒᵖ :=
  letI := leftModule ℤ S R P Q
  letI := rightModule ℤ S R P Q
  letI := leftRightSMulCommClass ℤ S R P Q R
  letI := rightModule ℤ R R A (TensorProduct.Balanced ℤ S P Q)
  ModuleCat.of Rᵐᵒᵖ (assocTarget ℤ R S A P Q)

/-- Native uniqueness of the integer action identifies the bundled
composite with the original associator source, without changing its factors. -/
def compositeCoordinates (A : ModuleCat.{v} Rᵐᵒᵖ) :
    ((tensorFunctor R S P) ⋙ (tensorFunctor S R Q)).obj A ≅
      assocSourceObj R S P Q A := by
  let X := TensorProduct.Balanced ℤ R A P
  let d : Module ℤ X := inferInstance
  let d₀ : Module ℤ X := AddCommGroup.toIntModule X
  let m : Module Sᵐᵒᵖ X := rightModule ℤ R S A P
  let K : Module ℤ X → ModuleCat.{v} Rᵐᵒᵖ := fun d' =>
    letI := d'
    letI := m
    letI := rightModule ℤ S R X Q
    ModuleCat.of Rᵐᵒᵖ (TensorProduct.Balanced ℤ S X Q)
  exact eqToIso (congrArg K (Subsingleton.elim d₀ d))

/-- The earned dictionary comparison preserves each literal triple class. -/
@[simp, nolint simpNF] -- composite-functor form for rw; Functor.comp_obj simplifies LHS
theorem compositeCoordinates_mk (A : ModuleCat.{v} Rᵐᵒᵖ)
    (a : A) (p : P) (q : Q) :
    letI := rightModule ℤ R S A P
    (compositeCoordinates R S P Q A).hom.hom (compositeMk R S P Q A a p q) =
      mk ℤ S (TensorProduct.Balanced ℤ R A P) Q (mk ℤ R A P a p) q := by
  let X := TensorProduct.Balanced ℤ R A P
  let d : Module ℤ X := inferInstance
  let d₀ : Module ℤ X := AddCommGroup.toIntModule X
  let m : Module Sᵐᵒᵖ X := rightModule ℤ R S A P
  let K : Module ℤ X → ModuleCat.{v} Rᵐᵒᵖ := fun d' =>
    letI := d'
    letI := m
    letI := rightModule ℤ S R X Q
    ModuleCat.of Rᵐᵒᵖ (TensorProduct.Balanced ℤ S X Q)
  let z : ∀ d' : Module ℤ X, K d' := fun d' =>
    letI := d'
    letI := m
    mk ℤ S X Q (mk ℤ R A P a p) q
  have hz (d₁ d₂ : Module ℤ X) (h : d₁ = d₂) :
      (eqToIso (congrArg K h)).hom.hom (z d₁) = z d₂ := by
    cases h
    rfl
  exact hz d₀ d (Subsingleton.elim d₀ d)

/-- The given raw associator is right-linear for the actual outer actions. -/
def associationLinear (A : ModuleCat.{v} Rᵐᵒᵖ) :
    assocSourceObj R S P Q A ≃ₗ[Rᵐᵒᵖ] assocTargetObj R S P Q A := by
  letI := rightModule ℤ R S A P
  letI := leftModule ℤ S R P Q
  letI := rightModule ℤ S R P Q
  letI := rightSMulCommClass ℤ S R P Q
  letI := leftRightSMulCommClass ℤ S R P Q R
  letI := rightModule ℤ S R (TensorProduct.Balanced ℤ R A P) Q
  letI := rightModule ℤ R R A (TensorProduct.Balanced ℤ S P Q)
  exact (assoc ℤ R S A P Q).toAddEquiv.toLinearEquiv
    (fun t x => assoc_right_smul ℤ R S A P Q R t x)

@[simp, nolint simpNF] -- stated with Balanced.mk for rw; Balanced.mk_apply simplifies LHS
theorem associationLinear_mk_mk (A : ModuleCat.{v} Rᵐᵒᵖ)
    (a : A) (p : P) (q : Q) :
    letI := rightModule ℤ R S A P
    letI := leftModule ℤ S R P Q
    associationLinear R S P Q A
        (mk ℤ S (TensorProduct.Balanced ℤ R A P) Q (mk ℤ R A P a p) q) =
      mk ℤ R A (TensorProduct.Balanced ℤ S P Q) a (mk ℤ S P Q p q) := by
  let := rightModule ℤ R S A P
  let := leftModule ℤ S R P Q
  exact assoc_mk_mk ℤ R S A P Q a p q

/-- Reassociation on the actual bundled composite tensor object. -/
def compositeAssociationIso (A : ModuleCat.{v} Rᵐᵒᵖ) :
    ((tensorFunctor R S P) ⋙ (tensorFunctor S R Q)).obj A ≅
      assocTargetObj R S P Q A :=
  (compositeCoordinates R S P Q A).trans
    (associationLinear R S P Q A).toModuleIso

@[simp, nolint simpNF] -- composite-functor form for rw; Functor.comp_obj simplifies LHS
theorem compositeAssociationIso_mk (A : ModuleCat.{v} Rᵐᵒᵖ)
    (a : A) (p : P) (q : Q) :
    letI := leftModule ℤ S R P Q
    (compositeAssociationIso R S P Q A).hom.hom
        (compositeMk R S P Q A a p q) =
      mk ℤ R A (TensorProduct.Balanced ℤ S P Q) a (mk ℤ S P Q p q) := by
  let := rightModule ℤ R S A P
  let := leftModule ℤ S R P Q
  change associationLinear R S P Q A
    ((compositeCoordinates R S P Q A).hom.hom
      (compositeMk R S P Q A a p q)) = _
  rw [compositeCoordinates_mk, associationLinear_mk_mk]

variable
  (u : letI := leftModule ℤ S R P Q
    letI := rightModule ℤ S R P Q
    TensorProduct.Balanced ℤ S P Q ≃ₗ[Rᵐᵒᵖ] R)
  (hu : letI := leftModule ℤ S R P Q
    letI := rightModule ℤ S R P Q
    ∀ (r : R) (x : TensorProduct.Balanced ℤ S P Q), u (r • x) = r * u x)

include u hu in
/-- Contract the reassociated pair using the given bimodule isomorphism. -/
def compositeContractionIso (A : ModuleCat.{v} Rᵐᵒᵖ) :
    ((tensorFunctor R S P) ⋙ (tensorFunctor S R Q)).obj A ≅ A := by
  letI := leftModule ℤ S R P Q
  letI := rightModule ℤ S R P Q
  letI := rightSMulCommClass ℤ S R P Q
  letI := leftRightSMulCommClass ℤ S R P Q R
  exact (compositeAssociationIso R S P Q A).trans
    (contractionLinearRaw R (TensorProduct.Balanced ℤ S P Q) u hu A).toModuleIso

/-- The return map has the literal pairing value on the original ordered factors. -/
@[simp, nolint simpNF] -- composite-functor form for rw; Functor.comp_obj simplifies LHS
theorem compositeContractionIso_mk (A : ModuleCat.{v} Rᵐᵒᵖ)
    (a : A) (p : P) (q : Q) :
    (compositeContractionIso R S P Q u hu A).hom.hom
        (compositeMk R S P Q A a p q) = op (u (mk ℤ S P Q p q)) • a := by
  let := leftModule ℤ S R P Q
  let := rightModule ℤ S R P Q
  let := rightSMulCommClass ℤ S R P Q
  let := leftRightSMulCommClass ℤ S R P Q R
  change contractionLinearRaw R (TensorProduct.Balanced ℤ S P Q) u hu A
    ((compositeAssociationIso R S P Q A).hom.hom
      (compositeMk R S P Q A a p q)) = _
  rw [compositeAssociationIso_mk, contractionLinearRaw_mk]

include u hu in
/-- The actual bimodule contraction is natural in the right-module variable. -/
def compositeContractionNatIso :
    (tensorFunctor R S P) ⋙ (tensorFunctor S R Q) ≅
      𝟭 (ModuleCat.{v} Rᵐᵒᵖ) :=
  NatIso.ofComponents (compositeContractionIso R S P Q u hu) (by
    intro A A' f
    apply ModuleCat.hom_ext
    apply LinearMap.toAddMonoidHom_injective
    let X := tensorObj R S P A
    let : Module ℤ X := AddCommGroup.toIntModule X
    apply TensorProduct.Balanced.addHom_ext ℤ S X Q
    intro x q
    let L : X →+ A' :=
      ((compositeContractionIso R S P Q u hu A').hom.hom.toAddMonoidHom.comp
        (((tensorFunctor R S P) ⋙ (tensorFunctor S R Q)).map f).hom.toAddMonoidHom).comp
          (((mk ℤ S X Q).flip q).toAddMonoidHom)
    let T : X →+ A' :=
      (f.hom.toAddMonoidHom.comp
        (compositeContractionIso R S P Q u hu A).hom.hom.toAddMonoidHom).comp
          (((mk ℤ S X Q).flip q).toAddMonoidHom)
    have h : L = T := by
      apply TensorProduct.Balanced.addHom_ext ℤ R A P
      intro a p
      change (compositeContractionIso R S P Q u hu A').hom.hom
          ((tensorMap S R Q (tensorMap R S P f)).hom
            (compositeMk R S P Q A a p q)) =
        f.hom ((compositeContractionIso R S P Q u hu A).hom.hom
          (compositeMk R S P Q A a p q))
      have hf : (tensorMap S R Q (tensorMap R S P f)).hom
          (compositeMk R S P Q A a p q) = compositeMk R S P Q A' (f.hom a) p q := by
        let X' := tensorObj R S P A'
        let : Module ℤ X' := AddCommGroup.toIntModule X'
        let a₀ : X := mk ℤ R A P a p
        let a₁ : X' := mk ℤ R A' P (f.hom a) p
        have houter : (tensorMap S R Q (tensorMap R S P f)).hom
            (mk ℤ S X Q a₀ q) =
            mk ℤ S X' Q ((tensorMap R S P f).hom a₀) q :=
          tensorMap_mk (R := S) (S := R) (B := Q) (A := X) (A' := X')
            (tensorMap R S P f) a₀ q
        have hinner : (tensorMap R S P f).hom a₀ = a₁ :=
          tensorMap_mk (R := R) (S := S) (B := P) (A := A) (A' := A') f a p
        change (tensorMap S R Q (tensorMap R S P f)).hom
          (mk ℤ S X Q a₀ q) = mk ℤ S X' Q a₁ q
        exact houter.trans (congrArg (fun y : X' => mk ℤ S X' Q y q) hinner)
      rw [hf, compositeContractionIso_mk, compositeContractionIso_mk]
      exact (f.hom.map_smul (op (u (mk ℤ S P Q p q))) a).symm
    exact DFunLike.congr_fun h x)

end Composite

section Equivalence

variable (R : Type r) (S : Type s) [Ring R] [Ring S]
  (P Q : Type v) [AddCommGroup P] [AddCommGroup Q]
  [Module R P] [Module Sᵐᵒᵖ P] [SMulCommClass R Sᵐᵒᵖ P]
  [Module S Q] [Module Rᵐᵒᵖ Q] [SMulCommClass S Rᵐᵒᵖ Q]
  (u : letI := leftModule ℤ S R P Q
    letI := rightModule ℤ S R P Q
    TensorProduct.Balanced ℤ S P Q ≃ₗ[Rᵐᵒᵖ] R)
  (hu : letI := leftModule ℤ S R P Q
    letI := rightModule ℤ S R P Q
    ∀ (r : R) (x : TensorProduct.Balanced ℤ S P Q), u (r • x) = r * u x)
  (w : letI := leftModule ℤ R S Q P
    letI := rightModule ℤ R S Q P
    TensorProduct.Balanced ℤ R Q P ≃ₗ[Sᵐᵒᵖ] S)
  (hw : letI := leftModule ℤ R S Q P
    letI := rightModule ℤ R S Q P
    ∀ (s : S) (x : TensorProduct.Balanced ℤ R Q P), w (s • x) = s * w x)

include u hu w hw in
/-- The actual right-module equivalence from the two invertible bimodule
contractions. Its triangle is earned by native adjointification. -/
def equivalence : ModuleCat.{v} Rᵐᵒᵖ ≌ ModuleCat.{v} Sᵐᵒᵖ :=
  CategoryTheory.Equivalence.mk (tensorFunctor R S P) (tensorFunctor S R Q)
    (compositeContractionNatIso R S P Q u hu).symm
    (compositeContractionNatIso S R Q P w hw)

@[simp]
theorem equivalence_functor : (equivalence R S P Q u hu w hw).functor =
    tensorFunctor R S P := rfl

@[simp]
theorem equivalence_inverse : (equivalence R S P Q u hu w hw).inverse =
    tensorFunctor S R Q := rfl

/-- Native adjointification keeps the earned counit unchanged. -/
theorem equivalence_counitIso : (equivalence R S P Q u hu w hw).counitIso =
    compositeContractionNatIso S R Q P w hw := rfl

/-- The chosen unit is the actual native refinement of the input contraction. -/
theorem equivalence_unitIso : (equivalence R S P Q u hu w hw).unitIso =
    Equivalence.adjointifyη (compositeContractionNatIso R S P Q u hu).symm
      (compositeContractionNatIso S R Q P w hw) := rfl

/-- The unchanged counit has the book's ordered contraction formula. -/
@[simp, nolint simpNF] -- stated with the equivalence for rw; equivalence_functor simplifies LHS
theorem equivalence_counitIso_mk (A : ModuleCat.{v} Sᵐᵒᵖ)
    (a : A) (q : Q) (p : P) :
    ((equivalence R S P Q u hu w hw).counitIso.hom.app A).hom
        (compositeMk S R Q P A a q p) = op (w (mk ℤ R Q P q p)) • a :=
  compositeContractionIso_mk S R Q P w hw A a q p

end Equivalence

end ModuleCat.BalancedTensorRight
