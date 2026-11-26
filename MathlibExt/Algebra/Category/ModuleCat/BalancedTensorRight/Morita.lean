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
# Morita return maps for right-module tensor functors

Let `R` and `S` be associative rings with independent universes. Let `P` be an `R`-left,
`S`-right bimodule and `Q` an `S`-left, `R`-right bimodule, with coefficient and module
carriers in universe `v`. The tensor functors `- ⊗_R P` and `- ⊗_S Q` act between the right
module categories.

The balanced associator identifies `(A ⊗_R P) ⊗_S Q` with `A ⊗_R (P ⊗_S Q)`. A bimodule
equivalence `u : P ⊗_S Q ≅ R` contracts the latter to `A`, with `[[a ⊗ p] ⊗ q] ↦ op (u([p ⊗
q])) • a`. More generally, a bimodule equivalent to the regular `R`-bimodule gives a tensor
unitor, including for a given integer-module structure on its carrier.

A second bimodule equivalence `Q ⊗_R P ≅ S` supplies the other return isomorphism. They define
a categorical equivalence of right-module categories whose counit is the specified `S`-return
map and whose unit is adjointified from the inverse `R`-return map.
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
/-- Right-module contraction with a given integer coefficient action.

Let `B` be an `R`-bimodule with a given integer-module structure and a right-linear
equivalence `e : B ≃ₗ[Rᵐᵒᵖ] R` preserving the left `R`-action. For each right module `A`,
contraction gives `Balanced ℤ R A B ≃ₗ[Rᵐᵒᵖ] A`. -/
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

/-- Raw right-module contraction on pure classes.

With the given integer-module coefficient action, the contraction associated to `e` sends `[a
⊗ b]` to `op (e b) • a`. -/
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
/-- Right-module contraction in the tensor-object coordinates.

For an `R`-bimodule equivalent to the regular bimodule, contraction gives a right `R`-linear
equivalence from `tensorObj R R B A` to `A`. -/
def contractionLinear (A : ModuleCat.{v} Rᵐᵒᵖ) :
    tensorObj R R B A ≃ₗ[Rᵐᵒᵖ] A :=
  contractionLinearRaw R B e he A

/-- Tensor-object right-module contraction on pure classes.

The contraction equivalence in the tensor-object coordinates satisfies `[a ⊗ b] ↦ op (e b) •
a`. -/
@[simp, nolint simpNF] -- stated with Balanced.mk for rw; Balanced.mk_apply simplifies LHS
theorem contractionLinear_mk (A : ModuleCat.{v} Rᵐᵒᵖ) (a : A) (b : B) :
    contractionLinear R B e he A (mk ℤ R A B a b) = op (e b) • a :=
  contractionLinearRaw_mk R B e he A a b

include e he in
/-- Categorical right-module contraction isomorphism.

Bundle the right-linear contraction from `A ⊗_R B` to `A` as an isomorphism in `ModuleCat
Rᵐᵒᵖ`, using a bimodule equivalence `B ≅ R`. -/
def contractionIso (A : ModuleCat.{v} Rᵐᵒᵖ) : tensorObj R R B A ≅ A :=
  (contractionLinear R B e he A).toModuleIso

/-- Categorical right-module contraction on pure classes.

The forward categorical contraction map sends the balanced class `[a ⊗ b]` to `op (e b) • a`. -/
@[simp, nolint simpNF] -- stated with Balanced.mk for rw; Balanced.mk_apply simplifies LHS
theorem contractionIso_hom_mk (A : ModuleCat.{v} Rᵐᵒᵖ) (a : A) (b : B) :
    (contractionIso R B e he A).hom.hom (mk ℤ R A B a b) = op (e b) • a :=
  contractionLinear_mk R B e he A a b

include e he in
/-- Regular-equivalent coefficient tensor is naturally the right-module identity.

A bimodule equivalence `B ≅ R` gives a natural isomorphism `tensorFunctor R R B ≅ 𝟭 (ModuleCat
Rᵐᵒᵖ)` through its contraction maps. -/
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

/-- Pure triple in the right-module return composite.

For `a : A`, `p : P`, and `q : Q`, this element is `[[a ⊗ p] ⊗ q]` in the composite that
tensors first by `P` and then by `Q`. -/
def compositeMk (A : ModuleCat.{v} Rᵐᵒᵖ) (a : A) (p : P) (q : Q) :
    ((tensorFunctor R S P) ⋙ (tensorFunctor S R Q)).obj A := by
  let X := tensorObj R S P A
  letI : Module ℤ X := AddCommGroup.toIntModule X
  exact mk ℤ S X Q (mk ℤ R A P a p) q

/-- Left-associated right-module return tensor object.

Bundle `(A ⊗_R P) ⊗_S Q` as a right `R`-module, with the outer right action induced from `Q`. -/
def assocSourceObj (A : ModuleCat.{v} Rᵐᵒᵖ) : ModuleCat.{v} Rᵐᵒᵖ :=
  letI := rightModule ℤ R S A P
  letI := rightModule ℤ S R (TensorProduct.Balanced ℤ R A P) Q
  ModuleCat.of Rᵐᵒᵖ (assocSource ℤ R S A P Q)

/-- Right-associated right-module return tensor object.

Bundle `A ⊗_R (P ⊗_S Q)` as a right `R`-module, using the induced left and right `R`-actions
on the composite coefficient `P ⊗_S Q`. -/
def assocTargetObj (A : ModuleCat.{v} Rᵐᵒᵖ) : ModuleCat.{v} Rᵐᵒᵖ :=
  letI := leftModule ℤ S R P Q
  letI := rightModule ℤ S R P Q
  letI := leftRightSMulCommClass ℤ S R P Q R
  letI := rightModule ℤ R R A (TensorProduct.Balanced ℤ S P Q)
  ModuleCat.of Rᵐᵒᵖ (assocTarget ℤ R S A P Q)

/-- Successive right-module tensor output in associator source coordinates.

The successive tensor-functor output at `A` is isomorphic to `assocSourceObj R S P Q A`, the
left-associated balanced quotient with its right `R`-action. -/
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

/-- Right-module composite coordinate on pure triples.

The forward coordinate map sends the composite-functor element represented by `a, p, q` to the
left-associated class `[[a ⊗ p] ⊗ q]`. -/
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

/-- Right-linear balanced associator for the return tensor.

The balanced associator is an `Rᵐᵒᵖ`-linear equivalence from `(A ⊗_R P) ⊗_S Q` to `A ⊗_R (P
⊗_S Q)` with the induced outer actions. -/
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

/-- Right-linear associator on nested pure classes.

The right-linear associator sends `[[a ⊗ p] ⊗ q]` to `[a ⊗ [p ⊗ q]]`. -/
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

/-- Categorical associator for the right-module return composite.

The successive tensor-functor output at `A` is isomorphic to `assocTargetObj R S P Q A` by the
composite coordinate followed by the right-linear balanced associator. -/
def compositeAssociationIso (A : ModuleCat.{v} Rᵐᵒᵖ) :
    ((tensorFunctor R S P) ⋙ (tensorFunctor S R Q)).obj A ≅
      assocTargetObj R S P Q A :=
  (compositeCoordinates R S P Q A).trans
    (associationLinear R S P Q A).toModuleIso

/-- Categorical right return associator on pure triples.

The categorical return associator sends the successive tensor element `[[a ⊗ p] ⊗ q]` to `[a ⊗
[p ⊗ q]]`. -/
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
/-- Right-module return isomorphism from a composite coefficient contraction.

Given a bimodule equivalence `u : P ⊗_S Q ≅ R`, associate the successive tensor output and
then contract its composite coefficient. This gives an isomorphism from `(A ⊗_R P) ⊗_S Q` to
`A`. -/
def compositeContractionIso (A : ModuleCat.{v} Rᵐᵒᵖ) :
    ((tensorFunctor R S P) ⋙ (tensorFunctor S R Q)).obj A ≅ A := by
  letI := leftModule ℤ S R P Q
  letI := rightModule ℤ S R P Q
  letI := rightSMulCommClass ℤ S R P Q
  letI := leftRightSMulCommClass ℤ S R P Q R
  exact (compositeAssociationIso R S P Q A).trans
    (contractionLinearRaw R (TensorProduct.Balanced ℤ S P Q) u hu A).toModuleIso

/-- Right-module composite return map on pure triples.

The return map defined by `u` sends `[[a ⊗ p] ⊗ q]` to `op (u([p ⊗ q])) • a`, retaining the
right-action order. -/
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
/-- Right-module composite contraction is natural.

The contraction maps give a natural isomorphism from `tensorFunctor R S P ⋙ tensorFunctor S R
Q` to the identity on right `R`-modules. -/
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
/-- Right-module Morita equivalence from two bimodule contractions.

Bimodule equivalences `P ⊗_S Q ≅ R` and `Q ⊗_R P ≅ S` construct `ModuleCat Rᵐᵒᵖ ≌ ModuleCat
Sᵐᵒᵖ`, with forward tensor coefficient `P` and inverse tensor coefficient `Q`. -/
def equivalence : ModuleCat.{v} Rᵐᵒᵖ ≌ ModuleCat.{v} Sᵐᵒᵖ :=
  CategoryTheory.Equivalence.mk (tensorFunctor R S P) (tensorFunctor S R Q)
    (compositeContractionNatIso R S P Q u hu).symm
    (compositeContractionNatIso S R Q P w hw)

/-- Forward right-module Morita functor is tensor by P.

The forward functor of the contraction-based right-module equivalence is `tensorFunctor R S
P`, namely `- ⊗_R P`. -/
@[simp]
theorem equivalence_functor : (equivalence R S P Q u hu w hw).functor =
    tensorFunctor R S P := rfl

/-- Inverse right-module Morita functor is tensor by Q.

The inverse functor of the contraction-based right-module equivalence is `tensorFunctor S R
Q`, namely `- ⊗_S Q`. -/
@[simp]
theorem equivalence_inverse : (equivalence R S P Q u hu w hw).inverse =
    tensorFunctor S R Q := rfl

/-- Counit of the right-module Morita equivalence is its S-return contraction.

The counit is `compositeContractionNatIso S R Q P w hw`, constructed from the bimodule
equivalence `Q ⊗_R P ≅ S`. -/
theorem equivalence_counitIso : (equivalence R S P Q u hu w hw).counitIso =
    compositeContractionNatIso S R Q P w hw := rfl

/-- Unit of the right-module Morita equivalence is adjointified.

The unit is `Equivalence.adjointifyη` of the inverse `R`-return contraction and the specified
`S`-return counit. The tensor functors and counit are retained. -/
theorem equivalence_unitIso : (equivalence R S P Q u hu w hw).unitIso =
    Equivalence.adjointifyη (compositeContractionNatIso R S P Q u hu).symm
      (compositeContractionNatIso S R Q P w hw) := rfl

/-- Right-module Morita counit evaluates the S-contraction.

For a right `S`-module `A`, the counit sends `[[a ⊗ q] ⊗ p]` to `op (w([q ⊗ p])) • a`, where
`w : Q ⊗_R P ≅ S` is the second bimodule equivalence. -/
@[simp, nolint simpNF] -- stated with the equivalence for rw; equivalence_functor simplifies LHS
theorem equivalence_counitIso_mk (A : ModuleCat.{v} Sᵐᵒᵖ)
    (a : A) (q : Q) (p : P) :
    ((equivalence R S P Q u hu w hw).counitIso.hom.app A).hom
        (compositeMk S R Q P A a q p) = op (w (mk ℤ R Q P q p)) • a :=
  compositeContractionIso_mk S R Q P w hw A a q p

end Equivalence

end ModuleCat.BalancedTensorRight
