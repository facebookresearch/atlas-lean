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

public import MathlibExt.Algebra.Category.ModuleCat.Bimodule
public import MathlibExt.LinearAlgebra.TensorProduct.Balanced.MoritaCoefficients
public import MathlibExt.LinearAlgebra.TensorProduct.Balanced.Unitors
public import Mathlib.CategoryTheory.Equivalence
public import MathlibExt.Algebra.Module.NatInt

/-!
# Native bimodule tensor functors from a Morita pair

The categories are the original native enveloping-module categories. The
object is the original `(Q ⊗_R M) ⊗_R P`, with its computed outer actions.
The original module reconstruction and coefficient map preserve native
carriers and morphism values. No category equivalence is given as data.
-/

@[expose] public section

noncomputable section

open CategoryTheory MulOpposite
open scoped TensorProduct

universe r s v

namespace ModuleCat.Bimodule.Morita

attribute [local instance] ModuleCat.Bimodule.int_isScalarTower
  Module.intModule_smulCommClass

variable (R : Type r) (S : Type s) [Ring R] [Ring S]
  (P Q : Type v) [AddCommGroup P] [AddCommGroup Q]
  [Module R P] [Module Sᵐᵒᵖ P] [SMulCommClass R Sᵐᵒᵖ P]
  [Module S Q] [Module Rᵐᵒᵖ Q] [SMulCommClass S Rᵐᵒᵖ Q]

section OriginalActions

variable (M : Type v) [AddCommGroup M] [givenIntegerModule : Module ℤ M]
  [Module R M] [Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M]

include P Q in
/-- Bundle the actual coefficient tensor with its earned native enveloping action. -/
def tensorObject : ModuleCat.{v} (S ⊗[ℤ] Sᵐᵒᵖ) := by
  letI := TensorProduct.Balanced.Morita.coefficientModule ℤ R S Q M P
  exact ModuleCat.of (S ⊗[ℤ] Sᵐᵒᵖ)
    (TensorProduct.Balanced.Morita.coefficientTensor ℤ R Q M P)

end OriginalActions

include P Q in
/-- The actual tensor object of the given native R-bimodule. -/
def tensorObj (X : ModuleCat.{v} (R ⊗[ℤ] Rᵐᵒᵖ)) :
    ModuleCat.{v} (S ⊗[ℤ] Sᵐᵒᵖ) := by
  letI := ModuleCat.Bimodule.leftModule R X
  letI := ModuleCat.Bimodule.rightModule R X
  letI := ModuleCat.Bimodule.commute R X
  exact tensorObject R S P Q X

/-- The original native morphism acts only on the middle coefficient. -/
def tensorMap {X Y : ModuleCat.{v} (R ⊗[ℤ] Rᵐᵒᵖ)} (f : X ⟶ Y) :
    tensorObj R S P Q X ⟶ tensorObj R S P Q Y := by
  letI := ModuleCat.Bimodule.leftModule R X
  letI := ModuleCat.Bimodule.rightModule R X
  letI := ModuleCat.Bimodule.commute R X
  letI := ModuleCat.Bimodule.leftModule R Y
  letI := ModuleCat.Bimodule.rightModule R Y
  letI := ModuleCat.Bimodule.commute R Y
  letI : Module (S ⊗[ℤ] Sᵐᵒᵖ)
      (TensorProduct.Balanced.Morita.coefficientTensor ℤ R Q X P) :=
    TensorProduct.Balanced.Morita.coefficientModule ℤ R S Q X P
  letI : Module (S ⊗[ℤ] Sᵐᵒᵖ)
      (TensorProduct.Balanced.Morita.coefficientTensor ℤ R Q Y P) :=
    TensorProduct.Balanced.Morita.coefficientModule ℤ R S Q Y P
  let g : (letI : Module (R ⊗[ℤ] Rᵐᵒᵖ) X := ModuleCat.Bimodule.reconstructedModule R X
      letI : Module (R ⊗[ℤ] Rᵐᵒᵖ) Y := ModuleCat.Bimodule.reconstructedModule R Y
      X →ₗ[R ⊗[ℤ] Rᵐᵒᵖ] Y) := (ModuleCat.Bimodule.reconstructedMap R f).hom
  exact ModuleCat.ofHom
    (TensorProduct.Balanced.Morita.coefficientMap
      (k := ℤ) (R := R) (S := S) (Q := Q) (M := X) (N := Y) (P := P) g)

/-- Pure triples retain the original middle map, with both outer factors fixed. -/
@[simp, nolint simpNF] -- stated with Balanced.mk for rw; Balanced.mk_apply simplifies LHS
theorem tensorMap_mk {X Y : ModuleCat.{v} (R ⊗[ℤ] Rᵐᵒᵖ)} (f : X ⟶ Y)
    (q : Q) (x : X) (p : P) :
    letI := ModuleCat.Bimodule.leftModule R X
    letI := ModuleCat.Bimodule.rightModule R X
    letI := ModuleCat.Bimodule.commute R X
    letI := ModuleCat.Bimodule.leftModule R Y
    letI := ModuleCat.Bimodule.rightModule R Y
    letI := ModuleCat.Bimodule.commute R Y
    letI := TensorProduct.Balanced.rightModule ℤ R R Q X
    letI := TensorProduct.Balanced.rightModule ℤ R R Q Y
    (tensorMap R S P Q f).hom
        (TensorProduct.Balanced.mk ℤ R (TensorProduct.Balanced ℤ R Q X) P
          (TensorProduct.Balanced.mk ℤ R Q X q x) p) =
      TensorProduct.Balanced.mk ℤ R (TensorProduct.Balanced ℤ R Q Y) P
        (TensorProduct.Balanced.mk ℤ R Q Y q (f.hom x)) p := by
  let := ModuleCat.Bimodule.leftModule R X
  let := ModuleCat.Bimodule.rightModule R X
  let := ModuleCat.Bimodule.commute R X
  let := ModuleCat.Bimodule.leftModule R Y
  let := ModuleCat.Bimodule.rightModule R Y
  let := ModuleCat.Bimodule.commute R Y
  let := TensorProduct.Balanced.rightModule ℤ R R Q X
  let := TensorProduct.Balanced.rightModule ℤ R R Q Y
  let : Module (S ⊗[ℤ] Sᵐᵒᵖ)
      (TensorProduct.Balanced.Morita.coefficientTensor ℤ R Q X P) :=
    TensorProduct.Balanced.Morita.coefficientModule ℤ R S Q X P
  let : Module (S ⊗[ℤ] Sᵐᵒᵖ)
      (TensorProduct.Balanced.Morita.coefficientTensor ℤ R Q Y P) :=
    TensorProduct.Balanced.Morita.coefficientModule ℤ R S Q Y P
  let g : (letI : Module (R ⊗[ℤ] Rᵐᵒᵖ) X := ModuleCat.Bimodule.reconstructedModule R X
      letI : Module (R ⊗[ℤ] Rᵐᵒᵖ) Y := ModuleCat.Bimodule.reconstructedModule R Y
      X →ₗ[R ⊗[ℤ] Rᵐᵒᵖ] Y) := (ModuleCat.Bimodule.reconstructedMap R f).hom
  have hg : g x = f.hom x := ModuleCat.Bimodule.reconstructedMap_apply R f x
  change TensorProduct.Balanced.Morita.coefficientMap
      (k := ℤ) (R := R) (S := S) (Q := Q) (M := X) (N := Y) (P := P) g
      (TensorProduct.Balanced.mk ℤ R (TensorProduct.Balanced ℤ R Q X) P
        (TensorProduct.Balanced.mk ℤ R Q X q x) p) = _
  have h := TensorProduct.Balanced.Morita.coefficientMap_mk
    (k := ℤ) (R := R) (S := S) (Q := Q) (M := X) (N := Y) (P := P) g q x p
  exact h.trans (congrArg (fun y : Y =>
    TensorProduct.Balanced.mk ℤ R (TensorProduct.Balanced ℤ R Q Y) P
      (TensorProduct.Balanced.mk ℤ R Q Y q y) p) hg)

include P Q in
/-- The actual native bimodule tensor functor, with both functor laws earned. -/
def tensorFunctor :
    ModuleCat.{v} (R ⊗[ℤ] Rᵐᵒᵖ) ⥤ ModuleCat.{v} (S ⊗[ℤ] Sᵐᵒᵖ) where
  obj := tensorObj R S P Q
  map := tensorMap R S P Q
  map_id X := by
    let := ModuleCat.Bimodule.leftModule R X
    let := ModuleCat.Bimodule.rightModule R X
    let := ModuleCat.Bimodule.commute R X
    let := TensorProduct.Balanced.rightModule ℤ R R Q X
    apply ModuleCat.hom_ext
    apply LinearMap.toAddMonoidHom_injective
    apply TensorProduct.Balanced.Morita.coefficientHom_ext ℤ R Q X P
    intro q x p
    change (tensorMap R S P Q (𝟙 X)).hom
        (TensorProduct.Balanced.mk ℤ R (TensorProduct.Balanced ℤ R Q X) P
          (TensorProduct.Balanced.mk ℤ R Q X q x) p) =
      TensorProduct.Balanced.mk ℤ R (TensorProduct.Balanced ℤ R Q X) P
        (TensorProduct.Balanced.mk ℤ R Q X q x) p
    exact tensorMap_mk R S P Q (𝟙 X) q x p
  map_comp {X Y Z} f g := by
    let := ModuleCat.Bimodule.leftModule R X
    let := ModuleCat.Bimodule.rightModule R X
    let := ModuleCat.Bimodule.commute R X
    let := ModuleCat.Bimodule.leftModule R Y
    let := ModuleCat.Bimodule.rightModule R Y
    let := ModuleCat.Bimodule.commute R Y
    let := ModuleCat.Bimodule.leftModule R Z
    let := ModuleCat.Bimodule.rightModule R Z
    let := ModuleCat.Bimodule.commute R Z
    let := TensorProduct.Balanced.rightModule ℤ R R Q X
    let := TensorProduct.Balanced.rightModule ℤ R R Q Y
    let := TensorProduct.Balanced.rightModule ℤ R R Q Z
    apply ModuleCat.hom_ext
    apply LinearMap.toAddMonoidHom_injective
    apply TensorProduct.Balanced.Morita.coefficientHom_ext ℤ R Q X P
    intro q x p
    let a := TensorProduct.Balanced.mk ℤ R (TensorProduct.Balanced ℤ R Q X) P
      (TensorProduct.Balanced.mk ℤ R Q X q x) p
    change (tensorMap R S P Q (f ≫ g)).hom a =
      (tensorMap R S P Q g).hom ((tensorMap R S P Q f).hom a)
    have hfg := tensorMap_mk R S P Q (f ≫ g) q x p
    have hg := tensorMap_mk R S P Q g q (f.hom x) p
    have hf := tensorMap_mk R S P Q f q x p
    exact hfg.trans (hg.symm.trans (congrArg
      (fun y : tensorObj R S P Q Y => (tensorMap R S P Q g).hom y) hf.symm))

end ModuleCat.Bimodule.Morita
