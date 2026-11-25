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

public import MathlibExt.Algebra.Category.ModuleCat.Bimodule.Over
public import MathlibExt.LinearAlgebra.TensorProduct.Balanced.MoritaCoefficients

/-!
# Original coefficient functors on native k-enveloping modules

The object is the existing `(Q ⊗_R M) ⊗_R P` with its computed S-actions.
The original native morphism acts on M. Scalars and raw coefficient worlds
remain independent; the functor's target world contains its fixed P/Q.
No invertibility or category comparison is required for this functor.
-/

@[expose] public section

noncomputable section

open CategoryTheory MulOpposite
open scoped TensorProduct

universe u r s p q v m

namespace ModuleCat.Bimodule.Over.Morita

variable (k : Type u) [CommRing k]
  (R : Type r) [Ring R] [Algebra k R] (S : Type s) [Ring S] [Algebra k S]
  (P : Type p) [AddCommGroup P] [Module k P]
  [Module R P] [Module Sᵐᵒᵖ P] [SMulCommClass R Sᵐᵒᵖ P]
  [IsScalarTower k R P] [IsScalarTower k Sᵐᵒᵖ P]
  (Q : Type q) [AddCommGroup Q] [Module k Q]
  [Module S Q] [Module Rᵐᵒᵖ Q] [SMulCommClass S Rᵐᵒᵖ Q]
  [IsScalarTower k S Q] [IsScalarTower k Rᵐᵒᵖ Q]

section GivenActions

variable (M : Type m) [AddCommGroup M] [Module k M]
  [Module R M] [Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M]
  [IsScalarTower k R M] [IsScalarTower k Rᵐᵒᵖ M]

include R P Q M in
/-- Bundle the existing coefficient tensor with its computed enveloping module. -/
def tensorObject : ModuleCat.{max p q m} (S ⊗[k] Sᵐᵒᵖ) :=
  letI := TensorProduct.Balanced.Morita.coefficientModule k R S Q M P
  ModuleCat.of (S ⊗[k] Sᵐᵒᵖ)
    (TensorProduct.Balanced.Morita.coefficientTensor k R Q M P)
omit [IsScalarTower k Rᵐᵒᵖ Q] in

/-- The transferred object's native ground restriction is the original quotient ground. -/
theorem tensorObject_groundModule :
    ModuleCat.Bimodule.Over.groundModule k S (tensorObject k R S P Q M) =
      (inferInstance : Module k (TensorProduct.Balanced.Morita.coefficientTensor k R Q M P)) := by
  let := TensorProduct.Balanced.Morita.coefficientLeftModule k R S Q M P
  let := TensorProduct.Balanced.Morita.coefficientRightModule k R S Q M P
  let := TensorProduct.Balanced.Morita.coefficientActionsComm k R S Q M P
  let := TensorProduct.Balanced.Morita.coefficientLeftTower k R S Q M P
  let := TensorProduct.Balanced.Morita.coefficientRightTower k R S Q M P
  exact ModuleCat.Bimodule.Over.groundModule_ofTensor k S
    (TensorProduct.Balanced.Morita.coefficientTensor k R Q M P)
omit [IsScalarTower k Rᵐᵒᵖ Q] in

/-- The original Q action is recovered from the native enveloping object. -/
theorem tensorObject_leftModule :
    ModuleCat.Bimodule.Over.leftModule k S (tensorObject k R S P Q M) =
      TensorProduct.Balanced.Morita.coefficientLeftModule k R S Q M P := by
  let := TensorProduct.Balanced.Morita.coefficientLeftModule k R S Q M P
  let := TensorProduct.Balanced.Morita.coefficientRightModule k R S Q M P
  let := TensorProduct.Balanced.Morita.coefficientActionsComm k R S Q M P
  let := TensorProduct.Balanced.Morita.coefficientLeftTower k R S Q M P
  let := TensorProduct.Balanced.Morita.coefficientRightTower k R S Q M P
  exact ModuleCat.Bimodule.Over.leftModule_ofTensor k S
    (TensorProduct.Balanced.Morita.coefficientTensor k R Q M P)
omit [IsScalarTower k Rᵐᵒᵖ Q] in

/-- The original P action is likewise recovered from the native object. -/
theorem tensorObject_rightModule :
    ModuleCat.Bimodule.Over.rightModule k S (tensorObject k R S P Q M) =
      TensorProduct.Balanced.Morita.coefficientRightModule k R S Q M P := by
  let := TensorProduct.Balanced.Morita.coefficientLeftModule k R S Q M P
  let := TensorProduct.Balanced.Morita.coefficientRightModule k R S Q M P
  let := TensorProduct.Balanced.Morita.coefficientActionsComm k R S Q M P
  let := TensorProduct.Balanced.Morita.coefficientLeftTower k R S Q M P
  let := TensorProduct.Balanced.Morita.coefficientRightTower k R S Q M P
  exact ModuleCat.Bimodule.Over.rightModule_ofTensor k S
    (TensorProduct.Balanced.Morita.coefficientTensor k R Q M P)

end GivenActions

include P Q in
/-- Transfer a native k-compatible bimodule with its actual restricted actions. -/
def tensorObj (X : ModuleCat.{v} (R ⊗[k] Rᵐᵒᵖ)) :
    ModuleCat.{max p q v} (S ⊗[k] Sᵐᵒᵖ) := by
  letI := ModuleCat.Bimodule.Over.groundModule k R X
  letI := ModuleCat.Bimodule.Over.leftModule k R X
  letI := ModuleCat.Bimodule.Over.rightModule k R X
  letI := ModuleCat.Bimodule.Over.leftTower k R X
  letI := ModuleCat.Bimodule.Over.rightTower k R X
  letI := ModuleCat.Bimodule.Over.commute k R X
  exact tensorObject k R S P Q X

/-- The original ordered pure coefficient class, with its actual native endpoint. -/
def tensorMk (X : ModuleCat.{v} (R ⊗[k] Rᵐᵒᵖ)) (q : Q) (x : X) (p : P) :
    tensorObj k R S P Q X := by
  letI := ModuleCat.Bimodule.Over.groundModule k R X
  letI := ModuleCat.Bimodule.Over.leftModule k R X
  letI := ModuleCat.Bimodule.Over.rightModule k R X
  letI := ModuleCat.Bimodule.Over.leftTower k R X
  letI := ModuleCat.Bimodule.Over.rightTower k R X
  letI := ModuleCat.Bimodule.Over.commute k R X
  letI := TensorProduct.Balanced.rightModule k R R Q X
  exact TensorProduct.Balanced.mk k R (TensorProduct.Balanced k R Q X) P
    (TensorProduct.Balanced.mk k R Q X q x) p

/-- Original native morphisms act only on the middle coefficient. -/
def tensorMap {X Y : ModuleCat.{v} (R ⊗[k] Rᵐᵒᵖ)} (f : X ⟶ Y) :
    tensorObj k R S P Q X ⟶ tensorObj k R S P Q Y := by
  letI := ModuleCat.Bimodule.Over.groundModule k R X
  letI := ModuleCat.Bimodule.Over.leftModule k R X
  letI := ModuleCat.Bimodule.Over.rightModule k R X
  letI := ModuleCat.Bimodule.Over.leftTower k R X
  letI := ModuleCat.Bimodule.Over.rightTower k R X
  letI := ModuleCat.Bimodule.Over.commute k R X
  letI := ModuleCat.Bimodule.Over.groundModule k R Y
  letI := ModuleCat.Bimodule.Over.leftModule k R Y
  letI := ModuleCat.Bimodule.Over.rightModule k R Y
  letI := ModuleCat.Bimodule.Over.leftTower k R Y
  letI := ModuleCat.Bimodule.Over.rightTower k R Y
  letI := ModuleCat.Bimodule.Over.commute k R Y
  letI : Module (S ⊗[k] Sᵐᵒᵖ)
      (TensorProduct.Balanced.Morita.coefficientTensor k R Q X P) :=
    TensorProduct.Balanced.Morita.coefficientModule k R S Q X P
  letI : Module (S ⊗[k] Sᵐᵒᵖ)
      (TensorProduct.Balanced.Morita.coefficientTensor k R Q Y P) :=
    TensorProduct.Balanced.Morita.coefficientModule k R S Q Y P
  let g : (letI : Module (R ⊗[k] Rᵐᵒᵖ) X := ModuleCat.Bimodule.Over.reconstructedModule k R X
      letI : Module (R ⊗[k] Rᵐᵒᵖ) Y := ModuleCat.Bimodule.Over.reconstructedModule k R Y
      X →ₗ[R ⊗[k] Rᵐᵒᵖ] Y) := (ModuleCat.Bimodule.Over.reconstructedMap k R f).hom
  let A := tensorObj k R S P Q X
  let B := tensorObj k R S P Q Y
  exact @ModuleCat.ofHom (S ⊗[k] Sᵐᵒᵖ) _ A.carrier B.carrier
    A.isAddCommGroup A.isModule B.isAddCommGroup B.isModule
    (TensorProduct.Balanced.Morita.coefficientMap
      (k := k) (R := R) (S := S) (Q := Q) (M := X) (N := Y) (P := P) g)

@[simp]
theorem tensorMap_mk {X Y : ModuleCat.{v} (R ⊗[k] Rᵐᵒᵖ)} (f : X ⟶ Y)
    (q : Q) (x : X) (p : P) :
    (tensorMap k R S P Q f).hom (tensorMk k R S P Q X q x p) =
      tensorMk k R S P Q Y q (f.hom x) p := by
  let := ModuleCat.Bimodule.Over.groundModule k R X
  let := ModuleCat.Bimodule.Over.leftModule k R X
  let := ModuleCat.Bimodule.Over.rightModule k R X
  let := ModuleCat.Bimodule.Over.leftTower k R X
  let := ModuleCat.Bimodule.Over.rightTower k R X
  let := ModuleCat.Bimodule.Over.commute k R X
  let := ModuleCat.Bimodule.Over.groundModule k R Y
  let := ModuleCat.Bimodule.Over.leftModule k R Y
  let := ModuleCat.Bimodule.Over.rightModule k R Y
  let := ModuleCat.Bimodule.Over.leftTower k R Y
  let := ModuleCat.Bimodule.Over.rightTower k R Y
  let := ModuleCat.Bimodule.Over.commute k R Y
  let := TensorProduct.Balanced.rightModule k R R Q X
  let := TensorProduct.Balanced.rightModule k R R Q Y
  let : Module (S ⊗[k] Sᵐᵒᵖ)
      (TensorProduct.Balanced.Morita.coefficientTensor k R Q X P) :=
    TensorProduct.Balanced.Morita.coefficientModule k R S Q X P
  let : Module (S ⊗[k] Sᵐᵒᵖ)
      (TensorProduct.Balanced.Morita.coefficientTensor k R Q Y P) :=
    TensorProduct.Balanced.Morita.coefficientModule k R S Q Y P
  let g : (letI : Module (R ⊗[k] Rᵐᵒᵖ) X := ModuleCat.Bimodule.Over.reconstructedModule k R X
      letI : Module (R ⊗[k] Rᵐᵒᵖ) Y := ModuleCat.Bimodule.Over.reconstructedModule k R Y
      X →ₗ[R ⊗[k] Rᵐᵒᵖ] Y) := (ModuleCat.Bimodule.Over.reconstructedMap k R f).hom
  have hg : g x = f.hom x := ModuleCat.Bimodule.Over.reconstructedMap_apply k R f x
  change TensorProduct.Balanced.Morita.coefficientMap
      (k := k) (R := R) (S := S) (Q := Q) (M := X) (N := Y) (P := P) g
      (TensorProduct.Balanced.mk k R (TensorProduct.Balanced k R Q X) P
        (TensorProduct.Balanced.mk k R Q X q x) p) = _
  have h := TensorProduct.Balanced.Morita.coefficientMap_mk
    (k := k) (R := R) (S := S) (Q := Q) (M := X) (N := Y) (P := P) g q x p
  exact h.trans (congrArg (fun y : Y =>
    TensorProduct.Balanced.mk k R (TensorProduct.Balanced k R Q Y) P
      (TensorProduct.Balanced.mk k R Q Y q y) p) hg)

include P Q in
/-- The actual k-envelope coefficient functor, with its two original functor laws. -/
def tensorFunctor :
    ModuleCat.{v} (R ⊗[k] Rᵐᵒᵖ) ⥤ ModuleCat.{max p q v} (S ⊗[k] Sᵐᵒᵖ) where
  obj := tensorObj k R S P Q
  map := tensorMap k R S P Q
  map_id X := by
    let := ModuleCat.Bimodule.Over.groundModule k R X
    let := ModuleCat.Bimodule.Over.leftModule k R X
    let := ModuleCat.Bimodule.Over.rightModule k R X
    let := ModuleCat.Bimodule.Over.leftTower k R X
    let := ModuleCat.Bimodule.Over.rightTower k R X
    let := ModuleCat.Bimodule.Over.commute k R X
    let := TensorProduct.Balanced.rightModule k R R Q X
    apply ModuleCat.hom_ext
    apply LinearMap.toAddMonoidHom_injective
    apply TensorProduct.Balanced.Morita.coefficientHom_ext k R Q X P
    intro q x p
    change (tensorMap k R S P Q (𝟙 X)).hom (tensorMk k R S P Q X q x p) =
      tensorMk k R S P Q X q x p
    exact tensorMap_mk k R S P Q (𝟙 X) q x p
  map_comp {X Y Z} f g := by
    let := ModuleCat.Bimodule.Over.groundModule k R X
    let := ModuleCat.Bimodule.Over.leftModule k R X
    let := ModuleCat.Bimodule.Over.rightModule k R X
    let := ModuleCat.Bimodule.Over.leftTower k R X
    let := ModuleCat.Bimodule.Over.rightTower k R X
    let := ModuleCat.Bimodule.Over.commute k R X
    let := ModuleCat.Bimodule.Over.groundModule k R Y
    let := ModuleCat.Bimodule.Over.leftModule k R Y
    let := ModuleCat.Bimodule.Over.rightModule k R Y
    let := ModuleCat.Bimodule.Over.leftTower k R Y
    let := ModuleCat.Bimodule.Over.rightTower k R Y
    let := ModuleCat.Bimodule.Over.commute k R Y
    let := ModuleCat.Bimodule.Over.groundModule k R Z
    let := ModuleCat.Bimodule.Over.leftModule k R Z
    let := ModuleCat.Bimodule.Over.rightModule k R Z
    let := ModuleCat.Bimodule.Over.leftTower k R Z
    let := ModuleCat.Bimodule.Over.rightTower k R Z
    let := ModuleCat.Bimodule.Over.commute k R Z
    let := TensorProduct.Balanced.rightModule k R R Q X
    let := TensorProduct.Balanced.rightModule k R R Q Y
    let := TensorProduct.Balanced.rightModule k R R Q Z
    apply ModuleCat.hom_ext
    apply LinearMap.toAddMonoidHom_injective
    apply TensorProduct.Balanced.Morita.coefficientHom_ext k R Q X P
    intro q x p
    let a : tensorObj k R S P Q X := tensorMk k R S P Q X q x p
    change (tensorMap k R S P Q (f ≫ g)).hom a =
      (tensorMap k R S P Q g).hom ((tensorMap k R S P Q f).hom a)
    have hfg := tensorMap_mk k R S P Q (f ≫ g) q x p
    have hg := tensorMap_mk k R S P Q g q (f.hom x) p
    have hf := tensorMap_mk k R S P Q f q x p
    exact hfg.trans (hg.symm.trans (congrArg
      (fun y : tensorObj k R S P Q Y => (tensorMap k R S P Q g).hom y) hf.symm))

end ModuleCat.Bimodule.Over.Morita
