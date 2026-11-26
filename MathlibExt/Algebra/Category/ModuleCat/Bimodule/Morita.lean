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
# Tensor functors between enveloping-module categories

Let R,S be rings in universes r,s, and let P be an (R,S)-bimodule and Q an (S,R)-bimodule with
carriers in universe v. For an R-bimodule M, the coefficient tensor F(M)=(Q⊗_R M)⊗_R P has left
S-action on Q and right S-action on P.

These actions define an S⊗_ℤSᵒᵖ-module. They give a functor
ModuleCat_v(R⊗_ℤRᵒᵖ)→ModuleCat_v(S⊗_ℤSᵒᵖ), whose map on f:M→N sends (q⊗m)⊗p to (q⊗f(m))⊗p. The
two endpoint rings and the coefficient carrier universe remain independent. This tensor functor
is defined for any such P,Q.
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
/-- Let R,S be rings in independent universes r,s. Let P be an (R,S)-bimodule and Q an
(S,R)-bimodule, with abelian carriers in universe v and commuting endpoint actions. For an
R-bimodule M in v, F(M)=(Q⊗_R M)⊗_R P is an object of ModuleCat_v(S⊗_ℤSᵒᵖ). The left S-action
acts on q and the right S-action on p: (s⊗t)•((q⊗m)⊗p)=((s•q)⊗m)⊗(t•p), for t∈Sᵒᵖ. -/
def tensorObject : ModuleCat.{v} (S ⊗[ℤ] Sᵐᵒᵖ) := by
  letI := TensorProduct.Balanced.Morita.coefficientModule ℤ R S Q M P
  exact ModuleCat.of (S ⊗[ℤ] Sᵐᵒᵖ)
    (TensorProduct.Balanced.Morita.coefficientTensor ℤ R Q M P)

end OriginalActions

include P Q in
/-- Let R,S be rings in independent universes r,s. Let P be an (R,S)-bimodule and Q an
(S,R)-bimodule, with abelian carriers in universe v and commuting endpoint actions. For
X∈ModuleCat_v(R⊗_ℤRᵒᵖ), restrict its endpoint actions and form F(X)=(Q⊗_R X)⊗_R P. The outer Q
and P actions make it an S⊗_ℤSᵒᵖ-module in the same coefficient carrier universe v. -/
def tensorObj (X : ModuleCat.{v} (R ⊗[ℤ] Rᵐᵒᵖ)) :
    ModuleCat.{v} (S ⊗[ℤ] Sᵐᵒᵖ) := by
  letI := ModuleCat.Bimodule.leftModule R X
  letI := ModuleCat.Bimodule.rightModule R X
  letI := ModuleCat.Bimodule.commute R X
  exact tensorObject R S P Q X

/-- Let R,S be rings in independent universes r,s. Let P be an (R,S)-bimodule and Q an
(S,R)-bimodule, with abelian carriers in universe v and commuting endpoint actions. For f:X→Y in
ModuleCat_v(R⊗_ℤRᵒᵖ), the induced S⊗_ℤSᵒᵖ-linear map F(X)→F(Y) is id_Q⊗f⊗id_P on the
left-associated balanced tensor. Its outer factors are retained, and its pure coefficient value
is (q⊗f(x))⊗p. -/
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

-- stated with Balanced.mk for rw; Balanced.mk_apply simplifies LHS
/-- Let R,S be rings in independent universes r,s. Let P be an (R,S)-bimodule and Q an
(S,R)-bimodule, with abelian carriers in universe v and commuting endpoint actions. For f:X→Y in
the R-enveloping module category and q∈Q,x∈X,p∈P, the tensor map satisfies F(f)((q⊗_R x)⊗_R
p)=(q⊗_R f(x))⊗_R p. Both sides are classes in the balanced tensor F(Y), with the endpoint
actions restricted from X,Y. -/
@[simp, nolint simpNF]
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
/-- Let R,S be rings in independent universes r,s. Let P be an (R,S)-bimodule and Q an
(S,R)-bimodule, with abelian carriers in universe v and commuting endpoint actions. The functor
F:ModuleCat_v(R⊗_ℤRᵒᵖ)→ModuleCat_v(S⊗_ℤSᵒᵖ) has F(X)=(Q⊗_R X)⊗_R P and F(f)=id_Q⊗f⊗id_P. Its
maps preserve identity morphisms and composition, using the same computed outer S-actions. -/
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
