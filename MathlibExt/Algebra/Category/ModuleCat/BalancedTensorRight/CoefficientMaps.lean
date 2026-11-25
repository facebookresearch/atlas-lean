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

public import MathlibExt.Algebra.Category.ModuleCat.BalancedTensorRight.Derived

/-!
# Coefficient morphisms on enriched tensor and Tor

The balanced quotient coefficient map is linear for the right outer action.
Its left-derived natural transformation acts on the right-module-valued Tor
functors.
-/

@[expose] public section

noncomputable section

open CategoryTheory MulOpposite TensorProduct.Balanced

universe r s v

namespace ModuleCat.BalancedTensorRight

variable (R : Type r) (S : Type s) [Ring R] [Ring S]
  (B B' : Type v) [AddCommGroup B] [AddCommGroup B']
  [Module R B] [Module R B'] [Module Sᵐᵒᵖ B] [Module Sᵐᵒᵖ B']
  [SMulCommClass R Sᵐᵒᵖ B] [SMulCommClass R Sᵐᵒᵖ B']
  (f : B →ₗ[R] B')
  (hS : ∀ (s : Sᵐᵒᵖ) (b : B), f (s • b) = s • f b)

/-- Change only the original left-module coefficient of the actual tensor quotient. -/
def tensorCoefficientMap (A : ModuleCat.{v} Rᵐᵒᵖ) :
    tensorObj R S B A ⟶ tensorObj R S B' A := by
  letI := rightModule ℤ R S A B
  letI := rightModule ℤ R S A B'
  let fS : B →ₗ[Sᵐᵒᵖ] B' :=
    { toFun := f
      map_add' := f.map_add
      map_smul' s b := by
        simpa only [RingHom.id_apply] using hS s b }
  exact ModuleCat.ofHom
    (TensorProduct.Balanced.CoefficientHom.coefficientTensorMap
      (R := R) (S := S) (B := B) (B' := B') (A := A) fS
      (fun r b => f.map_smul r b))

/-- The computed coefficient map has the original pure tensor value. -/
theorem tensorCoefficientMap_mk (A : ModuleCat.{v} Rᵐᵒᵖ) (a : A) (b : B) :
    (tensorCoefficientMap R S B B' f hS A).hom (mk ℤ R A B a b) =
      mk ℤ R A B' a (f b) := by
  let := rightModule ℤ R S A B
  let := rightModule ℤ R S A B'
  let fS : B →ₗ[Sᵐᵒᵖ] B' :=
    { toFun := f
      map_add' := f.map_add
      map_smul' s b := by
        simpa only [RingHom.id_apply] using hS s b }
  change TensorProduct.Balanced.CoefficientHom.coefficientTensorMap
      (R := R) (S := S) (B := B) (B' := B') (A := A) fS
      (fun r b => f.map_smul r b) (mk ℤ R A B a b) = mk ℤ R A B' a (f b)
  exact TensorProduct.Balanced.CoefficientHom.coefficientTensorMap_mk
    (R := R) (S := S) (B := B) (B' := B') (A := A) fS
    (fun r b => f.map_smul r b) a b

/-- Actual first-factor and coefficient morphisms commute on the original quotient. -/
theorem tensorCoefficientMap_naturality {A A' : ModuleCat.{v} Rᵐᵒᵖ} (g : A ⟶ A') :
    tensorMap R S B g ≫ tensorCoefficientMap R S B B' f hS A' =
      tensorCoefficientMap R S B B' f hS A ≫ tensorMap R S B' g := by
  let := rightModule ℤ R S A B
  let := rightModule ℤ R S A' B'
  apply ModuleCat.hom_ext
  apply LinearMap.toAddMonoidHom_injective
  apply TensorProduct.Balanced.addHom_ext ℤ R A B
  intro a b
  change (tensorCoefficientMap R S B B' f hS A').hom
      ((tensorMap R S B g).hom (mk ℤ R A B a b)) =
    (tensorMap R S B' g).hom
      ((tensorCoefficientMap R S B B' f hS A).hom (mk ℤ R A B a b))
  rw [tensorMap_mk, tensorCoefficientMap_mk, tensorCoefficientMap_mk, tensorMap_mk]

set_option linter.unusedVariables false in
/-- The actual bimodule coefficient morphism induces a tensor natural transformation. -/
def tensorCoefficientTransformation : tensorFunctor R S B ⟶ tensorFunctor R S B' where
  app := tensorCoefficientMap R S B B' f hS
  naturality {A A'} g := tensorCoefficientMap_naturality R S B B' f hS g

/-- Its components are the already constructed outer-linear quotient maps. -/
theorem tensorCoefficientTransformation_app (A : ModuleCat.{v} Rᵐᵒᵖ) :
    (tensorCoefficientTransformation R S B B' f hS).app A =
      tensorCoefficientMap R S B B' f hS A := rfl

/-- The identity coefficient morphism gives the actual tensor identity. -/
theorem tensorCoefficientTransformation_id :
    tensorCoefficientTransformation R S B B (LinearMap.id : B →ₗ[R] B)
      (fun _ _ => rfl) = 𝟙 (tensorFunctor R S B) := by
  apply NatTrans.ext
  funext A
  let := rightModule ℤ R S A B
  apply ModuleCat.hom_ext
  apply LinearMap.toAddMonoidHom_injective
  apply TensorProduct.Balanced.addHom_ext ℤ R A B
  intro a b
  change (tensorCoefficientMap R S B B LinearMap.id (fun _ _ => rfl) A).hom
      (mk ℤ R A B a b) = mk ℤ R A B a b
  rw [tensorCoefficientMap_mk, LinearMap.id_apply]

variable (B'' : Type v) [AddCommGroup B''] [Module R B''] [Module Sᵐᵒᵖ B'']
  [SMulCommClass R Sᵐᵒᵖ B'']
  (g : B' →ₗ[R] B'')
  (hSg : ∀ (s : Sᵐᵒᵖ) (b : B'), g (s • b) = s • g b)

/-- Composition is proved on the same original pure coefficient representatives. -/
theorem tensorCoefficientTransformation_comp :
    tensorCoefficientTransformation R S B B' f hS ≫
        tensorCoefficientTransformation R S B' B'' g hSg =
      tensorCoefficientTransformation R S B B'' (g.comp f)
        (fun s b => (congrArg g (hS s b)).trans (hSg s (f b))) := by
  apply NatTrans.ext
  funext A
  let := rightModule ℤ R S A B
  let := rightModule ℤ R S A B''
  apply ModuleCat.hom_ext
  apply LinearMap.toAddMonoidHom_injective
  apply TensorProduct.Balanced.addHom_ext ℤ R A B
  intro a b
  change (tensorCoefficientMap R S B' B'' g hSg A).hom
      ((tensorCoefficientMap R S B B' f hS A).hom (mk ℤ R A B a b)) =
    (tensorCoefficientMap R S B B'' (g.comp f)
      (fun s b => (congrArg g (hS s b)).trans (hSg s (f b))) A).hom (mk ℤ R A B a b)
  rw [tensorCoefficientMap_mk, tensorCoefficientMap_mk, tensorCoefficientMap_mk]
  rfl

section Tor

variable [HasProjectiveResolutions (ModuleCat.{v} Rᵐᵒᵖ)]

/-- The native left-derived transformation retains the existing Sᵐᵒᵖ-valued Tor. -/
def torCoefficientTransformation (n : ℕ) :
    torFunctor R S B n ⟶ torFunctor R S B' n :=
  NatTrans.leftDerived (tensorCoefficientTransformation R S B B' f hS) n

/-- Its actual components are canonical coefficient morphisms of native Tor objects. -/
def torCoefficientMap (n : ℕ) (A : ModuleCat.{v} Rᵐᵒᵖ) :
    (torFunctor R S B n).obj A ⟶ (torFunctor R S B' n).obj A :=
  (torCoefficientTransformation R S B B' f hS n).app A

/-- The original resolved-variable naturality is earned by the native transformation. -/
theorem torCoefficientMap_naturality (n : ℕ)
    {A A' : ModuleCat.{v} Rᵐᵒᵖ} (a : A ⟶ A') :
    (torFunctor R S B n).map a ≫ torCoefficientMap R S B B' f hS n A' =
      torCoefficientMap R S B B' f hS n A ≫ (torFunctor R S B' n).map a :=
  (torCoefficientTransformation R S B B' f hS n).naturality a

/-- Identity coefficient maps induce the identity on the same native Tor functor. -/
theorem torCoefficientTransformation_id (n : ℕ) :
    torCoefficientTransformation R S B B (LinearMap.id : B →ₗ[R] B)
      (fun _ _ => rfl) n = 𝟙 (torFunctor R S B n) := by
  rw [torCoefficientTransformation, tensorCoefficientTransformation_id,
    NatTrans.leftDerived_id]
  rfl

/-- The native derived composition law applies to the earned coefficient maps. -/
theorem torCoefficientTransformation_comp (n : ℕ) :
    torCoefficientTransformation R S B B' f hS n ≫
        torCoefficientTransformation R S B' B'' g hSg n =
      torCoefficientTransformation R S B B'' (g.comp f)
        (fun s b => (congrArg g (hS s b)).trans (hSg s (f b))) n := by
  change NatTrans.leftDerived (tensorCoefficientTransformation R S B B' f hS) n ≫
      NatTrans.leftDerived (tensorCoefficientTransformation R S B' B'' g hSg) n =
    NatTrans.leftDerived (tensorCoefficientTransformation R S B B'' (g.comp f)
      (fun s b => (congrArg g (hS s b)).trans (hSg s (f b)))) n
  rw [← NatTrans.leftDerived_comp, tensorCoefficientTransformation_comp]

/-- A genuine projective resolution computes the coefficient morphism using
its actual degreewise tensor map; no acyclicity or comparison is an input. -/
theorem torCoefficientTransformation_resolution (n : ℕ)
    {A : ModuleCat.{v} Rᵐᵒᵖ} (P : ProjectiveResolution A) :
    (torCoefficientTransformation R S B B' f hS n).app A =
      (P.isoLeftDerivedObj (tensorFunctor R S B) n).hom ≫
        (HomologicalComplex.homologyFunctor (ModuleCat.{v} Sᵐᵒᵖ)
          (ComplexShape.down ℕ) n).map
          ((NatTrans.mapHomologicalComplex
            (tensorCoefficientTransformation R S B B' f hS) (ComplexShape.down ℕ)).app P.complex) ≫
        (P.isoLeftDerivedObj (tensorFunctor R S B') n).inv :=
  ProjectiveResolution.leftDerived_app_eq
    (tensorCoefficientTransformation R S B B' f hS) P n

end Tor

end ModuleCat.BalancedTensorRight
