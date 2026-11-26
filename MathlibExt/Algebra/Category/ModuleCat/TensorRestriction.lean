/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.ModuleCat.TensorBifunctor
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Tensoring an R-module with an S-module coefficient

Let R → S be a commutative algebra map and M an S-module. Restrict the R-action on M along
that map, then form M ⊗_R L for each R-module L. The S-action is on the first factor. These
modules and maps form an additive functor in L, natural in S-linear coefficient maps M → N.

Base-change cancellation gives the S-linear equivalence M ⊗_S (S ⊗_R L) ≃ M ⊗_R L, sending m ⊗
(s ⊗ l) to (s·m) ⊗ l. Its inverse sends m ⊗ l to m ⊗ (1 ⊗ l). The raw equivalence permits
independent carrier heights; the categorical natural isomorphism uses input height max(w,v)
and output height max(w,t,v), retaining the S-ring and coefficient heights.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u w t v

namespace ModuleCat.TensorRestriction

variable (R : Type u) (S : Type w) [CommRing R] [CommRing S] [Algebra R S]
  (M : ModuleCat.{t} S)

/-- The restricted R-action on an S-coefficient module.

For an S-module M, define its R-module structure through algebraMap R S. -/
abbrev restrictModule : Module R M := Module.compHom M (algebraMap R S)

/-- The scalar tower of the restricted coefficient action.

The R-action obtained from R → S and the S-action on M satisfy IsScalarTower R S M. -/
abbrev restrictTower :
    letI : Module R M := restrictModule R S M
    IsScalarTower R S M := by
  letI : Module R M := restrictModule R S M
  exact IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

/-- The commuting scalar actions on the coefficient module.

The restricted R-action and the S-action on M commute because S is commutative. -/
abbrev restrictCommute :
    letI : Module R M := restrictModule R S M
    SMulCommClass R S M := by
  letI : Module R M := restrictModule R S M
  refine ⟨fun r s m => ?_⟩
  change (algebraMap R S r) • (s • m) = s • ((algebraMap R S r) • m)
  exact smul_comm (algebraMap R S r) s m

/-- The S-module obtained by tensoring a restricted coefficient.

For an R-module L, form M ⊗_R L with the S-action on M. Its carrier height is max(t,v), with t
the coefficient height and v the input height. -/
abbrev objAt (L : ModuleCat.{v} R) : ModuleCat.{max t v} S := by
  letI : Module R M := restrictModule R S M
  letI : IsScalarTower R S M := restrictTower R S M
  letI : SMulCommClass R S M := restrictCommute R S M
  exact ModuleCat.of S (M ⊗[R] L)

/-- The tensor map of an R-linear input morphism.

For f : L → L′, the S-linear map M ⊗_R L → M ⊗_R L′ acts by id_M ⊗ f. -/
def mapAt {L L' : ModuleCat.{v} R} (f : L ⟶ L') :
    objAt R S M L ⟶ objAt R S M L' := by
  letI : Module R M := restrictModule R S M
  letI : IsScalarTower R S M := restrictTower R S M
  letI : SMulCommClass R S M := restrictCommute R S M
  exact ModuleCat.ofHom (TensorProduct.AlgebraTensorModule.lTensor S M f.hom)

/-- The additive tensor functor with an S-module coefficient.

For fixed M, send L to M ⊗_R L and f to id_M ⊗ f, retaining the independent ring and module
heights. -/
abbrev functorAt : ModuleCat.{v} R ⥤ ModuleCat.{max t v} S where
  obj := objAt R S M
  map := mapAt R S M
  map_id L := by
    letI : Module R M := restrictModule R S M
    letI : IsScalarTower R S M := restrictTower R S M
    letI : SMulCommClass R S M := restrictCommute R S M
    apply ModuleCat.hom_ext
    exact TensorProduct.AlgebraTensorModule.lTensor_id
  map_comp f g := by
    letI : Module R M := restrictModule R S M
    letI : IsScalarTower R S M := restrictTower R S M
    letI : SMulCommClass R S M := restrictCommute R S M
    apply ModuleCat.hom_ext
    exact TensorProduct.AlgebraTensorModule.lTensor_comp g.hom f.hom

/-- The tensor functor on a pure tensor.

The map induced by f sends m ⊗ l to m ⊗ f(l). -/
@[simp]
theorem functorAt_map_tmul {L L' : ModuleCat.{v} R} (f : L ⟶ L') (m : M) (l : L) :
    letI : Module R M := Module.compHom M (algebraMap R S)
    ((functorAt R S M).map f).hom (m ⊗ₜ[R] l) = m ⊗ₜ[R] f.hom l := by
  letI : Module R M := restrictModule R S M
  letI : IsScalarTower R S M := restrictTower R S M
  letI : SMulCommClass R S M := restrictCommute R S M
  rfl

/-- Additivity of the restricted-coefficient tensor functor.

The functor L ↦ M ⊗_R L preserves addition of R-linear morphisms. -/
instance functorAt_additive : (functorAt R S M : ModuleCat.{v} R ⥤ _).Additive where
  map_add {L L' f g} := by
    letI : Module R M := restrictModule R S M
    letI : IsScalarTower R S M := restrictTower R S M
    letI : SMulCommClass R S M := restrictCommute R S M
    apply ModuleCat.hom_ext
    apply TensorProduct.AlgebraTensorModule.ext
    intro m l
    change m ⊗ₜ[R] (f.hom l + g.hom l) =
      (m ⊗ₜ[R] f.hom l) + (m ⊗ₜ[R] g.hom l)
    exact TensorProduct.tmul_add m (f.hom l) (g.hom l)

/-- The S-linear base-change cancellation equivalence.

For any input carrier height, M ⊗_S (S ⊗_R L) is S-linearly equivalent to M ⊗_R L through the
canonical cancellation map. -/
def cancellationLinearEquiv (L : ModuleCat.{v} R) :
    letI : Module R M := Module.compHom M (algebraMap R S)
    letI : IsScalarTower R S M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    letI : SMulCommClass R S M := restrictCommute R S M
    M ⊗[S] (S ⊗[R] L) ≃ₗ[S] M ⊗[R] L := by
  letI : Module R M := restrictModule R S M
  letI : IsScalarTower R S M := restrictTower R S M
  letI : SMulCommClass R S M := restrictCommute R S M
  exact TensorProduct.AlgebraTensorModule.cancelBaseChange R S S M L

/-- The forward cancellation formula on pure tensors.

The cancellation equivalence sends m ⊗_S (s ⊗_R l) to (s·m) ⊗_R l. -/
@[simp]
theorem cancellationLinearEquiv_tmul (L : ModuleCat.{v} R)
    (m : M) (s : S) (l : L) :
    letI : Module R M := Module.compHom M (algebraMap R S)
    cancellationLinearEquiv R S M L (m ⊗ₜ[S] (s ⊗ₜ[R] l)) =
      (s • m) ⊗ₜ[R] l := by
  letI : Module R M := restrictModule R S M
  letI : IsScalarTower R S M := restrictTower R S M
  letI : SMulCommClass R S M := restrictCommute R S M
  exact TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul R S S m l s

/-- The inverse cancellation formula on pure tensors.

The inverse cancellation equivalence sends m ⊗_R l to m ⊗_S (1 ⊗_R l). -/
@[simp]
theorem cancellationLinearEquiv_symm_tmul (L : ModuleCat.{v} R) (m : M) (l : L) :
    letI : Module R M := Module.compHom M (algebraMap R S)
    (cancellationLinearEquiv R S M L).symm (m ⊗ₜ[R] l) =
      m ⊗ₜ[S] ((1 : S) ⊗ₜ[R] l) := by
  letI : Module R M := restrictModule R S M
  letI : IsScalarTower R S M := restrictTower R S M
  letI : SMulCommClass R S M := restrictCommute R S M
  exact TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul R S S m l

/-- The natural categorical base-change cancellation.

For input R-module height max(w,v), scalar extension to S followed by tensoring with M is
naturally isomorphic to L ↦ M ⊗_R L, with common output height max(w,t,v). -/
def cancellationNatIso :
    (ModuleCat.extendScalars (algebraMap R S) :
        ModuleCat.{max w v} R ⥤ ModuleCat.{max w v} S) ⋙
        (ModuleCat.tensorBifunctorAt.{w, t, max w v} S).obj M ≅
      (functorAt R S M : ModuleCat.{max w v} R ⥤ ModuleCat.{max w t v} S) :=
  NatIso.ofComponents
    (fun L => by
      let f : R →+* S := algebraMap R S
      letI : Algebra R S := f.toAlgebra
      letI : Module R M := restrictModule R S M
      letI : IsScalarTower R S M := restrictTower R S M
      letI : SMulCommClass R S M := restrictCommute R S M
      exact LinearEquiv.toModuleIso (cancellationLinearEquiv R S M L))
    (by
      intro L L' f
      let φ : R →+* S := algebraMap R S
      letI : Algebra R S := φ.toAlgebra
      letI : Module R M := restrictModule R S M
      letI : IsScalarTower R S M := restrictTower R S M
      letI : SMulCommClass R S M := restrictCommute R S M
      apply ModuleCat.hom_ext
      change (TensorProduct.AlgebraTensorModule.cancelBaseChange R S S M L').toLinearMap ∘ₗ
          TensorProduct.AlgebraTensorModule.lTensor S M
            (TensorProduct.AlgebraTensorModule.lTensor S S f.hom) =
        TensorProduct.AlgebraTensorModule.lTensor S M f.hom ∘ₗ
          (TensorProduct.AlgebraTensorModule.cancelBaseChange R S S M L).toLinearMap
      exact (TensorProduct.AlgebraTensorModule.lTensor_comp_cancelBaseChange
        (R := R) (A := S) (B := S) (M := M) f.hom).symm)

/-- The inverse categorical cancellation on generators.

At L, the inverse natural comparison sends m ⊗_R l to m ⊗_S (1 ⊗_R l). -/
@[simp]
theorem cancellationNatIso_inv_tmul (L : ModuleCat.{max w v} R) (m : M) (l : L) :
    letI : Module R M := Module.compHom M (algebraMap R S)
    ((cancellationNatIso R S M).inv.app L).hom (m ⊗ₜ[R] l) =
      (let φ : R →+* S := algebraMap R S
       letI : Algebra R S := φ.toAlgebra
       m ⊗ₜ[S] ((1 : S) ⊗ₜ[R] l)) := by
  let φ : R →+* S := algebraMap R S
  letI : Algebra R S := φ.toAlgebra
  letI : Module R M := restrictModule R S M
  letI : IsScalarTower R S M := restrictTower R S M
  letI : SMulCommClass R S M := restrictCommute R S M
  exact TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul R S S m l

section Coefficients

variable {M} {N P : ModuleCat.{t} S}

/-- The tensor map of an S-linear coefficient morphism.

For g : M → N, the S-linear map M ⊗_R L → N ⊗_R L acts by g ⊗ id_L. -/
def coefficientMapAt (g : M ⟶ N) (L : ModuleCat.{v} R) :
    objAt R S M L ⟶ objAt R S N L := by
  letI : Module R M := restrictModule R S M
  letI : IsScalarTower R S M := restrictTower R S M
  letI : SMulCommClass R S M := restrictCommute R S M
  letI : Module R N := restrictModule R S N
  letI : IsScalarTower R S N := restrictTower R S N
  letI : SMulCommClass R S N := restrictCommute R S N
  exact ModuleCat.ofHom
    (TensorProduct.AlgebraTensorModule.map g.hom (LinearMap.id : L →ₗ[R] L))

/-- The coefficient tensor map on a pure tensor.

The map induced by g sends m ⊗ l to g(m) ⊗ l. -/
@[simp]
theorem coefficientMapAt_tmul (g : M ⟶ N) (L : ModuleCat.{v} R) (m : M) (l : L) :
    letI : Module R M := Module.compHom M (algebraMap R S)
    letI : Module R N := Module.compHom N (algebraMap R S)
    (coefficientMapAt R S g L).hom (m ⊗ₜ[R] l) = g.hom m ⊗ₜ[R] l := by
  letI : Module R M := restrictModule R S M
  letI : IsScalarTower R S M := restrictTower R S M
  letI : SMulCommClass R S M := restrictCommute R S M
  letI : Module R N := restrictModule R S N
  letI : IsScalarTower R S N := restrictTower R S N
  letI : SMulCommClass R S N := restrictCommute R S N
  rfl

/-- The natural tensor transformation of a coefficient map.

An S-linear g : M → N gives a natural transformation from M ⊗_R − to N ⊗_R −, whose components
are g ⊗ id. -/
abbrev coefficientTransformation (g : M ⟶ N) : functorAt R S M ⟶ functorAt R S N where
  app := coefficientMapAt R S g
  naturality {L L'} f := by
    letI : Module R M := restrictModule R S M
    letI : IsScalarTower R S M := restrictTower R S M
    letI : SMulCommClass R S M := restrictCommute R S M
    letI : Module R N := restrictModule R S N
    letI : IsScalarTower R S N := restrictTower R S N
    letI : SMulCommClass R S N := restrictCommute R S N
    apply ModuleCat.hom_ext
    apply TensorProduct.AlgebraTensorModule.ext
    intro m l
    rfl

/-- The coefficient transformation of an identity map.

The identity of M induces the identity natural transformation of M ⊗_R −. -/
@[simp]
theorem coefficientTransformation_id :
    coefficientTransformation R S (𝟙 M) = 𝟙 (functorAt R S M) := by
  apply NatTrans.ext
  funext L
  letI : Module R M := restrictModule R S M
  letI : IsScalarTower R S M := restrictTower R S M
  letI : SMulCommClass R S M := restrictCommute R S M
  apply ModuleCat.hom_ext
  apply TensorProduct.AlgebraTensorModule.ext
  intro m l
  rfl

/-- Composition of coefficient tensor transformations.

The transformation induced by g followed by h equals the transformation induced by the
composite g ≫ h. -/
theorem coefficientTransformation_comp (g : M ⟶ N) (h : N ⟶ P) :
    coefficientTransformation R S (g ≫ h) =
      coefficientTransformation R S g ≫ coefficientTransformation R S h := by
  apply NatTrans.ext
  funext L
  letI : Module R M := restrictModule R S M
  letI : IsScalarTower R S M := restrictTower R S M
  letI : SMulCommClass R S M := restrictCommute R S M
  letI : Module R N := restrictModule R S N
  letI : IsScalarTower R S N := restrictTower R S N
  letI : SMulCommClass R S N := restrictCommute R S N
  letI : Module R P := restrictModule R S P
  letI : IsScalarTower R S P := restrictTower R S P
  letI : SMulCommClass R S P := restrictCommute R S P
  apply ModuleCat.hom_ext
  apply TensorProduct.AlgebraTensorModule.ext
  intro m l
  rfl

end Coefficients

/-- The tensor bifunctor with S-coefficients and R-inputs.

Send an S-module M to the functor L ↦ M ⊗_R L, and an S-linear map to its coefficient tensor
transformation. -/
def factory : ModuleCat.{t} S ⥤ (ModuleCat.{v} R ⥤ ModuleCat.{max t v} S) where
  obj := functorAt R S
  map := coefficientTransformation R S
  map_id _ := coefficientTransformation_id R S
  map_comp g h := coefficientTransformation_comp R S g h

end ModuleCat.TensorRestriction

end
