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
# Native tensor with an original restricted coefficient

For an actual commutative algebra map R → S and an arbitrary original
S-module M, the functor sends an R-module L to the literal S-module
M ⊗[R] L.  Its R-action is earned from the original S-action and the map.
All rings and both module carriers have independent universes.  No flatness,
projectivity, finite generation, Small, or extended-origin assumption is used.

Native cancellation identifies M ⊗[S] (S ⊗[R] L) with M ⊗[R] L as a raw
S-linear equivalence across worlds.  The categorical natural isomorphism
uses a displayed input height containing S, because the explicit S factor
otherwise raises the source carrier universe.  Original M is never replaced.

This is functor packaging of native heterobasic tensor maps and cancellation;
it adds no balanced quotient or tensor engine.  Native checks are unexecuted.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u w t v

namespace ModuleCat.TensorRestriction

variable (R : Type u) (S : Type w) [CommRing R] [CommRing S] [Algebra R S]
  (M : ModuleCat.{t} S)

/-- The original coefficient's R-action is its S-action through the structural map. -/
abbrev restrictModule : Module R M := Module.compHom M (algebraMap R S)

/-- The restricted action and original S-action form the native scalar tower. -/
abbrev restrictTower :
    letI : Module R M := restrictModule R S M
    IsScalarTower R S M := by
  letI : Module R M := restrictModule R S M
  exact IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

/-- Restricted R-scalars commute with the original S-scalars on the same coefficient. -/
abbrev restrictCommute :
    letI : Module R M := restrictModule R S M
    SMulCommClass R S M := by
  letI : Module R M := restrictModule R S M
  refine ⟨fun r s m => ?_⟩
  change (algebraMap R S r) • (s • m) = s • ((algebraMap R S r) • m)
  exact smul_comm (algebraMap R S r) s m

/-- The literal original coefficient tensor, with its earned outer S-action. -/
abbrev objAt (L : ModuleCat.{v} R) : ModuleCat.{max t v} S := by
  letI : Module R M := restrictModule R S M
  letI : IsScalarTower R S M := restrictTower R S M
  letI : SMulCommClass R S M := restrictCommute R S M
  exact ModuleCat.of S (M ⊗[R] L)

/-- The actual native heterobasic map, retaining the original coefficient first. -/
def mapAt {L L' : ModuleCat.{v} R} (f : L ⟶ L') :
    objAt R S M L ⟶ objAt R S M L' := by
  letI : Module R M := restrictModule R S M
  letI : IsScalarTower R S M := restrictTower R S M
  letI : SMulCommClass R S M := restrictCommute R S M
  exact ModuleCat.ofHom (TensorProduct.AlgebraTensorModule.lTensor S M f.hom)

/-- Native coefficient-first tensoring with independent module carrier worlds. -/
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

@[simp]
theorem functorAt_map_tmul {L L' : ModuleCat.{v} R} (f : L ⟶ L') (m : M) (l : L) :
    letI : Module R M := Module.compHom M (algebraMap R S)
    ((functorAt R S M).map f).hom (m ⊗ₜ[R] l) = m ⊗ₜ[R] f.hom l := by
  letI : Module R M := restrictModule R S M
  letI : IsScalarTower R S M := restrictTower R S M
  letI : SMulCommClass R S M := restrictCommute R S M
  rfl

/-- The original tensor functor is additive, not merely an object assignment. -/
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

/-- Raw native S-linear cancellation, valid with every ring and carrier world independent. -/
def cancellationLinearEquiv (L : ModuleCat.{v} R) :
    letI : Module R M := Module.compHom M (algebraMap R S)
    letI : IsScalarTower R S M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    letI : SMulCommClass R S M := restrictCommute R S M
    M ⊗[S] (S ⊗[R] L) ≃ₗ[S] M ⊗[R] L := by
  letI : Module R M := restrictModule R S M
  letI : IsScalarTower R S M := restrictTower R S M
  letI : SMulCommClass R S M := restrictCommute R S M
  exact TensorProduct.AlgebraTensorModule.cancelBaseChange R S S M L

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

@[simp]
theorem cancellationLinearEquiv_symm_tmul (L : ModuleCat.{v} R) (m : M) (l : L) :
    letI : Module R M := Module.compHom M (algebraMap R S)
    (cancellationLinearEquiv R S M L).symm (m ⊗ₜ[R] l) =
      m ⊗ₜ[S] ((1 : S) ⊗ₜ[R] l) := by
  letI : Module R M := restrictModule R S M
  letI : IsScalarTower R S M := restrictTower R S M
  letI : SMulCommClass R S M := restrictCommute R S M
  exact TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul R S S m l

/-- Categorical cancellation in its actual displayed common input height.
The coefficient M keeps its original independently specified carrier. -/
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

/-- The categorical inverse has the actual native original-carrier formula. -/
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

/-- An original S-linear coefficient map acts on the actual first tensor factor. -/
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

/-- The original coefficient map is natural in every actual R-linear input map. -/
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

/-- A native functor factory for arbitrary original coefficients, with no supplied right action. -/
def factory : ModuleCat.{t} S ⥤ (ModuleCat.{v} R ⥤ ModuleCat.{max t v} S) where
  obj := functorAt R S
  map := coefficientTransformation R S
  map_id _ := coefficientTransformation_id R S
  map_comp g h := coefficientTransformation_comp R S g h

end ModuleCat.TensorRestriction

end
