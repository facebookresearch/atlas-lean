/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AnalyticCoefficientPeriodScalars
public import MathlibExt.CategoryTheory.RingSheafModuleTensors

/-!
# Integral lisse modules with arbitrary finite Zp coefficients

The local constant model is the native sheafification of the section
presheaf Zhat(U) tensor[Zp] M0, where M0 is a finitely generated Zp
module. The scalar map is the original continuous constant function
followed by the original coefficient-sheafification unit. All restriction
maps are its actual semilinear coefficient maps. Torsion modules are
included; local freeness is a different predicate.

Source: Scholze arXiv:1205.3463v2, Definition8.1 and Theorem8.8.
Native Mathlib tensor/module/sheafification APIs retain
56a005855ea17e0b0958f73ec801ae140b0a1679, Apache 2.0.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.ProEtaleIntegralLisseModules

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open AnalyticTateAdicModels AnalyticProEtaleCoefficientSources AnalyticProObjectSites
open MathlibExt.CategoryTheory.RingedDerivedCoefficientOperations
open MathlibExt.CategoryTheory.RingSheafModuleTensors
open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime] (X : AnalyticAdicSpace p) (P : PointRealization p X)
  [HasSheafify (proTopology p X P) CommRingCat.{1}]

def continuousConstant (U : (ProEtaleSite p X)ᵒᵖ) :
    ℤ_[p] →+* (AnalyticCoefficientPeriodScalars.rawIntegral p X P).obj U where
  toFun c := ULift.up (ContinuousMap.const (P.functor.obj U.unop) c)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The original constant coefficient map, rather than a selected algebra structure. -/
def constantScalar (U : (ProEtaleSite p X)ᵒᵖ) : ℤ_[p] →+* (Zhat p X P).obj.obj U :=
  ((toSheafify (proTopology p X P)
    (AnalyticCoefficientPeriodScalars.rawIntegral p X P)).app U).hom.comp
      (continuousConstant p X P U)

theorem constantScalar_natural {U V : (ProEtaleSite p X)ᵒᵖ} (f : U ⟶ V) (c : ℤ_[p]) :
    ((Zhat p X P).obj.map f).hom (constantScalar p X P U c) = constantScalar p X P V c := by
  have hc : ((AnalyticCoefficientPeriodScalars.rawIntegral p X P).map f).hom
      (continuousConstant p X P U c) = continuousConstant p X P V c := by
    apply ULift.ext
    apply ContinuousMap.ext
    intro x
    rfl
  have h := congrArg (fun g ↦ g.hom (continuousConstant p X P U c))
    ((toSheafify (proTopology p X P)
      (AnalyticCoefficientPeriodScalars.rawIntegral p X P)).naturality f)
  change ((toSheafify (proTopology p X P)
      (AnalyticCoefficientPeriodScalars.rawIntegral p X P)).app V).hom
      (((AnalyticCoefficientPeriodScalars.rawIntegral p X P).map f).hom
        (continuousConstant p X P U c)) =
    ((Zhat p X P).obj.map f).hom
      (((toSheafify (proTopology p X P)
        (AnalyticCoefficientPeriodScalars.rawIntegral p X P)).app U).hom
          (continuousConstant p X P U c)) at h
  rw [hc] at h
  exact h.symm

local instance scalarAlgebra (U : (ProEtaleSite p X)ᵒᵖ) :
    Algebra ℤ_[p] ((Zhat p X P).obj.obj U) := (constantScalar p X P U).toAlgebra

def scalarRestriction {U V : (ProEtaleSite p X)ᵒᵖ} (f : U ⟶ V) :
    (Zhat p X P).obj.obj U →ₗ[ℤ_[p]] (Zhat p X P).obj.obj V where
  toFun := ((Zhat p X P).obj.map f).hom
  map_add' := map_add _
  map_smul' c a := by
    change ((Zhat p X P).obj.map f).hom (constantScalar p X P U c * a) =
      constantScalar p X P V c * ((Zhat p X P).obj.map f).hom a
    rw [map_mul, constantScalar_natural]

variable (M0 : ModuleCat.{1} ℤ_[p])

def tensorRestriction {U V : (ProEtaleSite p X)ᵒᵖ} (f : U ⟶ V) :
    ((Zhat p X P).obj.obj U ⊗[ℤ_[p]] M0) →ₛₗ[((Zhat p X P).obj.map f).hom]
      ((Zhat p X P).obj.obj V ⊗[ℤ_[p]] M0) where
  toFun := TensorProduct.map (scalarRestriction p X P f) (LinearMap.id : M0 →ₗ[ℤ_[p]] M0)
  map_add' := map_add _
  map_smul' a z := by
    induction z using TensorProduct.inductionOn with
    | tmul b m =>
      simp [TensorProduct.smul_tmul', TensorProduct.map_tmul, scalarRestriction, map_mul]
    | add z w hz hw => simp_all only [smul_add, map_add]

def constantObj (U : (ProEtaleSite p X)ᵒᵖ) : ModuleCat.{1} ((Zhat p X P).obj.obj U) :=
  ModuleCat.of ((Zhat p X P).obj.obj U) ((Zhat p X P).obj.obj U ⊗[ℤ_[p]] M0)

def constantMap {U V : (ProEtaleSite p X)ᵒᵖ} (f : U ⟶ V) : constantObj p X P M0 U ⟶
    (ModuleCat.restrictScalars ((moduleRing (Zhat p X P)).obj.map f).hom).obj
      (constantObj p X P M0 V) :=
  ModuleCat.ofHom
    (X := constantObj p X P M0 U)
    (Y := (ModuleCat.restrictScalars ((moduleRing (Zhat p X P)).obj.map f).hom).obj
      (constantObj p X P M0 V))
    { toFun := tensorRestriction p X P M0 f
      map_add' := map_add _
      map_smul' a z := (tensorRestriction p X P M0 f).map_smul' a z }

/-- The literal sectionwise scalar extension of the finite coefficient module. -/
def constantPresheaf : PresheafOfModules.{1} (moduleRing (Zhat p X P)).obj where
  obj := constantObj p X P M0
  map := constantMap p X P M0
  map_id U := by
    ext z
    induction z using TensorProduct.inductionOn with
    | tmul a m =>
      change ((Zhat p X P).obj.map (𝟙 U)).hom a ⊗ₜ[ℤ_[p]] m = a ⊗ₜ[ℤ_[p]] m
      rw [(Zhat p X P).obj.map_id]
      rfl
    | add z w hz hw => simp_all only [map_add]
  map_comp f g := by
    ext z
    induction z using TensorProduct.inductionOn with
    | tmul a m =>
      change ((Zhat p X P).obj.map (f ≫ g)).hom a ⊗ₜ[ℤ_[p]] m =
        ((Zhat p X P).obj.map g).hom (((Zhat p X P).obj.map f).hom a) ⊗ₜ[ℤ_[p]] m
      rw [(Zhat p X P).obj.map_comp]
      rfl
    | add z w hz hw => simp_all only [map_add]

variable [HasSheafify (proTopology p X P) AddCommGrpCat.{1}]
  [(proTopology p X P).WEqualsLocallyBijective AddCommGrpCat.{1}]

def constantModule : Modules (Zhat p X P) :=
  (moduleSheafification (Zhat p X P)).obj (constantPresheaf p X P M0)

variable [∀ U : ProEtaleSite p X, HasWeakSheafify ((proTopology p X P).over U) AddCommGrpCat.{1}]
  [∀ U : ProEtaleSite p X,
    ((proTopology p X P).over U).WEqualsLocallyBijective AddCommGrpCat.{1}]

/-- Definition8.1 on the SAME actual coefficient module, retaining finite torsion coefficients. -/
def IsLisse (N : Modules (Zhat p X P)) : Prop :=
  ∀ U : ProEtaleSite p X, ∃ S : Sieve U, S ∈ proTopology p X P U ∧
    ∀ (V : ProEtaleSite p X) (f : V ⟶ U), S f →
      ∃ M0 : ModuleCat.{1} ℤ_[p], Module.Finite ℤ_[p] M0 ∧
        Nonempty (N.over V ≅ (constantModule p X P M0).over V)

omit [∀ U : ProEtaleSite p X, HasWeakSheafify ((proTopology p X P).over U) AddCommGrpCat.{1}]
  [∀ U : ProEtaleSite p X, ((proTopology p X P).over U).WEqualsLocallyBijective AddCommGrpCat.{1}] in
theorem constantModule_isLisse [Module.Finite ℤ_[p] M0] :
    IsLisse p X P (constantModule p X P M0) := by
  intro U
  refine ⟨⊤, GrothendieckTopology.top_mem _ _, ?_⟩
  intro V f _
  exact ⟨M0, inferInstance, ⟨Iso.refl _⟩⟩

end MathlibExt.AlgebraicGeometry.ProEtaleIntegralLisseModules
