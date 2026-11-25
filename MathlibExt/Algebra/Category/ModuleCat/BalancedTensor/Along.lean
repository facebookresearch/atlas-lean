/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Category.ModuleCat.BalancedTensor
public import MathlibExt.LinearAlgebra.TensorProduct.BalancedAlong
public import Mathlib.Algebra.Homology.Functor

/-!
# Naturality of balanced tensor maps under change of scalars

A scalar homomorphism and an equivariant coefficient map give a natural transformation between the
corresponding balanced tensor functors. Scalar restriction identifies the ground actions on the
variable left module. Prolongation gives the associated natural transformation on chain complexes.
-/

@[expose] public section
noncomputable section

open CategoryTheory

universe uk uR uS w z

namespace ModuleCat.BalancedTensor.Along

variable (k : Type uk) [CommRing k]
  {R : Type uR} {S : Type uS} [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  {M N : Type w} [AddCommGroup M] [AddCommGroup N] [Module k M] [Module k N]
  [Module Rᵐᵒᵖ M] [Module Sᵐᵒᵖ N]
  (φ : R →ₐ[k] S) (f : M →ₗ[k] N)
  (hf : ∀ r m, f (MulOpposite.op r • m) = MulOpposite.op (φ r) • f m)

local notation "Source" => ModuleCat.restrictScalars φ.toRingHom ⋙
  ModuleCat.BalancedTensor.functor k R M
local notation "Target" => ModuleCat.BalancedTensor.functor k S N

/--
The ground restriction-composition identity, with the algebra scalar law providing its ring-map
equality.
-/
def groundRestrictionIso :
    ModuleCat.restrictScalars.{z} φ.toRingHom ⋙ ModuleCat.restrictScalars (algebraMap k R) ≅
      ModuleCat.restrictScalars (algebraMap k S) :=
  (ModuleCat.restrictScalarsComp' (algebraMap k R) φ.toRingHom (algebraMap k S)
      (RingHom.ext fun c => (φ.commutes c).symm)).symm

/-- A pure balanced tensor before the change of scalars. -/
def sourceMk (Y : ModuleCat.{z} S) (m : M) (y : Y) : (Source).obj Y := by
  let RY := (ModuleCat.restrictScalars φ.toRingHom).obj Y
  letI : Module k RY := Module.compHom RY (algebraMap k R)
  exact TensorProduct.Balanced.mk k R M RY m y

/-- A pure balanced tensor after the change of scalars. -/
def targetMk (Y : ModuleCat.{z} S) (n : N) (y : Y) : (Target).obj Y := by
  letI : Module k Y := Module.compHom Y (algebraMap k S)
  exact TensorProduct.Balanced.mk k S N Y n y

/-- Scalar-changing coefficient map on a left module. -/
def component (Y : ModuleCat.{z} S) : (Source).obj Y ⟶ (Target).obj Y := by
  let RY := (ModuleCat.restrictScalars φ.toRingHom).obj Y
  letI : Module k RY := Module.compHom RY (algebraMap k R)
  letI : Module k Y := Module.compHom Y (algebraMap k S)
  let RK := (ModuleCat.restrictScalars (algebraMap k R)).obj RY
  let SK := (ModuleCat.restrictScalars (algebraMap k S)).obj Y
  letI : Module R RK := RY.isModule
  letI : Module S SK := Y.isModule
  let a : RK →ₗ[k] SK := ((groundRestrictionIso k φ).hom.app Y).hom
  exact ModuleCat.ofHom (TensorProduct.Balanced.mapAlong φ.toRingHom f a hf (by
    intro r y
    rfl))

/--
The coefficient is mapped and the left-module element is unchanged. The latter identity comes from
scalar restriction.
-/
theorem component_mk (Y : ModuleCat.{z} S) (m : M) (y : Y) :
    (component k φ f hf Y).hom (sourceMk k φ Y m y) = targetMk k Y (f m) y := by
  rfl

/-- The source tensor map retains the left-module morphism. -/
theorem sourceMk_map {Y Y' : ModuleCat.{z} S} (h : Y ⟶ Y') (m : M) (y : Y) :
    ((Source).map h).hom (sourceMk k φ Y m y) = sourceMk k φ Y' m (h.hom y) := by
  let RY := (ModuleCat.restrictScalars φ.toRingHom).obj Y
  let RY' := (ModuleCat.restrictScalars φ.toRingHom).obj Y'
  letI : Module k RY := Module.compHom RY (algebraMap k R)
  letI : Module k RY' := Module.compHom RY' (algebraMap k R)
  exact ModuleCat.BalancedTensor.map_mk k R M
    ((ModuleCat.restrictScalars φ.toRingHom).map h) m y

/-- The target tensor map likewise retains the morphism. -/
theorem targetMk_map {Y Y' : ModuleCat.{z} S} (h : Y ⟶ Y') (n : N) (y : Y) :
    ((Target).map h).hom (targetMk k Y n y) = targetMk k Y' n (h.hom y) := by
  letI : Module k Y := Module.compHom Y (algebraMap k S)
  letI : Module k Y' := Module.compHom Y' (algebraMap k S)
  exact ModuleCat.BalancedTensor.map_mk k S N h n y

/-- The scalar-changing balanced coefficient natural transformation. -/
def natTrans : Source ⟶ Target where
  app := component k φ f hf
  naturality {Y Y'} h := by
    apply ModuleCat.hom_ext
    let RY := (ModuleCat.restrictScalars φ.toRingHom).obj Y
    letI : Module k RY := Module.compHom RY (algebraMap k R)
    apply TensorProduct.Balanced.hom_ext
    intro m y
    let yS : Y := y
    have hSource := sourceMk_map k φ h m yS
    have hFirst := component_mk k φ f hf Y m yS
    have hSecond := component_mk k φ f hf Y' m (h.hom yS)
    have hTarget := targetMk_map k h (f m) yS
    change (component k φ f hf Y').hom
        (((Source).map h).hom (sourceMk k φ Y m yS)) =
      ((Target).map h).hom ((component k φ f hf Y).hom (sourceMk k φ Y m yS))
    exact (congrArg (component k φ f hf Y').hom hSource).trans
      (hSecond.trans (hTarget.symm.trans (congrArg ((Target).map h).hom hFirst).symm))

/-- The balanced tensor functor after scalar restriction is additive. -/
local instance source_additive : (Source).Additive := by
  let : (ModuleCat.BalancedTensor.functor k R M).Additive :=
    ModuleCat.BalancedTensor.additive k R M
  infer_instance

/-- The target balanced tensor functor is additive. -/
local instance target_additive : (Target).Additive := ModuleCat.BalancedTensor.additive k S N

/--
Applying the natural-transformation prolongation gives the scalar-changing coefficient map on
every chain complex.
-/
def chainNatTrans : (Source).mapHomologicalComplex (.down ℕ) ⟶
    (Target).mapHomologicalComplex (.down ℕ) :=
  (natTrans k φ f hf).mapHomologicalComplex (.down ℕ)

end ModuleCat.BalancedTensor.Along
