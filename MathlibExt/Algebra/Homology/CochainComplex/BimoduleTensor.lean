/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.FGModuleCat.BimoduleTensor
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# The original cochain tensor of a noncommutative bimodule

The degreewise functor is the canonical prolongation of the existing
left-module balanced tensor. Terms, differentials and cochain maps retain
the original quotient and its actual commuting outer action. Its raw
carrier formulas have independent ring, coefficient and module universes.

The existing integral Tor₁ criterion earns exactness in its original
common-universe module categories. Canonical preservation of kernels and
cokernels gives the homology comparison and preservation of actual
quasi-isomorphisms. No homology comparison or derived outcome is an input.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe uR uS uE uM u

attribute [local instance] ModuleCat.BalancedTensor.Left.additive

namespace ModuleCat

section OriginalCarriers

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]
  (E : Type uE) [AddCommGroup E] [Module S E] [Module Rᵐᵒᵖ E]
  [SMulCommClass S Rᵐᵒᵖ E]

/-- Apply the original module tensor in each original cochain degree. -/
abbrev bimoduleTensorCochain :
    CochainComplex (ModuleCat.{uM} R) ℤ ⥤
      CochainComplex (ModuleCat.{max uE uM} S) ℤ :=
  (BalancedTensor.Left.functor ℤ R S E).mapHomologicalComplex (.up ℤ)

/-- Every term is the existing balanced tensor object with its given outer S action. -/
theorem bimoduleTensorCochain_obj_X (K : CochainComplex (ModuleCat.{uM} R) ℤ) (j : ℤ) :
    ((bimoduleTensorCochain (S := S) E).obj K).X j =
      (BalancedTensor.Left.functor ℤ R S E).obj (K.X j) := rfl

/-- Every original differential is mapped by that same balanced tensor functor. -/
theorem bimoduleTensorCochain_obj_d (K : CochainComplex (ModuleCat.{uM} R) ℤ) (i j : ℤ) :
    ((bimoduleTensorCochain (S := S) E).obj K).d i j =
      (BalancedTensor.Left.functor ℤ R S E).map (K.d i j) := rfl

/-- Every original cochain-map component is the actual quotient map of the module component. -/
theorem bimoduleTensorCochain_map_f {K L : CochainComplex (ModuleCat.{uM} R) ℤ}
    (f : K ⟶ L) (j : ℤ) :
    ((bimoduleTensorCochain (S := S) E).map f).f j =
      (BalancedTensor.Left.functor ℤ R S E).map (f.f j) := rfl

/-- The original differential acts on the module factor of every ordered pure class. -/
theorem bimoduleTensorCochain_d_mk (K : CochainComplex (ModuleCat.{uM} R) ℤ)
    (i j : ℤ) (e : E) (x : K.X i) :
    letI : Module ℤ (K.X i) := Module.compHom (K.X i) (algebraMap ℤ R)
    letI : Module ℤ (K.X j) := Module.compHom (K.X j) (algebraMap ℤ R)
    (((bimoduleTensorCochain (S := S) E).obj K).d i j).hom
        (TensorProduct.Balanced.mk ℤ R E (K.X i) e x) =
      TensorProduct.Balanced.mk ℤ R E (K.X j) e ((K.d i j).hom x) := by
  let : Module ℤ (K.X i) := Module.compHom (K.X i) (algebraMap ℤ R)
  let : Module ℤ (K.X j) := Module.compHom (K.X j) (algebraMap ℤ R)
  exact BalancedTensor.Left.map_mk ℤ R S E (K.d i j) e x

/-- An actual original cochain map preserves the coefficient in every pure tensor component. -/
theorem bimoduleTensorCochain_map_mk {K L : CochainComplex (ModuleCat.{uM} R) ℤ}
    (f : K ⟶ L) (j : ℤ) (e : E) (x : K.X j) :
    letI : Module ℤ (K.X j) := Module.compHom (K.X j) (algebraMap ℤ R)
    letI : Module ℤ (L.X j) := Module.compHom (L.X j) (algebraMap ℤ R)
    (((bimoduleTensorCochain (S := S) E).map f).f j).hom
        (TensorProduct.Balanced.mk ℤ R E (K.X j) e x) =
      TensorProduct.Balanced.mk ℤ R E (L.X j) e ((f.f j).hom x) := by
  let : Module ℤ (K.X j) := Module.compHom (K.X j) (algebraMap ℤ R)
  let : Module ℤ (L.X j) := Module.compHom (L.X j) (algebraMap ℤ R)
  exact BalancedTensor.Left.map_mk ℤ R S E (f.f j) e x

/-- The original zero cochain remains zero under the actual degreewise tensor. -/
theorem bimoduleTensorCochain_zero :
    IsZero ((bimoduleTensorCochain (R := R) (S := S) E).obj
      (0 : CochainComplex (ModuleCat.{uM} R) ℤ)) :=
  (bimoduleTensorCochain (R := R) (S := S) E).map_isZero (isZero_zero _)

end OriginalCarriers

section RightFlat

variable {R S : Type u} [Ring R] [Ring S]
  (E : Type u) [AddCommGroup E] [Module S E] [Module Rᵐᵒᵖ E]
  [SMulCommClass S Rᵐᵒᵖ E]
  (hE : ∀ N : ModuleCat.{u} R,
    IsZero (((BalancedTensor.torFirst R 1).obj (ModuleCat.of Rᵐᵒᵖ E)).obj N))

include hE

/-- The canonical right-flatness input earns preservation of the original module homology. -/
theorem bimoduleTensor_preservesHomology :
    (BalancedTensor.Left.functor ℤ R S E :
      ModuleCat.{u} R ⥤ ModuleCat.{u} S).PreservesHomology := by
  let F : ModuleCat.{u} R ⥤ ModuleCat.{u} S := BalancedTensor.Left.functor ℤ R S E
  let : PreservesFiniteLimits F := bimoduleTensor_preservesFiniteLimits_of_torFirst_one E hE
  let : PreservesFiniteColimits F := bimoduleTensor_preservesFiniteColimits E
  infer_instance

/-- Homology of the actual tensor cochain is the actual tensor of its original homology. -/
def bimoduleTensorCochainHomologyIso (K : CochainComplex (ModuleCat.{u} R) ℤ) (j : ℤ) :
    ((bimoduleTensorCochain (S := S) E).obj K).homology j ≅
      (BalancedTensor.Left.functor ℤ R S E).obj (K.homology j) := by
  let F : ModuleCat.{u} R ⥤ ModuleCat.{u} S := BalancedTensor.Left.functor ℤ R S E
  let : F.PreservesHomology := bimoduleTensor_preservesHomology E hE
  exact (K.sc j).mapHomologyIso F

/-- The original homology square is natural for every actual original cochain map. -/
theorem bimoduleTensorCochainHomologyIso_hom_naturality
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) (j : ℤ) :
    HomologicalComplex.homologyMap ((bimoduleTensorCochain (S := S) E).map f) j ≫
        (bimoduleTensorCochainHomologyIso E hE L j).hom =
      (bimoduleTensorCochainHomologyIso E hE K j).hom ≫
        (BalancedTensor.Left.functor ℤ R S E).map (HomologicalComplex.homologyMap f j) := by
  let F : ModuleCat.{u} R ⥤ ModuleCat.{u} S := BalancedTensor.Left.functor ℤ R S E
  let : F.PreservesHomology := bimoduleTensor_preservesHomology E hE
  exact ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (.up ℤ) j).map f) F

/-- Exact tensor preserves a quasi-isomorphism at each original integer degree. -/
theorem bimoduleTensorCochain_quasiIsoAt
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) (j : ℤ) [QuasiIsoAt f j] :
    QuasiIsoAt ((bimoduleTensorCochain (S := S) E).map f) j := by
  let F : ModuleCat.{u} R ⥤ ModuleCat.{u} S := BalancedTensor.Left.functor ℤ R S E
  let : F.PreservesHomology := bimoduleTensor_preservesHomology E hE
  exact HomologicalComplex.quasiIsoAt_map_of_preservesHomology f F j

/-- The actual right-flat tensor preserves every actual original quasi-isomorphism. -/
theorem bimoduleTensorCochain_quasiIso
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) [QuasiIso f] :
    QuasiIso ((bimoduleTensorCochain (S := S) E).map f) := by
  let F : ModuleCat.{u} R ⥤ ModuleCat.{u} S := BalancedTensor.Left.functor ℤ R S E
  let : F.PreservesHomology := bimoduleTensor_preservesHomology E hE
  exact HomologicalComplex.quasiIso_map_of_preservesHomology f F

end RightFlat

end ModuleCat

end
