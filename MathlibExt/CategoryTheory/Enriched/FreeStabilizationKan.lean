/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.FreeStabilizationMapping
import MathlibExt.CategoryTheory.Enriched.LeftKanFreeComparison

/-!
# Free stabilization maps under enriched Kan extension

Expresses stabilization as free extension of its coefficient and computes its enriched components. With the required weighted coends, the Kan/free comparison preserves every stabilization and coefficient map, including the unit square and inverse comparison.
-/

set_option autoImplicit false
noncomputable section
universe uV vV uA uB

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonoidalClosed

namespace HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.CurrentFree

open CategoryTheory.EnrichedFunctorCat

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]
  {B : Type uB} [EnrichedCategory V B]

/-- The original stabilization is the original free extension of its complete coefficient. -/
theorem stabilization_eq_extend (a b : A) (K : V) (D : K ⟶ (a ⟶[V] b)) :
    stabilization a b K D =
      Free.extend b K (Free.object a (𝟙_ V)) (D ≫ (λ_ (a ⟶[V] b)).inv) := by
  apply (Free.homEquiv b K (Free.object a (𝟙_ V))).injective
  change Free.evaluate b K (Free.object a (𝟙_ V)) (stabilization a b K D) =
    Free.evaluate b K (Free.object a (𝟙_ V))
      (Free.extend b K (Free.object a (𝟙_ V)) (D ≫ (λ_ (a ⟶[V] b)).inv))
  rw [Free.evaluate_extend]
  have h := stabilization_adjunct a b K D
  rw [Free.adjunction_homEquiv] at h
  exact h

/-- Evaluate the same actual stabilization through the original free Hom correspondence. -/
theorem stabilization_evaluate (a b : A) (K : V) (D : K ⟶ (a ⟶[V] b)) :
    Free.evaluate b K (Free.object a (𝟙_ V)) (stabilization a b K D) =
      D ≫ (λ_ (a ⟶[V] b)).inv := by
  have h := stabilization_adjunct a b K D
  rw [Free.adjunction_homEquiv] at h
  exact h

/-- Every component uses the complete original coefficient and enriched composition action. -/
theorem stabilization_component (a b c : A) (K : V) (D : K ⟶ (a ⟶[V] b)) :
    component (stabilization a b K D) c =
      ((D ≫ (λ_ (a ⟶[V] b)).inv) ⊗ₘ 𝟙 (b ⟶[V] c)) ≫
        Free.action a (𝟙_ V) b c := by
  rw [stabilization_eq_extend, Free.extend_component]
  exact congrArg (fun g => ((D ≫ (λ_ (a ⟶[V] b)).inv) ⊗ₘ 𝟙 (b ⟶[V] c)) ≫ g)
    (MonoidalClosed.uncurry_curry _)

/-- Arbitrary coefficient precomposition preserves the entire original stabilization. -/
theorem stabilization_coefficient (a b : A) {K L : V} (c : K ⟶ L)
    (D : L ⟶ (a ⟶[V] b)) :
    Free.coefficientMap b c ≫ stabilization a b L D = stabilization a b K (c ≫ D) := by
  rw [stabilization_eq_extend, stabilization_eq_extend]
  exact (Free.extend_precomp b (Free.object a (𝟙_ V)) c
    (D ≫ (λ_ (a ⟶[V] b)).inv)).symm.trans
      (congrArg (Free.extend b K (Free.object a (𝟙_ V))) (Category.assoc _ _ _).symm)

variable (j : EnrichedFunctor V A B)

/-- The complete original index Hom map preserves the actual stabilization source and target. -/
theorem stabilization_homTransport (a b : A) (K : V) (D : K ⟶ (a ⟶[V] b)) :
    stabilization a b K D ≫ FreeHomTransport.map j a (𝟙_ V) =
      FreeHomTransport.map j b K ≫
        restrictionMap j (stabilization (j.obj a) (j.obj b) K (D ≫ j.map a b)) := by
  apply (Free.homEquiv b K (restrictionObject j (Free.object (j.obj a) (𝟙_ V)))).injective
  change Free.evaluate b K (restrictionObject j (Free.object (j.obj a) (𝟙_ V)))
      (stabilization a b K D ≫ FreeHomTransport.map j a (𝟙_ V)) =
    Free.evaluate b K (restrictionObject j (Free.object (j.obj a) (𝟙_ V)))
      (FreeHomTransport.map j b K ≫
        restrictionMap j (stabilization (j.obj a) (j.obj b) K (D ≫ j.map a b)))
  rw [Free.evaluate_postcomp, stabilization_evaluate, evaluation_map,
    FreeHomTransport.map_component, FreeHomTransport.evaluate_map, stabilization_evaluate]
  change (D ≫ (λ_ (a ⟶[V] b)).inv) ≫ (𝟙_ V ◁ j.map a b) =
    (D ≫ j.map a b) ≫ (λ_ (j.obj a ⟶[V] j.obj b)).inv
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun q => D ≫ q) (leftUnitor_inv_naturality (j.map a b)).symm).trans
      (Category.assoc _ _ _).symm)

omit [BraidedCategory V] [MonoidalClosed V] in
/-- The original whole coefficient equation also preserves both complete unitor factors. -/
theorem stabilization_unitCoefficient (a b : A) {K L : V} (c : K ⟶ L)
    (D : K ⟶ (a ⟶[V] b)) (E : L ⟶ (j.obj a ⟶[V] j.obj b))
    (h : D ≫ j.map a b = c ≫ E) :
    (D ≫ (λ_ (a ⟶[V] b)).inv) ≫ (𝟙_ V ◁ j.map a b) =
      (c ≫ E) ≫ (λ_ (j.obj a ⟶[V] j.obj b)).inv := by
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun q => D ≫ q) (leftUnitor_inv_naturality (j.map a b)).symm).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun q => q ≫ (λ_ (j.obj a ⟶[V] j.obj b)).inv) h)))

variable
  [∀ (F : EnrichedFunctorCat V A) (b : B),
    HasCoproduct (Enriched.weightedCoend.relations (leftKanWeight j b) F.toEnrichedFunctor)]
  [∀ (F : EnrichedFunctorCat V A) (b : B),
    HasCoproduct (Enriched.weightedCoend.objects (leftKanWeight j b) F.toEnrichedFunctor)]
  [∀ (F : EnrichedFunctorCat V A) (b : B),
    HasCoequalizer (Enriched.weightedCoend.leftMap (leftKanWeight j b) F.toEnrichedFunctor)
      (Enriched.weightedCoend.rightMap (leftKanWeight j b) F.toEnrichedFunctor)]

/-- The genuine Kan/free comparison preserves the full original stabilization map. -/
theorem stabilization_kan (a b : A) (K : V) (D : K ⟶ (a ⟶[V] b)) :
    (leftKan j).map (stabilization a b K D) ≫ LeftKanFreeComparison.hom j a (𝟙_ V) =
      LeftKanFreeComparison.hom j b K ≫
        stabilization (j.obj a) (j.obj b) K (D ≫ j.map a b) := by
  apply (leftKanHomEquiv j (Free.object b K) (Free.object (j.obj a) (𝟙_ V))).injective
  rw [leftKanHomEquiv_naturality_left, leftKanHomEquiv_naturality_right,
    leftKanHomEquiv_apply, leftKanHomEquiv_apply]
  change stabilization a b K D ≫
      (leftKanUnit j (Free.object a (𝟙_ V)) ≫
        restrictionMap j (LeftKanFreeComparison.hom j a (𝟙_ V))) =
    (leftKanUnit j (Free.object b K) ≫ restrictionMap j (LeftKanFreeComparison.hom j b K)) ≫
      restrictionMap j (stabilization (j.obj a) (j.obj b) K (D ≫ j.map a b))
  rw [LeftKanFreeComparison.hom_unit, LeftKanFreeComparison.hom_unit]
  exact stabilization_homTransport j a b K D

/-- All coefficients of the original stabilization retain the entire Kan comparison square. -/
theorem stabilization_kan_coefficient (a b : A) {K L : V} (c : K ⟶ L)
    (D : K ⟶ (a ⟶[V] b)) (E : L ⟶ (j.obj a ⟶[V] j.obj b))
    (h : D ≫ j.map a b = c ≫ E) :
    (leftKan j).map (stabilization a b K D) ≫ LeftKanFreeComparison.hom j a (𝟙_ V) =
      LeftKanFreeComparison.hom j b K ≫ Free.coefficientMap (j.obj b) c ≫
        stabilization (j.obj a) (j.obj b) L E := by
  have hk := stabilization_kan j a b K D
  have hc := stabilization_coefficient (j.obj a) (j.obj b) c E
  exact hk.trans ((congrArg
    (fun q => LeftKanFreeComparison.hom j b K ≫ stabilization (j.obj a) (j.obj b) K q) h).trans
      (congrArg (fun q => LeftKanFreeComparison.hom j b K ≫ q) hc.symm))

/-- The original unit retains both source factors and the complete target stabilization. -/
theorem stabilization_unit_square (a b : A) (K : V) (D : K ⟶ (a ⟶[V] b)) :
    stabilization a b K D ≫ leftKanUnit j (Free.object a (𝟙_ V)) ≫
        restrictionMap j (LeftKanFreeComparison.hom j a (𝟙_ V)) =
      leftKanUnit j (Free.object b K) ≫ restrictionMap j (LeftKanFreeComparison.hom j b K) ≫
        restrictionMap j (stabilization (j.obj a) (j.obj b) K (D ≫ j.map a b)) := by
  calc
    _ = stabilization a b K D ≫ FreeHomTransport.map j a (𝟙_ V) :=
      congrArg (fun q => stabilization a b K D ≫ q) (LeftKanFreeComparison.hom_unit j a (𝟙_ V))
    _ = FreeHomTransport.map j b K ≫
        restrictionMap j (stabilization (j.obj a) (j.obj b) K (D ≫ j.map a b)) :=
      stabilization_homTransport j a b K D
    _ = _ := by rw [← Category.assoc, LeftKanFreeComparison.hom_unit]

/-- The complete inverse Kan/free map also preserves every original stabilization. -/
theorem stabilization_kan_inverse (a b : A) (K : V) (D : K ⟶ (a ⟶[V] b)) :
    stabilization (j.obj a) (j.obj b) K (D ≫ j.map a b) ≫
        LeftKanFreeComparison.inv j a (𝟙_ V) =
      LeftKanFreeComparison.inv j b K ≫ (leftKan j).map (stabilization a b K D) := by
  apply (cancel_mono (LeftKanFreeComparison.iso j a (𝟙_ V)).hom).1
  rw [LeftKanFreeComparison.iso_hom, Category.assoc,
    LeftKanFreeComparison.inv_hom_id, Category.comp_id,
    Category.assoc, stabilization_kan, ← Category.assoc,
    LeftKanFreeComparison.inv_hom_id, Category.id_comp]

end HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.CurrentFree




#lint only unusedArguments
