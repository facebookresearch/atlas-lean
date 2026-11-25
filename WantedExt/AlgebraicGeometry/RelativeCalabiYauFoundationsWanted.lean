/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.CategoryTheory.DGMoritaCospanModels
public import MathlibExt.CategoryTheory.DGModuleDiagramModels

/-!
# Wanted actual trace, duality and relative-CY construction foundations

These requests use the complete native DG bar/path/product formulas,
actual projective modules and their unit-normalized adjunctions. They
assemble shared objects and maps; no constructor below returns a glued
Calabi-Yau structure or assumes its nondegeneracy.

Source: Brav--Dyckerhoff, arXiv:1606.00619v1, §§2--4 and6;
Keller, Deriving DG categories, §§2--3; Hovey, Model Categories, §5.
-/

namespace WantedExt.AlgebraicGeometry.RelativeCalabiYauFoundationsWanted

open CategoryTheory
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.PerfectDGModuleModels
open MathlibExt.CategoryTheory.CosimplicialDGMappingModels
open MathlibExt.CategoryTheory.DGScalarExtensionModels
open MathlibExt.CategoryTheory.DGBimoduleEnvelopingModels
open MathlibExt.CategoryTheory.DGBarDiagonalModels
open MathlibExt.CategoryTheory.DGCalabiYauMapModels
open MathlibExt.CategoryTheory.DGModuleConeShiftModels
open MathlibExt.CategoryTheory.DGBimodulePushforwardModels
open MathlibExt.CategoryTheory.DGRelativeCalabiYauModels
open MathlibExt.CategoryTheory.DGMoritaCospanModels
open MathlibExt.CategoryTheory.DGModuleDiagramModels
open MathlibExt.Algebra.Homology.DGCategoryCyclicBarModels
open MathlibExt.Algebra.Homology.DGCategoryTraceModels
open MathlibExt.Algebra.Homology.RelativeCyclicGluing
open CochainComplex.HomComplex

universe u

/-- Assemble the actual all-object cyclic Hom bar, with its fixed faces, units and rotation. -/
def_wanted dg_category_cyclic_bar (k : Type u) [Field k] (C : DGCat k) : CyclicBarModel C

/-- Assemble the actual direct-sum Hochschild trace with its fixed differential. -/
def_wanted dg_category_hochschild_trace (k : Type u) [Field k] (C : DGCat k) : TraceTotalModel C

/-- Construct the actual Connes mixed map on that same all-object bar total. -/
def_wanted dg_category_mixed_trace (k : Type u) [Field k] (C : DGCat k) : TraceMixedModel C

/-- Assemble the full source [[u]] completed product, retaining every coefficient and differential. -/
def_wanted dg_category_negative_trace (k : Type u) [Field k] (C : DGCat k)
    (M : TraceMixedModel C) : NegativeTraceModel M

/-- A DG functor induces the fixed trace map on every actual bar tensor. -/
def_wanted dg_category_trace_map (k : Type u) [Field k] (C D : DGCat k) (f : C ⟶ D)
    (M : TraceMixedModel C) (N : TraceMixedModel D) : TraceMapModel f M N

/-- Complete the corresponding native map on every negative-cyclic coefficient. -/
def_wanted dg_category_negative_trace_map (k : Type u) [Field k] (C D : DGCat k)
    (f : C ⟶ D) (M : TraceMixedModel C) (N : TraceMixedModel D)
    (F : TraceMapModel f M N) (P : NegativeTraceModel M) (Q : NegativeTraceModel N) :
  NegativeTraceMapModel F P Q

/-- The source forgetful cochain map is the fixed u^0 coefficient projection. -/
def_wanted dg_category_negative_projection (k : Type u) [Field k] (C : DGCat k)
    (M : TraceMixedModel C) (N : NegativeTraceModel M) : NegativeProjectionModel N

/-- Assemble the actual trace/product maps as a coherent coefficient functor. -/
def_wanted dg_category_negative_trace_system (k : Type u) [Field k] : NegativeTraceSystem k

/-- Scalar DG tensors retain the native pointwise values and every signed homogeneous action. -/
def_wanted scalar_tensor_dg_module (k : Type u) [Field k] (C : DGCat k)
    (K : Cochains k) (M : RightModule k C) : ScalarTensorModuleModel K M

/-- Every actual path word is a scalar free module on its enveloping representable. -/
def_wanted dg_free_diagonal_system (k : Type u) [Field k] (C : DGCat k) : FreeDiagonalSystem C

/-- Construct the projective diagonal from the fixed path differential, augmentation and all actions. -/
def_wanted dg_bar_diagonal (k : Type u) [Field k] (C : DGCat k)
    (D : EnvelopingModuleModel (diagonal C)) (F : FreeDiagonalSystem C) : BarDiagonalModel D F

/-- The inverse dualizing module is the actual bar-to-representable Hom with its fixed action. -/
def_wanted dg_inverse_dualizing_module (k : Type u) [Field k] (C : DGCat k)
    (D : EnvelopingModuleModel (diagonal C)) (F : FreeDiagonalSystem C) (P : BarDiagonalModel D F) :
  InverseDualModel P

/-- Assemble the class-to-bimodule trace map from the bar evaluation of each cyclic word with the
identity of its distinguished object appended. -/
def_wanted dg_trace_evaluation (k : Type u) [Field k] (C : DGCat k)
    (D : EnvelopingModuleModel (diagonal C)) (F : FreeDiagonalSystem C)
    (P : BarDiagonalModel D F) (I : InverseDualModel P) (T : TraceMixedModel C) :
  TraceEvaluationModel P I T

/-- Source equation3.4 is duality for the actual perfect diagonal, with smoothness explicit. -/
theorem_wanted smooth_dg_trace_duality (k : Type u) [Field k] (C : DGCat k)
    (D : EnvelopingModuleModel (diagonal C)) (h : IsHomologicallySmooth C D)
    (F : FreeDiagonalSystem C) (P : BarDiagonalModel D F) (I : InverseDualModel P)
    (T : TraceMixedModel C) (E : TraceEvaluationModel P I T) : QuasiIso E.comparison

/-- Extract the fixed degree -n module map from the actual negative-cyclic class. -/
def_wanted negative_cyclic_left_cy_map (k : Type u) [Field k] (C : DGCat k)
    (D : EnvelopingModuleModel (diagonal C)) (F : FreeDiagonalSystem C)
    (P : BarDiagonalModel D F) (I : InverseDualModel P) (T : TraceMixedModel C)
    (E : TraceEvaluationModel P I T) (N : NegativeTraceModel T) (R : NegativeProjectionModel N)
    (n : ℤ) (a : NegativeCYClass N n) : LeftCYMapModel E R n a

/-- The projective module shift has every value and all homogeneous actions fixed. -/
def_wanted dg_module_shift (k : Type u) [Field k] (C : DGCat k)
    (M : DGDerivedModules k C) (n : ℤ) : CofibrantShiftModel M n

/-- The projective module cone retains its actual native cochain matrix in every point and arrow. -/
def_wanted dg_module_cone (k : Type u) [Field k] (C : DGCat k)
    (M N : DGDerivedModules k C) (f : M.obj ⟶ N.obj) : CofibrantConeModel M N f

/-- Assemble the literal closed cochain as the actual module map to its fixed shift. -/
def_wanted shifted_dg_module_map (k : Type u) [Field k] (C : DGCat k)
    (M N : RightModule k C) (n : ℤ) (a : DGHom k n M N)
    (h : dgDifferential k n a = 0) (S : ModuleShiftModel N n) : ShiftedModuleMapModel n a h S

/-- A projective enveloping module's actual left dual retains all representable values and actions. -/
def_wanted dg_module_left_dual (k : Type u) [Field k] (C : DGCat k)
    (M : DGDerivedModules k (enveloping C C)) : ModuleLeftDualModel C M

/-- The actual DG functor maps every bar path before the induction counit is formed. -/
def_wanted dg_bar_restriction_map (k : Type u) [Field k] (A B : DGCat k) (f : A ⟶ B)
    (T : EnvelopingMap f) (R : RestrictionModel T.functor)
    (DA : EnvelopingModuleModel (diagonal A)) (DB : EnvelopingModuleModel (diagonal B))
    (FA : FreeDiagonalSystem A) (FB : FreeDiagonalSystem B)
    (PA : BarDiagonalModel DA FA) (PB : BarDiagonalModel DB FB) :
  BarRestrictionMapModel f T R PA PB

/-- The counit is the same all-degree induction-adjunction transpose of that actual bar map. -/
def_wanted dg_bar_counit (k : Type u) [Field k] (A B : DGCat k) (f : A ⟶ B)
    (T : EnvelopingMap f) (R : RestrictionModel T.functor) (L : ExtensionModel T.functor R)
    (DA : EnvelopingModuleModel (diagonal A)) (DB : EnvelopingModuleModel (diagonal B))
    (FA : FreeDiagonalSystem A) (FB : FreeDiagonalSystem B)
    (PA : BarDiagonalModel DA FA) (PB : BarDiagonalModel DB FB)
    (F : BarRestrictionMapModel f T R PA PB) : BarCounitModel L F

/-- Restriction of the actual representable uses both native DG Hom-factor maps. -/
def_wanted dg_representable_restriction (k : Type u) [Field k] (A B : DGCat k) (f : A ⟶ B)
    (T : EnvelopingMap f) (R : RestrictionModel T.functor) (x : A) (y : Aᵒᵖ) :
  RepresentableRestrictionMapModel f T R x y

/-- Source Lemma4.2 supplies the actual unit-normalized left-duality base-change mate. -/
def_wanted smooth_dg_duality_base_change (k : Type u) [Field k] (A B : DGCat k) (f : A ⟶ B)
    (T : EnvelopingMap f) (R : RestrictionModel T.functor) (L : ExtensionModel T.functor R)
    (DA : EnvelopingModuleModel (diagonal A)) (h : IsHomologicallySmooth A DA)
    (FA : FreeDiagonalSystem A) (PA : BarDiagonalModel DA FA) (IA : InverseDualModel PA)
    (J : ModuleLeftDualModel B (pushedDiagonal L PA)) : DualBaseChangeModel L PA IA J

/-- The actual dual counit is normalized by Hom precomposition on every representable. -/
def_wanted dg_dual_counit (k : Type u) [Field k] (A B : DGCat k) (f : A ⟶ B)
    (T : EnvelopingMap f) (R : RestrictionModel T.functor) (L : ExtensionModel T.functor R)
    (DA : EnvelopingModuleModel (diagonal A)) (DB : EnvelopingModuleModel (diagonal B))
    (FA : FreeDiagonalSystem A) (FB : FreeDiagonalSystem B)
    (PA : BarDiagonalModel DA FA) (PB : BarDiagonalModel DB FB)
    (F : BarRestrictionMapModel f T R PA PB) (c : BarCounitModel L F)
    (IB : InverseDualModel PB) (J : ModuleLeftDualModel B (pushedDiagonal L PA)) :
  DualCounitModel L c IB J

/-- The common category-level trace/dual construction data contain no Calabi-Yau condition. -/
def_wanted dg_cy_category_data (k : Type u) [Field k] (S : NegativeTraceSystem k)
    (C : DGCat k) : CYCategoryData S C

/-- The whole-diagram replacement is projective in the actual small diagram category. -/
def_wanted dg_module_diagram_projective_replacement (k : Type u) [Field k]
    (C : DGCat k) (J : Type u) [Category.{u} J] (D : J ⥤ RightModule k C) :
  ProjectiveDiagramReplacement D

/-- Construct the actual coherent source DG frames used by Morita mapping-space tests. -/
def_wanted dg_category_frame_system (k : Type u) [Field k] : DGFrameSystem k

/-- The source coproduct has its exact object set, fully faithful inclusions and zero cross Hom. -/
def_wanted dg_category_coproduct (k : Type u) [Field k] (A B : DGCat k) : DGCoproductModel A B

/-- The combined DG functor is fixed on both actual coproduct inclusions. -/
def_wanted dg_category_coproduct_functor (k : Type u) [Field k] (A B X : DGCat k)
    (P : DGCoproductModel A B) (f : A ⟶ X) (g : B ⟶ X) : CoproductFunctorModel P f g

/-- The full [[u]] trace of the actual coproduct splits on its native inclusion maps. -/
def_wanted dg_negative_coproduct (k : Type u) [Field k] (A B : DGCat k)
    (S : NegativeTraceSystem k) (P : DGCoproductModel A B) : NegativeCoproductModel S P

/-- Rectify the general cospan through all three actual augmented source objects and maps. -/
def_wanted dg_cospan_resolution (k : Type u) [Field k] (B X Y : DGCat k)
    (f : B ⟶ X) (g : B ⟶ Y) : CospanResolution f g

/-- The resolved cospan has the full actual Morita homotopy pushout comparison. -/
def_wanted dg_morita_cospan_pushout (k : Type u) [Field k] (R : DGFrameSystem k)
    (B X Y : DGCat k) (f : B ⟶ X) (g : B ⟶ Y) (P : CospanResolution f g) :
  MoritaPushoutModel R P.resolvedF P.resolvedG

/-- The source coefficient gluing map is assembled from its fixed signed cone-degree blocks. -/
def_wanted relative_negative_cyclic_gluing (k : Type u) [Field k]
    (A B C X Y Z : Cochains k) (e : A ⟶ X) (f : B ⟶ X) (g : B ⟶ Y) (h : C ⟶ Y)
    (i : X ⟶ Z) (j : Y ⟶ Z) (comm : f ≫ i = g ≫ j) : CochainGluingModel e f g h i j comm

/-- Construct the actual counit-cone objects and target shifts, with no relative class assumption. -/
def_wanted relative_cy_cone_context (k : Type u) [Field k] (A B : DGCat k)
    (S : NegativeTraceSystem k) (f : A ⟶ B) (DA : CYCategoryData S A) (DB : CYCategoryData S B)
    (F : RelativeCYContext S f DA DB) (n : ℤ) : RelativeConeContext F n

/-- The relative class gives its actual boundary, null-homotopy and fixed counit-cone maps. -/
def_wanted relative_cy_class_maps (k : Type u) [Field k] (A B : DGCat k)
    (S : NegativeTraceSystem k) (f : A ⟶ B) (DA : CYCategoryData S A) (DB : CYCategoryData S B)
    (F : RelativeCYContext S f DA DB) (n : ℤ) (a : RelativeNegativeClass S f n)
    (C : RelativeConeContext F n) : RelativeCYMapModel F n a C

end WantedExt.AlgebraicGeometry.RelativeCalabiYauFoundationsWanted
