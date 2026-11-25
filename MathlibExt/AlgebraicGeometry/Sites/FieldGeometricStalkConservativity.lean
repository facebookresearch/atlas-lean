/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
-- Formalization developed with automated proof assistants; original Git history retained.
module
public import MathlibExt.AlgebraicGeometry.Sites.FieldGeometricStalkGaloisAction
public import Mathlib.CategoryTheory.Sites.Point.Conservative

/-! # Cover detection and conservativity of the prescribed field point

The field, chosen separable closure, original small etale objects and actual
arrows are retained. Only point-fiber elements and original coefficient groups
are lifted to the same common universe.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
universe u w
namespace AlgebraicGeometry.Scheme.DerivedSections
attribute [local instance] IsSepClosure.sep_closed
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]

omit [IsSepClosure k Ω] in
/-- The actual map from the chosen closure covers the spectrum of the field. -/
theorem fieldPrescribedGeometricMorphism_surjective :
    Function.Surjective (Spec.algebraMap k Ω) := by
  intro x
  exact ⟨default, Subsingleton.elim _ _⟩

/-- A singleton family containing the prescribed original point. -/
def fieldPrescribedGeometricPointFamily :
    ObjectProperty (Spec (.of k)).smallEtaleTopology.Point.{u} :=
  ObjectProperty.ofObj (fun _ : Unit => fieldGeometricPoint k Ω)

/-- Native conservativity follows from the actual geometric morphism's range. -/
theorem fieldPrescribedGeometricPointFamily_conservative :
    (fieldPrescribedGeometricPointFamily k Ω).IsConservativeFamilyOfPoints := by
  apply Scheme.isConservative_pointSmallEtale (Ω := fun _ : Unit => Ω)
    (fun _ => Spec.algebraMap k Ω)
  ext x
  simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
  exact ⟨(), (fieldPrescribedGeometricMorphism_surjective k Ω x)⟩

/-- Every original covering sieve is detected by the same native point. -/
theorem fieldPrescribedGeometricPoint_cover_iff
    {U : (Spec (.of k)).Etale} (R : Sieve U) :
    R ∈ (Spec (.of k)).smallEtaleTopology U ↔
      ∀ z : (fieldGeometricPoint k Ω).fiber.obj U,
        ∃ (V : (Spec (.of k)).Etale) (g : V ⟶ U) (_ : R g)
          (y : (fieldGeometricPoint k Ω).fiber.obj V),
          (fieldGeometricPoint k Ω).fiber.map g y = z := by
  constructor
  · intro hR z
    exact (fieldGeometricPoint k Ω).jointly_surjective R hR z
  · intro hR
    let : ObjectProperty.Small.{u} (fieldPrescribedGeometricPointFamily k Ω) := by
      dsimp only [fieldPrescribedGeometricPointFamily]
      infer_instance
    obtain ⟨ι, V, g, rfl⟩ := R.exists_eq_ofArrows
    apply (ObjectProperty.IsConservativeFamilyOfPoints.jointly_reflect_ofArrows_mem_of_small
      (fieldPrescribedGeometricPointFamily_conservative k Ω) g).mpr
    rintro ⟨Φ, hΦ⟩ z
    obtain ⟨i, hi⟩ := (ObjectProperty.ofObj_iff _ Φ).mp hΦ
    subst Φ
    obtain ⟨T, q, hq, y, hy⟩ := hR z
    obtain ⟨_, p, _, ⟨j⟩, rfl⟩ := hq
    refine ⟨j, (fieldGeometricPoint k Ω).fiber.map p y, ?_⟩
    simpa only [Functor.map_comp, ConcreteCategory.comp_apply] using hy

/-- The common point retains exactly the original fiber elements through up/down. -/
theorem fieldPrescribedCommonPoint_fiber_obj (U : (Spec (.of k)).Etale) :
    (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).fiber.obj U =
      ULift.{w} ((fieldGeometricPoint k Ω).fiber.obj U) := rfl

/-- Each common fiber restriction is the single lift of the original restriction. -/
theorem fieldPrescribedCommonPoint_fiber_map
    {U V : (Spec (.of k)).Etale} (g : V ⟶ U)
    (z : (fieldGeometricPoint k Ω).fiber.obj V) :
    (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).fiber.map g
        (ULift.up z) = ULift.up ((fieldGeometricPoint k Ω).fiber.map g z) := rfl

/-- The common lifting criterion concerns the very same original sieve and arrows. -/
theorem fieldPrescribedCommonPoint_cover_iff
    {U : (Spec (.of k)).Etale} (R : Sieve U) :
    R ∈ (Spec (.of k)).smallEtaleTopology U ↔
      ∀ z : (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).fiber.obj U,
        ∃ (V : (Spec (.of k)).Etale) (g : V ⟶ U) (_ : R g)
          (y : (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).fiber.obj V),
          (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).fiber.map g y = z := by
  constructor
  · intro hR z
    exact (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).jointly_surjective
      R hR z
  · intro hR
    apply (fieldPrescribedGeometricPoint_cover_iff k Ω R).mpr
    intro z
    obtain ⟨V, g, hg, y, hy⟩ := hR (ULift.up z)
    exact ⟨V, g, hg, y.down, congrArg ULift.down hy⟩

/-- The singleton family after lifting only its point-fiber elements. -/
def fieldPrescribedCommonPointFamily :
    ObjectProperty (Spec (.of k)).smallEtaleTopology.Point.{max u w} :=
  ObjectProperty.ofObj
    (fun _ : Unit => smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω))

/-- Common conservativity is derived from the actual original-sieve criterion. -/
theorem fieldPrescribedCommonPointFamily_conservative :
    (fieldPrescribedCommonPointFamily.{u, w} k Ω).IsConservativeFamilyOfPoints := by
  apply ObjectProperty.IsConservativeFamilyOfPoints.mk'
  intro U R hR
  apply (fieldPrescribedCommonPoint_cover_iff.{u, w} k Ω R).mpr
  intro z
  exact hR
    ⟨smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω),
      ObjectProperty.ofObj.mk ()⟩ z

/-- The actual prescribed common abelian stalk reflects all sheaf isomorphisms. -/
instance fieldPrescribedCommonStalk_reflectsIsomorphisms :
    (smallEtaleCommonGeometricStalk.{u, w} (Spec.algebraMap k Ω)).ReflectsIsomorphisms where
  reflects τ _ := by
    have h := (fieldPrescribedCommonPointFamily_conservative.{u, w} k Ω).jointlyReflectIsomorphisms
      AddCommGrpCat.{max u w}
    let (Φ : (fieldPrescribedCommonPointFamily.{u, w} k Ω).FullSubcategory) :
        IsIso (Φ.obj.sheafFiber.map τ) := by
      rcases Φ with ⟨Φ, hΦ⟩
      obtain ⟨i, rfl⟩ := (ObjectProperty.ofObj_iff _ Φ).mp hΦ
      exact inferInstanceAs
        (IsIso ((smallEtaleCommonGeometricStalk.{u, w} (Spec.algebraMap k Ω)).map τ))
    exact h.isIso τ

/-- Forgetting the same Galois action transfers actual stalk conservativity to T. -/
instance fieldGeometricStalkGaloisFunctor_reflectsIsomorphisms :
    (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).ReflectsIsomorphisms := by
  let : (fieldGeometricStalkGaloisFunctor.{u, w} k Ω ⋙
      DiscreteAbelianAction.forget Gal(Ω/k)).ReflectsIsomorphisms :=
    inferInstanceAs
      ((smallEtaleCommonGeometricStalk.{u, w} (Spec.algebraMap k Ω)).ReflectsIsomorphisms)
  exact reflectsIsomorphisms_of_comp (fieldGeometricStalkGaloisFunctor.{u, w} k Ω)
    (DiscreteAbelianAction.forget Gal(Ω/k))

/-- The canonical one coefficient lift reflects all original sheaf isomorphisms. -/
instance fieldOriginalCoefficientLift_reflectsIsomorphisms :
    (liftCoefficients.{u, w} (Spec (.of k))).ReflectsIsomorphisms := by
  let J := (Spec (.of k)).smallEtaleTopology
  let L := liftCoefficients.{u, w} (Spec (.of k))
  let : (L ⋙ sheafToPresheaf J AddCommGrpCat.{max u w}).ReflectsIsomorphisms := by
    change (sheafToPresheaf J AddCommGrpCat.{w} ⋙
      (Functor.whiskeringRight (Spec (.of k)).Etaleᵒᵖ AddCommGrpCat.{w}
        AddCommGrpCat.{max u w}).obj AddCommGrpCat.uliftFunctor.{u, w}).ReflectsIsomorphisms
    infer_instance
  exact reflectsIsomorphisms_of_comp L (sheafToPresheaf J AddCommGrpCat.{max u w})

/-- Original sheaf maps are detected after the same one lift and prescribed stalk. -/
theorem fieldOriginalSheafMap_isIso_iff_commonStalk
    {F F' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w}} (τ : F ⟶ F') :
    IsIso ((smallEtaleCommonGeometricStalk.{u, w} (Spec.algebraMap k Ω)).map
      ((liftCoefficients.{u, w} (Spec (.of k))).map τ)) ↔ IsIso τ := by
  rw [isIso_iff_of_reflects_iso,
    isIso_iff_of_reflects_iso]

/-- The same original-map assertion holds for the actual Galois-module functor. -/
theorem fieldOriginalSheafMap_isIso_iff_galoisStalk
    {F F' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w}} (τ : F ⟶ F') :
    IsIso ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map
      ((liftCoefficients.{u, w} (Spec (.of k))).map τ)) ↔ IsIso τ := by
  rw [isIso_iff_of_reflects_iso,
    isIso_iff_of_reflects_iso]

/-- Every original coefficient value is retained through the literal single lift. -/
theorem fieldOriginalCoefficientLift_obj
    (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w})
    (U : (Spec (.of k)).Etale) :
    ((liftCoefficients.{u, w} (Spec (.of k))).obj F).obj.obj (op U) =
      AddCommGrpCat.of (ULift.{u} (F.obj.obj (op U))) := rfl

/-- Every original restriction and coefficient morphism retains its actual lifted map. -/
theorem fieldOriginalCoefficientLift_map
    {F F' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w}}
    (τ : F ⟶ F') (U : (Spec (.of k)).Etale) :
    ((liftCoefficients.{u, w} (Spec (.of k))).map τ).hom.app (op U) =
      AddCommGrpCat.uliftFunctor.{u, w}.map (τ.hom.app (op U)) := rfl

/-- All native/common covering and original-map reflection laws use the fixed point. -/
def OriginalFieldSingletonStalkConservativityLaws : Prop :=
  let X := Spec (.of k)
  let p := fieldGeometricPoint k Ω
  let pc := smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)
  let S := smallEtaleCommonGeometricStalk.{u, w} (Spec.algebraMap k Ω)
  let T := fieldGeometricStalkGaloisFunctor.{u, w} k Ω
  let L := liftCoefficients.{u, w} X
  Function.Surjective (Spec.algebraMap k Ω) ∧
  (∀ (U : X.Etale) (R : Sieve U), R ∈ X.smallEtaleTopology U ↔
    ∀ z : p.fiber.obj U, ∃ (V : X.Etale) (g : V ⟶ U) (_ : R g)
      (y : p.fiber.obj V), p.fiber.map g y = z) ∧
  (∀ U : X.Etale, pc.fiber.obj U = ULift.{w} (p.fiber.obj U)) ∧
  (∀ (U V : X.Etale) (g : V ⟶ U) (z : p.fiber.obj V),
    pc.fiber.map g (ULift.up z) = ULift.up (p.fiber.map g z)) ∧
  (∀ (U : X.Etale) (R : Sieve U), R ∈ X.smallEtaleTopology U ↔
    ∀ z : pc.fiber.obj U, ∃ (V : X.Etale) (g : V ⟶ U) (_ : R g)
      (y : pc.fiber.obj V), pc.fiber.map g y = z) ∧
  (fieldPrescribedGeometricPointFamily k Ω).IsConservativeFamilyOfPoints ∧
  (fieldPrescribedCommonPointFamily.{u, w} k Ω).IsConservativeFamilyOfPoints ∧
  S.ReflectsIsomorphisms ∧ T.ReflectsIsomorphisms ∧
  (∀ (Q Q' : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (τ : Q ⟶ Q'),
    IsIso (S.map τ) ↔ IsIso τ) ∧
  (∀ (Q Q' : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (τ : Q ⟶ Q'),
    IsIso (T.map τ) ↔ IsIso τ) ∧
  (∀ (F F' : Sheaf X.smallEtaleTopology AddCommGrpCat.{w}) (τ : F ⟶ F'),
    (IsIso (S.map (L.map τ)) ↔ IsIso τ) ∧
    (IsIso (T.map (L.map τ)) ↔ IsIso τ) ∧
    (∀ U : X.Etale, (L.map τ).hom.app (op U) =
      AddCommGrpCat.uliftFunctor.{u, w}.map (τ.hom.app (op U))) ∧
    (DiscreteAbelianAction.forget Gal(Ω/k)).map (T.map (L.map τ)) = S.map (L.map τ)) ∧
  (∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{w}) (U : X.Etale),
    (L.obj F).obj.obj (op U) = AddCommGrpCat.of (ULift.{u} (F.obj.obj (op U)))) ∧
  T ⋙ DiscreteAbelianAction.forget Gal(Ω/k) = S

/-- The complete original singleton-cover and conservative-stalk source unit. -/
theorem original_field_singleton_stalk_conservativity :
    OriginalFieldSingletonStalkConservativityLaws.{u, w} k Ω := by
  refine ⟨fieldPrescribedGeometricMorphism_surjective k Ω,
    (fun _ R => fieldPrescribedGeometricPoint_cover_iff k Ω R),
    fieldPrescribedCommonPoint_fiber_obj.{u, w} k Ω,
    (fun _ _ g z => fieldPrescribedCommonPoint_fiber_map.{u, w} k Ω g z),
    (fun _ R => fieldPrescribedCommonPoint_cover_iff.{u, w} k Ω R),
    fieldPrescribedGeometricPointFamily_conservative k Ω,
    fieldPrescribedCommonPointFamily_conservative.{u, w} k Ω,
    inferInstance, inferInstance, ?_, ?_, ?_,
    fieldOriginalCoefficientLift_obj.{u, w} k,
    fieldGeometricStalkGaloisFunctor_forget.{u, w} k Ω⟩
  · exact fun _ _ τ => isIso_iff_of_reflects_iso τ _
  · exact fun _ _ τ => isIso_iff_of_reflects_iso τ _
  · intro F F' τ
    exact ⟨fieldOriginalSheafMap_isIso_iff_commonStalk.{u, w} k Ω τ,
      fieldOriginalSheafMap_isIso_iff_galoisStalk.{u, w} k Ω τ,
      fieldOriginalCoefficientLift_map.{u, w} k τ, rfl⟩

end AlgebraicGeometry.Scheme.DerivedSections
