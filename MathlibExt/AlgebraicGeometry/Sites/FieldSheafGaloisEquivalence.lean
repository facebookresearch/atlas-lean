/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module
public import MathlibExt.AlgebraicGeometry.Sites.FieldEquivariantStalkCounitIsomorphism
public import MathlibExt.AlgebraicGeometry.Sites.FieldGeometricStalkConservativity
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-! # The original field-sheaf and continuous Galois-module equivalence

The functors, point, chosen closure and original-index inverse are the same
constructed objects. The actual counit and first triangle give an invertible
stalk image of the unit; prescribed-stalk conservativity gives the unit itself.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
universe u w
namespace AlgebraicGeometry.Scheme.DerivedSections
attribute [local instance] IsSepClosure.sep_closed
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]

/-- The first actual triangle identifies the image of the original unit with
the inverse of the SAME original counit component. -/
theorem fieldEquivariantStalkUnit_map_eq_counit_inv
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map
        ((fieldEquivariantStalkUnit.{u, w} k Ω).app Q) =
      inv ((fieldEquivariantStalkCounit.{u, w} k Ω).app
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q)) := by
  let a := (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map
    ((fieldEquivariantStalkUnit.{u, w} k Ω).app Q)
  let b := (fieldEquivariantStalkCounit.{u, w} k Ω).app
    ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q)
  have h : a ≫ b = 𝟙 _ := fieldEquivariantStalk_left_triangle.{u, w} k Ω Q
  calc
    a = a ≫ (b ≫ inv b) := (by rw [IsIso.hom_inv_id, Category.comp_id])
    _ = (a ≫ b) ≫ inv b := (Category.assoc _ _ _).symm
    _ = inv b := by rw [h, Category.id_comp]

/-- The SAME original stalk functor reflects invertibility of its actual unit. -/
instance fieldEquivariantStalkUnit_isIso
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    IsIso ((fieldEquivariantStalkUnit.{u, w} k Ω).app Q) := by
  let : IsIso ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map
      ((fieldEquivariantStalkUnit.{u, w} k Ω).app Q)) := by
    rw [fieldEquivariantStalkUnit_map_eq_counit_inv.{u, w} k Ω Q]
    infer_instance
  exact isIso_of_reflects_iso _ (fieldGeometricStalkGaloisFunctor.{u, w} k Ω)

/-- The genuine equivalence uses the SAME original stalk and literal inverse sheaf. -/
def fieldSheafGaloisEquivalence :
    Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w} ≌
      DiscreteAbelianAction.{u, max u w} Gal(Ω/k) :=
  (fieldEquivariantStalkAdjunction.{u, w} k Ω).toEquivalence

theorem fieldSheafGaloisEquivalence_functor :
    (fieldSheafGaloisEquivalence.{u, w} k Ω).functor =
      fieldGeometricStalkGaloisFunctor.{u, w} k Ω := rfl

theorem fieldSheafGaloisEquivalence_inverse :
    (fieldSheafGaloisEquivalence.{u, w} k Ω).inverse =
      fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω := rfl

/-- Its actual unit is exactly the original invariant germ unit, without replacement. -/
theorem fieldSheafGaloisEquivalence_unit_hom :
    (fieldSheafGaloisEquivalence.{u, w} k Ω).unitIso.hom =
      fieldEquivariantStalkUnit.{u, w} k Ω := rfl

/-- Its actual counit is exactly the original evaluation arrow. -/
theorem fieldSheafGaloisEquivalence_counit_hom :
    (fieldSheafGaloisEquivalence.{u, w} k Ω).counitIso.hom =
      fieldEquivariantStalkCounit.{u, w} k Ω := rfl

/-- Both original triangles hold for the constructed equivalence maps. -/
theorem fieldSheafGaloisEquivalence_left_triangle
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    (fieldSheafGaloisEquivalence.{u, w} k Ω).functor.map
        ((fieldSheafGaloisEquivalence.{u, w} k Ω).unitIso.hom.app Q) ≫
      (fieldSheafGaloisEquivalence.{u, w} k Ω).counitIso.hom.app
        ((fieldSheafGaloisEquivalence.{u, w} k Ω).functor.obj Q) = 𝟙 _ :=
  fieldEquivariantStalk_left_triangle.{u, w} k Ω Q

theorem fieldSheafGaloisEquivalence_right_triangle
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    (fieldSheafGaloisEquivalence.{u, w} k Ω).unitIso.hom.app
        ((fieldSheafGaloisEquivalence.{u, w} k Ω).inverse.obj M) ≫
      (fieldSheafGaloisEquivalence.{u, w} k Ω).inverse.map
        ((fieldSheafGaloisEquivalence.{u, w} k Ω).counitIso.hom.app M) = 𝟙 _ :=
  fieldEquivariantStalk_right_triangle.{u, w} k Ω M

/-- The unit retains every actual original section and its original point germ. -/
theorem fieldSheafGaloisEquivalence_unit_germ
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (U : (Spec (.of k)).Etale) (z : (fieldGeometricPoint k Ω).fiber.obj U)
    (c : Q.obj.obj (op U)) :
    (show FieldEquivariantFunctions.{u, w} k Ω U
      ((fieldSheafGaloisEquivalence.{u, w} k Ω).functor.obj Q) from
      ((fieldSheafGaloisEquivalence.{u, w} k Ω).unitIso.hom.app Q).hom.app (op U) c) z =
      (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        U (ULift.up z) Q.obj c :=
  fieldEquivariantStalkUnit_germ.{u, w} k Ω Q U z c

/-- The counit retains every original germ and its literal invariant-function value. -/
theorem fieldSheafGaloisEquivalence_counit_germ
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (U : (Spec (.of k)).Etale) (z : (fieldGeometricPoint k Ω).fiber.obj U)
    (h : FieldEquivariantFunctions.{u, w} k Ω U M) :
    DiscreteAbelianAction.homToAdd
      ((fieldSheafGaloisEquivalence.{u, w} k Ω).counitIso.hom.app M)
      ((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber U
        (ULift.up z) ((fieldSheafGaloisEquivalence.{u, w} k Ω).inverse.obj M).obj h) = h z :=
  fieldEquivariantStalkCounit_germ.{u, w} k Ω M U z h

/-- The full original-site inverse value is the literal equivariant-function group. -/
theorem fieldSheafGaloisEquivalence_inverse_value
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) (U : (Spec (.of k)).Etale) :
    ((fieldSheafGaloisEquivalence.{u, w} k Ω).inverse.obj M).obj.obj (op U) =
      AddCommGrpCat.of (FieldEquivariantFunctions.{u, w} k Ω U M) := rfl

/-- Every original-site inverse restriction retains actual geometric-fiber precomposition. -/
theorem fieldSheafGaloisEquivalence_inverse_restrict
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    {U V : (Spec (.of k)).Etale} (r : V ⟶ U)
    (h : FieldEquivariantFunctions.{u, w} k Ω U M)
    (z : (fieldGeometricPoint k Ω).fiber.obj V) :
    (show FieldEquivariantFunctions.{u, w} k Ω V M from
      ((fieldSheafGaloisEquivalence.{u, w} k Ω).inverse.obj M).obj.map r.op h) z =
        h ((fieldGeometricPoint k Ω).fiber.map r z) :=
  fieldInvariantSkyscraperInverseSheaf_restrict_apply.{u, w} k Ω M r h z

/-- Every original module map is the SAME original pointwise additive function. -/
theorem fieldSheafGaloisEquivalence_inverse_map
    {M N : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)} (t : M ⟶ N)
    (U : (Spec (.of k)).Etale) (h : FieldEquivariantFunctions.{u, w} k Ω U M)
    (z : (fieldGeometricPoint k Ω).fiber.obj U) :
    (show FieldEquivariantFunctions.{u, w} k Ω U N from
      ((fieldSheafGaloisEquivalence.{u, w} k Ω).inverse.map t).hom.app (op U) h) z =
      DiscreteAbelianAction.homToAdd t (h z) :=
  fieldInvariantSkyscraperInverseSheaf_map_apply.{u, w} k Ω t U h z

/-- Every finite-algebra value is the SAME original Hom_G formula, including product algebras. -/
@[nolint defsWithUnderscore]
def fieldSheafGaloisEquivalence_finite_value
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (A : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ) :
    ((fieldSheafGaloisEquivalence.{u, w} k Ω).inverse.obj M).obj.obj
        (op ((fieldFiniteEtaleToEtale k).obj A)) ≃+
      ((A.unop →ₐ[k] Ω) →[Gal(Ω/k)] DiscreteAbelianAction.underlying M) :=
  fieldInvariantFiniteEtaleSectionsEquiv.{u, w} k Ω M A

/-- Every original finite-algebra arrow is the actual embedding precomposition. -/
theorem fieldSheafGaloisEquivalence_finite_restrict
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    {A B : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ} (r : A ⟶ B)
    (h : ((fieldSheafGaloisEquivalence.{u, w} k Ω).inverse.obj M).obj.obj
      (op ((fieldFiniteEtaleToEtale k).obj B))) (ξ : A.unop →ₐ[k] Ω) :
    fieldSheafGaloisEquivalence_finite_value.{u, w} k Ω M A
        (((fieldSheafGaloisEquivalence.{u, w} k Ω).inverse.obj M).obj.map
          ((fieldFiniteEtaleToEtale k).map r).op h) ξ =
      fieldSheafGaloisEquivalence_finite_value.{u, w} k Ω M B h (ξ.comp r.unop.hom.hom) :=
  fieldInvariantFiniteEtaleSectionsEquiv_restrict.{u, w} k Ω M r h ξ

/-- Every original module arrow uses its SAME additive postcomposition on finite values. -/
theorem fieldSheafGaloisEquivalence_finite_map
    {M N : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)} (t : M ⟶ N)
    (A : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ)
    (h : ((fieldSheafGaloisEquivalence.{u, w} k Ω).inverse.obj M).obj.obj
      (op ((fieldFiniteEtaleToEtale k).obj A))) (ξ : A.unop →ₐ[k] Ω) :
    fieldSheafGaloisEquivalence_finite_value.{u, w} k Ω N A
        (((fieldSheafGaloisEquivalence.{u, w} k Ω).inverse.map t).hom.app
          (op ((fieldFiniteEtaleToEtale k).obj A)) h) ξ =
      DiscreteAbelianAction.homToAdd t
        (fieldSheafGaloisEquivalence_finite_value.{u, w} k Ω M A h ξ) :=
  fieldInvariantFiniteEtaleSectionsEquiv_map.{u, w} k Ω t A h ξ

/-- The original coefficient specialization goes through the ONE existing lift. -/
theorem fieldSheafGaloisEquivalence_original_unit_germ
    (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w})
    (U : (Spec (.of k)).Etale) (z : (fieldGeometricPoint k Ω).fiber.obj U)
    (c : F.obj.obj (op U)) :
    (show FieldEquivariantFunctions.{u, w} k Ω U
      ((fieldSheafGaloisEquivalence.{u, w} k Ω).functor.obj
        ((liftCoefficients.{u, w} (Spec (.of k))).obj F)) from
      ((fieldSheafGaloisEquivalence.{u, w} k Ω).unitIso.hom.app
        ((liftCoefficients.{u, w} (Spec (.of k))).obj F)).hom.app (op U) (ULift.up c)) z =
    (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber U
      (ULift.up z) ((liftCoefficients.{u, w} (Spec (.of k))).obj F).obj (ULift.up c) :=
  fieldEquivariantStalkUnit_original_germ.{u, w} k Ω F U z c

/-- The complete field equivalence keeps both actual functors and every original source law. -/
def OriginalFieldSheafGaloisEquivalenceLaws : Prop :=
  let E := fieldSheafGaloisEquivalence.{u, w} k Ω
  let T := fieldGeometricStalkGaloisFunctor.{u, w} k Ω
  let R := fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω
  E.functor = T ∧ E.inverse = R ∧
  E.unitIso.hom = fieldEquivariantStalkUnit.{u, w} k Ω ∧
  E.counitIso.hom = fieldEquivariantStalkCounit.{u, w} k Ω ∧
  (∀ Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w},
    IsIso ((fieldEquivariantStalkUnit.{u, w} k Ω).app Q)) ∧
  (∀ M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k),
    IsIso ((fieldEquivariantStalkCounit.{u, w} k Ω).app M)) ∧
  (∀ Q, T.map (E.unitIso.hom.app Q) ≫ E.counitIso.hom.app (T.obj Q) = 𝟙 _) ∧
  (∀ M, E.unitIso.hom.app (R.obj M) ≫ R.map (E.counitIso.hom.app M) = 𝟙 _) ∧
  (∀ (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (U : (Spec (.of k)).Etale) (z : (fieldGeometricPoint k Ω).fiber.obj U)
    (c : Q.obj.obj (op U)),
    (show FieldEquivariantFunctions.{u, w} k Ω U (T.obj Q) from
      (E.unitIso.hom.app Q).hom.app (op U) c) z =
    (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
      U (ULift.up z) Q.obj c) ∧
  (∀ (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (U : (Spec (.of k)).Etale) (z : (fieldGeometricPoint k Ω).fiber.obj U)
    (h : FieldEquivariantFunctions.{u, w} k Ω U M),
    DiscreteAbelianAction.homToAdd (E.counitIso.hom.app M)
      ((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        U (ULift.up z) (R.obj M).obj h) = h z) ∧
  (∀ (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) (U : (Spec (.of k)).Etale),
    (R.obj M).obj.obj (op U) = AddCommGrpCat.of (FieldEquivariantFunctions.{u, w} k Ω U M)) ∧
  (∀ (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (U V : (Spec (.of k)).Etale) (r : V ⟶ U)
    (h : FieldEquivariantFunctions.{u, w} k Ω U M)
    (z : (fieldGeometricPoint k Ω).fiber.obj V),
    (show FieldEquivariantFunctions.{u, w} k Ω V M from (R.obj M).obj.map r.op h) z =
      h ((fieldGeometricPoint k Ω).fiber.map r z)) ∧
  (∀ (M N : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) (t : M ⟶ N)
    (U : (Spec (.of k)).Etale) (h : FieldEquivariantFunctions.{u, w} k Ω U M)
    (z : (fieldGeometricPoint k Ω).fiber.obj U),
    (show FieldEquivariantFunctions.{u, w} k Ω U N from (R.map t).hom.app (op U) h) z =
      DiscreteAbelianAction.homToAdd t (h z)) ∧
  (∀ (Q Q' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (τ : Q ⟶ Q'), τ ≫ E.unitIso.hom.app Q' =
      E.unitIso.hom.app Q ≫ R.map (T.map τ)) ∧
  (∀ (M N : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) (t : M ⟶ N),
    T.map (R.map t) ≫ E.counitIso.hom.app N = E.counitIso.hom.app M ≫ t) ∧
  (∀ (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (A : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ),
    Nonempty ((R.obj M).obj.obj (op ((fieldFiniteEtaleToEtale k).obj A)) ≃+
      ((A.unop →ₐ[k] Ω) →[Gal(Ω/k)] DiscreteAbelianAction.underlying M))) ∧
  (∀ (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (A B : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ) (r : A ⟶ B)
    (h : (R.obj M).obj.obj (op ((fieldFiniteEtaleToEtale k).obj B)))
    (ξ : A.unop →ₐ[k] Ω),
    fieldSheafGaloisEquivalence_finite_value.{u, w} k Ω M A
      ((R.obj M).obj.map ((fieldFiniteEtaleToEtale k).map r).op h) ξ =
    fieldSheafGaloisEquivalence_finite_value.{u, w} k Ω M B h (ξ.comp r.unop.hom.hom)) ∧
  (∀ (M N : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) (t : M ⟶ N)
    (A : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ)
    (h : (R.obj M).obj.obj (op ((fieldFiniteEtaleToEtale k).obj A))) (ξ : A.unop →ₐ[k] Ω),
    fieldSheafGaloisEquivalence_finite_value.{u, w} k Ω N A
      ((R.map t).hom.app (op ((fieldFiniteEtaleToEtale k).obj A)) h) ξ =
    DiscreteAbelianAction.homToAdd t
      (fieldSheafGaloisEquivalence_finite_value.{u, w} k Ω M A h ξ)) ∧
  ∀ (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w})
    (U : (Spec (.of k)).Etale) (z : (fieldGeometricPoint k Ω).fiber.obj U)
    (c : F.obj.obj (op U)),
    (show FieldEquivariantFunctions.{u, w} k Ω U
      (T.obj ((liftCoefficients.{u, w} (Spec (.of k))).obj F)) from
      (E.unitIso.hom.app ((liftCoefficients.{u, w} (Spec (.of k))).obj F)).hom.app
        (op U) (ULift.up c)) z =
    (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
      U (ULift.up z) ((liftCoefficients.{u, w} (Spec (.of k))).obj F).obj (ULift.up c)

/-- The full original field-sheaf/Galois-module equivalence source unit. -/
theorem original_field_sheaf_galois_equivalence :
    OriginalFieldSheafGaloisEquivalenceLaws.{u, w} k Ω := by
  refine ⟨rfl, rfl, rfl, rfl, (fun Q => inferInstance), (fun M => inferInstance),
    fieldSheafGaloisEquivalence_left_triangle.{u, w} k Ω,
    fieldSheafGaloisEquivalence_right_triangle.{u, w} k Ω,
    fieldSheafGaloisEquivalence_unit_germ.{u, w} k Ω,
    fieldSheafGaloisEquivalence_counit_germ.{u, w} k Ω,
    fieldSheafGaloisEquivalence_inverse_value.{u, w} k Ω, ?_, ?_, ?_, ?_,
    (fun M A => ⟨fieldSheafGaloisEquivalence_finite_value.{u, w} k Ω M A⟩),
    ?_, ?_, fieldSheafGaloisEquivalence_original_unit_germ.{u, w} k Ω⟩
  · intro M U V r h z
    exact fieldSheafGaloisEquivalence_inverse_restrict.{u, w} k Ω M r h z
  · intro M N t U h z
    exact fieldSheafGaloisEquivalence_inverse_map.{u, w} k Ω t U h z
  · intro Q Q' τ
    exact fieldEquivariantStalkUnit_naturality.{u, w} k Ω τ
  · intro M N t
    exact fieldEquivariantStalkCounit_naturality.{u, w} k Ω t
  · intro M A B r h ξ
    exact fieldSheafGaloisEquivalence_finite_restrict.{u, w} k Ω M r h ξ
  · intro M N t A h ξ
    exact fieldSheafGaloisEquivalence_finite_map.{u, w} k Ω t A h ξ

end AlgebraicGeometry.Scheme.DerivedSections
