/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module
public import MathlibExt.AlgebraicGeometry.Sites.FieldGeometricStalkGaloisAction
public import MathlibExt.AlgebraicGeometry.Sites.FieldFiniteEtaleBasis
public import MathlibExt.CategoryTheory.Sites.Point.Mates
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-! # Literal equivariant-function sheaves from the same point skyscraper

The field and prescribed separable closure are fixed. The original point
indices and all possibly infinite discrete abelian modules are retained.
The skyscraper diagonal uses the inverse on the index and the same action on
its coefficient group. Invariant limits are taken in the common sheaf category.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
universe u w
namespace AlgebraicGeometry.Scheme.DerivedSections
attribute [local instance] IsSepClosure.sep_closed
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]

/-- The native set action is the SAME original geometric fiber map. -/
instance fieldOriginalFiberMulAction (U : (Spec (.of k)).Etale) :
    MulAction Gal(Ω/k) ((fieldGeometricPoint k Ω).fiber.obj U) where
  smul g z := (fieldGaloisFiberMap k Ω g).app U z
  one_smul z := by
    change (fieldGaloisFiberMap k Ω (1 : Gal(Ω/k))).app U z = z
    rw [fieldGaloisFiberMap_one]
    rfl
  mul_smul g h z := by
    change (fieldGaloisFiberMap k Ω (g * h)).app U z =
      (fieldGaloisFiberMap k Ω g).app U ((fieldGaloisFiberMap k Ω h).app U z)
    rw [fieldGaloisFiberMap_mul]
    rfl

/-- The original restrictions are genuine equivariant maps of the native fibers. -/
def fieldOriginalFiberMap {U V : (Spec (.of k)).Etale} (r : V ⟶ U) :
    (fieldGeometricPoint k Ω).fiber.obj V →[Gal(Ω/k)]
      (fieldGeometricPoint k Ω).fiber.obj U where
  toFun := (fieldGeometricPoint k Ω).fiber.map r
  map_smul' g z := by
    change (fieldGeometricPoint k Ω).fiber.map r ((fieldGaloisFiberMap k Ω g).app V z) =
      (fieldGaloisFiberMap k Ω g).app U ((fieldGeometricPoint k Ω).fiber.map r z)
    exact ((fieldGaloisFiberMap k Ω g).naturality_apply r z).symm

/-- The literal ORIGINAL-index equivariant function space, with its pointwise group. -/
abbrev FieldEquivariantFunctions (U : (Spec (.of k)).Etale)
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) : Type (max u w) :=
  (fieldGeometricPoint k Ω).fiber.obj U →[Gal(Ω/k)] DiscreteAbelianAction.underlying M

@[nolint defsWithUnderscore] -- instance name; never referenced
instance fieldEquivariantFunctions_addCommGroup (U : (Spec (.of k)).Etale)
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    AddCommGroup (FieldEquivariantFunctions.{u, w} k Ω U M) := by
  infer_instance

/-- The original section restriction is precomposition by the original fiber map. -/
def fieldEquivariantFunctionsRestrict {U V : (Spec (.of k)).Etale} (r : V ⟶ U)
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    FieldEquivariantFunctions.{u, w} k Ω U M →+
      FieldEquivariantFunctions.{u, w} k Ω V M where
  toFun h := h.comp (fieldOriginalFiberMap k Ω r)
  map_zero' := by ext z; rfl
  map_add' h h' := by ext z; rfl

/-- Deprecated alias for `fieldEquivariantFunctionsRestrict`. -/
@[deprecated fieldEquivariantFunctionsRestrict (since := "2026-10-28"), nolint defsWithUnderscore]
alias fieldEquivariantFunctions_restrict := fieldEquivariantFunctionsRestrict

/-- Every original module map acts by postcomposition with its same additive function. -/
def fieldEquivariantFunctionsPost
    {M N : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)} (t : M ⟶ N)
    (U : (Spec (.of k)).Etale) :
    FieldEquivariantFunctions.{u, w} k Ω U M →+
      FieldEquivariantFunctions.{u, w} k Ω U N where
  toFun h := {
    toFun := fun z => DiscreteAbelianAction.homToAdd t (h z)
    map_smul' := fun g z => by
      rw [h.map_smul]
      exact DiscreteAbelianAction.homToAdd_equivariant t g (h z) }
  map_zero' := by ext z; exact (DiscreteAbelianAction.homToAdd t).map_zero
  map_add' h h' := by ext z; exact (DiscreteAbelianAction.homToAdd t).map_add _ _

/-- Deprecated alias for `fieldEquivariantFunctionsPost`. -/
@[deprecated fieldEquivariantFunctionsPost (since := "2026-10-28"), nolint defsWithUnderscore]
alias fieldEquivariantFunctions_post := fieldEquivariantFunctionsPost

/-- The literal original-index equivariant-function presheaf on every original object. -/
def fieldEquivariantFunctionPresheaf
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    (Spec (.of k)).Etaleᵒᵖ ⥤ AddCommGrpCat.{max u w} where
  obj U := AddCommGrpCat.of (FieldEquivariantFunctions.{u, w} k Ω U.unop M)
  map r := AddCommGrpCat.ofHom (fieldEquivariantFunctionsRestrict.{u, w} k Ω r.unop M)
  map_id U := by
    ext h z
    change h ((fieldGeometricPoint k Ω).fiber.map (𝟙 U.unop) z) = h z
    rw [CategoryTheory.Functor.map_id]
    rfl
  map_comp r s := by
    ext h z
    change h ((fieldGeometricPoint k Ω).fiber.map (s.unop ≫ r.unop) z) =
      h ((fieldGeometricPoint k Ω).fiber.map r.unop
        ((fieldGeometricPoint k Ω).fiber.map s.unop z))
    rw [CategoryTheory.Functor.map_comp]
    rfl

/-- All module maps give the actual original-component natural transformation. -/
def fieldEquivariantFunctionPresheafMap
    {M N : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)} (t : M ⟶ N) :
    fieldEquivariantFunctionPresheaf.{u, w} k Ω M ⟶
      fieldEquivariantFunctionPresheaf.{u, w} k Ω N where
  app U := AddCommGrpCat.ofHom (fieldEquivariantFunctionsPost.{u, w} k Ω t U.unop)
  naturality U V r := by ext h; rfl

/-- The same underlying coefficient action through the genuine stock forgetful functors. -/
abbrev fieldModuleAbAction
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    Action AddCommGrpCat.{max u w} Gal(Ω/k) :=
  ((forget₂ (TopModuleCat.{max u w} ℤ) (ModuleCat.{max u w} ℤ) ⋙
    forget₂ (ModuleCat.{max u w} ℤ) AddCommGrpCat.{max u w}).mapAction Gal(Ω/k)).obj M.obj.obj

/-- The actual skyscraper of the SAME common point and SAME coefficient group. -/
abbrev fieldSkyscraper
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w} :=
  (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafFunctor.obj
    ((fieldModuleAbAction.{u, w} k Ω M).V)

/-- The mate of the SAME point map acts on the original skyscraper index. -/
def fieldSkyscraperIndexMap (g : Gal(Ω/k)) :
    (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafFunctor
      (A := AddCommGrpCat.{max u w}) ⟶
    (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafFunctor :=
  conjugateEquiv
    (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafAdjunction
    (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafAdjunction
    (fieldGaloisPointEndomorphism.{u, w} k Ω g).sheafFiber

/-- The diagonal is the ACTUAL inverse-index mate followed by the same module action. -/
def fieldSkyscraperDiagonalMap
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) (g : Gal(Ω/k)) :
    fieldSkyscraper.{u, w} k Ω M ⟶ fieldSkyscraper.{u, w} k Ω M :=
  (fieldSkyscraperIndexMap.{u, w} k Ω g⁻¹).app
      ((fieldModuleAbAction.{u, w} k Ω M).V) ≫
    (smallEtaleGeometricPointCommon.{u, w}
      (Spec.algebraMap k Ω)).skyscraperSheafFunctor.map
        ((fieldModuleAbAction.{u, w} k Ω M).ρ g).asHom

/-- Every product coordinate is the SAME inverse-index diagonal formula. -/
theorem fieldSkyscraperDiagonalMap_π
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) (g : Gal(Ω/k))
    (U : (Spec (.of k)).Etale)
    (z : (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).fiber.obj U) :
    (fieldSkyscraperDiagonalMap.{u, w} k Ω M g).hom.app (op U) ≫
        Pi.π (fun _ : (smallEtaleGeometricPointCommon.{u, w}
          (Spec.algebraMap k Ω)).fiber.obj U =>
            (fieldModuleAbAction.{u, w} k Ω M).V) z =
      Pi.π (fun _ : (smallEtaleGeometricPointCommon.{u, w}
          (Spec.algebraMap k Ω)).fiber.obj U =>
            (fieldModuleAbAction.{u, w} k Ω M).V)
        ((fieldGaloisCommonFiberMap.{u, w} k Ω g⁻¹).app U z) ≫
          ((fieldModuleAbAction.{u, w} k Ω M).ρ g).asHom := by
  have hmap (Φ : (Spec (.of k)).smallEtaleTopology.Point.{max u w})
      {A B : AddCommGrpCat.{max u w}} (t : A ⟶ B)
      (V : (Spec (.of k)).Etale) (y : Φ.fiber.obj V) :
      (Φ.skyscraperSheafFunctor.map t).hom.app (op V) ≫ Pi.π (fun _ : Φ.fiber.obj V => B) y =
        Pi.π (fun _ : Φ.fiber.obj V => A) y ≫ t := by
    exact Pi.map_π (fun _ => t) y
  let Φ := smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)
  let C := (fieldModuleAbAction.{u, w} k Ω M).V
  let a := ((fieldModuleAbAction.{u, w} k Ω M).ρ g).asHom
  let B := (fieldSkyscraperIndexMap.{u, w} k Ω g⁻¹).app C
  have hm := hmap Φ a U z
  have hb : B.hom.app (op U) ≫ Pi.π (fun _ : Φ.fiber.obj U => C) z =
      Pi.π (fun _ : Φ.fiber.obj U => C)
        ((fieldGaloisCommonFiberMap.{u, w} k Ω g⁻¹).app U z) :=
    GrothendieckTopology.Point.conjugateEquiv_sheafFiber_app_π
      (fieldGaloisPointEndomorphism.{u, w} k Ω g⁻¹) C U z
  change B.hom.app (op U) ≫ ((Φ.skyscraperSheafFunctor.map a).hom.app (op U) ≫
    Pi.π (fun _ : Φ.fiber.obj U => C) z) = _
  exact (congrArg (fun t => B.hom.app (op U) ≫ t) hm).trans
    ((Category.assoc _ _ a).symm.trans (congrArg (fun t => t ≫ a) hb))


/-- The actual index mates preserve the identity. -/
theorem fieldSkyscraperIndexMap_one :
    fieldSkyscraperIndexMap.{u, w} k Ω (1 : Gal(Ω/k)) = 𝟙 _ := by
  change conjugateEquiv _ _ (fieldGaloisStalkMap.{u, w} k Ω 1) = _
  rw [fieldGaloisStalkMap_one]
  exact conjugateEquiv_id _

/-- The same point mates compose in the original group order. -/
theorem fieldSkyscraperIndexMap_mul (g h : Gal(Ω/k)) :
    fieldSkyscraperIndexMap.{u, w} k Ω (g * h) =
      fieldSkyscraperIndexMap.{u, w} k Ω g ≫ fieldSkyscraperIndexMap.{u, w} k Ω h := by
  change conjugateEquiv _ _ (fieldGaloisStalkMap.{u, w} k Ω (g * h)) = _
  rw [fieldGaloisStalkMap_mul]
  exact (conjugateEquiv_comp _ _ _ _ _).symm

/-- The genuine diagonal preserves the identity. -/
theorem fieldSkyscraperDiagonalMap_one
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    fieldSkyscraperDiagonalMap.{u, w} k Ω M 1 = 𝟙 _ := by
  change (fieldSkyscraperIndexMap.{u, w} k Ω (1 : Gal(Ω/k))⁻¹).app _ ≫ _ = _
  rw [inv_one, fieldSkyscraperIndexMap_one]
  simp only [NatTrans.id_app, Category.id_comp, map_one, End.one_asHom,
    CategoryTheory.Functor.map_id]

/-- The same inverse-index diagonal is a left group action on the actual skyscraper. -/
theorem fieldSkyscraperDiagonalMap_mul
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) (g h : Gal(Ω/k)) :
    fieldSkyscraperDiagonalMap.{u, w} k Ω M (g * h) =
      fieldSkyscraperDiagonalMap.{u, w} k Ω M h ≫
        fieldSkyscraperDiagonalMap.{u, w} k Ω M g := by
  let Φ := smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)
  let C := (fieldModuleAbAction.{u, w} k Ω M).V
  let a := ((fieldModuleAbAction.{u, w} k Ω M).ρ g).asHom
  let b := ((fieldModuleAbAction.{u, w} k Ω M).ρ h).asHom
  have hab : ((fieldModuleAbAction.{u, w} k Ω M).ρ (g * h)).asHom = b ≫ a := by
    rw [map_mul, End.mul_asHom]
  change (fieldSkyscraperIndexMap.{u, w} k Ω (g * h)⁻¹).app C ≫
      Φ.skyscraperSheafFunctor.map _ = _
  rw [mul_inv_rev, fieldSkyscraperIndexMap_mul, NatTrans.comp_app, hab,
    CategoryTheory.Functor.map_comp]
  have hn := (fieldSkyscraperIndexMap.{u, w} k Ω g⁻¹).naturality b
  change Φ.skyscraperSheafFunctor.map b ≫
      (fieldSkyscraperIndexMap.{u, w} k Ω g⁻¹).app C =
    (fieldSkyscraperIndexMap.{u, w} k Ω g⁻¹).app C ≫
      Φ.skyscraperSheafFunctor.map b at hn
  change _ = ((fieldSkyscraperIndexMap.{u, w} k Ω h⁻¹).app C ≫
    Φ.skyscraperSheafFunctor.map b) ≫
      ((fieldSkyscraperIndexMap.{u, w} k Ω g⁻¹).app C ≫
        Φ.skyscraperSheafFunctor.map a)
  simp only [Category.assoc]
  have hna : (fieldSkyscraperIndexMap.{u, w} k Ω g⁻¹).app C ≫
      (Φ.skyscraperSheafFunctor.map b ≫ Φ.skyscraperSheafFunctor.map a) =
    Φ.skyscraperSheafFunctor.map b ≫
      ((fieldSkyscraperIndexMap.{u, w} k Ω g⁻¹).app C ≫
        Φ.skyscraperSheafFunctor.map a) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫ Φ.skyscraperSheafFunctor.map a) hn.symm).trans
        (Category.assoc _ _ _))
  exact congrArg (fun t => (fieldSkyscraperIndexMap.{u, w} k Ω h⁻¹).app C ≫ t) hna

/-- The actual diagonal action, using the SAME point skyscraper and coefficient module. -/
def fieldSkyscraperDiagonalAction
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    Action (Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) Gal(Ω/k) where
  V := fieldSkyscraper.{u, w} k Ω M
  ρ := {
    toFun := fun g => End.of (fieldSkyscraperDiagonalMap.{u, w} k Ω M g)
    map_one' := by
      apply End.ext
      exact fieldSkyscraperDiagonalMap_one.{u, w} k Ω M
    map_mul' := fun g h => by
      apply End.ext
      exact fieldSkyscraperDiagonalMap_mul.{u, w} k Ω M g h }

/-- The diagram whose genuine limit is the invariant skyscraper. -/
abbrev fieldSkyscraperInvariantDiagram
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    SingleObj Gal(Ω/k) ⥤ Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w} :=
  SingleObj.functor (fieldSkyscraperDiagonalAction.{u, w} k Ω M).ρ

/-- Evaluation at one ORIGINAL geometric point is additive. -/
def fieldEquivariantFunctionEvaluation
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (U : (Spec (.of k)).Etale) (z : (fieldGeometricPoint k Ω).fiber.obj U) :
    FieldEquivariantFunctions.{u, w} k Ω U M →+
      (fieldModuleAbAction.{u, w} k Ω M).V where
  toFun h := h z
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The actual original-index functions enter the common point product by taking `down`. -/
def fieldEquivariantFunctionInclusion
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    fieldEquivariantFunctionPresheaf.{u, w} k Ω M ⟶
      (fieldSkyscraper.{u, w} k Ω M).obj where
  app U := Pi.lift (fun z => AddCommGrpCat.ofHom
    (fieldEquivariantFunctionEvaluation.{u, w} k Ω M U.unop z.down))
  naturality U V r := by
    apply Pi.hom_ext
    intro z
    let P := fieldEquivariantFunctionPresheaf.{u, w} k Ω M
    let K := (fieldSkyscraper.{u, w} k Ω M).obj
    let C := (fieldModuleAbAction.{u, w} k Ω M).V
    let Φ := smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)
    let iU := Pi.lift (fun y : Φ.fiber.obj U.unop => AddCommGrpCat.ofHom
      (fieldEquivariantFunctionEvaluation.{u, w} k Ω M U.unop y.down))
    let iV := Pi.lift (fun y : Φ.fiber.obj V.unop => AddCommGrpCat.ofHom
      (fieldEquivariantFunctionEvaluation.{u, w} k Ω M V.unop y.down))
    have hV : iV ≫ Pi.π (fun _ : Φ.fiber.obj V.unop => C) z =
        AddCommGrpCat.ofHom
          (fieldEquivariantFunctionEvaluation.{u, w} k Ω M V.unop z.down) :=
      Pi.lift_comp_π _ _
    have hr : K.map r ≫ Pi.π (fun _ : Φ.fiber.obj V.unop => C) z =
        Pi.π (fun _ : Φ.fiber.obj U.unop => C) (Φ.fiber.map r.unop z) :=
      GrothendieckTopology.Point.skyscraperSheaf_restrict_π Φ C r.unop z
    have hU : iU ≫ Pi.π (fun _ : Φ.fiber.obj U.unop => C)
          (Φ.fiber.map r.unop z) = AddCommGrpCat.ofHom
        (fieldEquivariantFunctionEvaluation.{u, w} k Ω M U.unop
          (Φ.fiber.map r.unop z).down) := Pi.lift_comp_π _ _
    have hleft := (Category.assoc (P.map r) iV _).trans
      (congrArg (fun t => P.map r ≫ t) hV)
    have hright := (Category.assoc iU (K.map r) _).trans
      ((congrArg (fun t => iU ≫ t) hr).trans hU)
    exact hleft.trans hright.symm

/-- Each common product coordinate recovers the SAME original function value. -/
@[reassoc]
theorem fieldEquivariantFunctionInclusion_π
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (U : (Spec (.of k)).Etale)
    (z : (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).fiber.obj U) :
    (fieldEquivariantFunctionInclusion.{u, w} k Ω M).app (op U) ≫
      Pi.π (fun _ : (smallEtaleGeometricPointCommon.{u, w}
        (Spec.algebraMap k Ω)).fiber.obj U => (fieldModuleAbAction.{u, w} k Ω M).V) z =
      AddCommGrpCat.ofHom (fieldEquivariantFunctionEvaluation.{u, w} k Ω M U z.down) :=
  Pi.lift_comp_π _ _


/-- The original equivariant functions are fixed by the actual diagonal, not by supplied data. -/
theorem fieldEquivariantFunctionInclusion_invariant
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) (g : Gal(Ω/k)) :
    fieldEquivariantFunctionInclusion.{u, w} k Ω M ≫
      (fieldSkyscraperDiagonalMap.{u, w} k Ω M g).hom =
        fieldEquivariantFunctionInclusion.{u, w} k Ω M := by
  apply NatTrans.ext
  funext U
  apply Pi.hom_ext
  intro z
  have hd := fieldSkyscraperDiagonalMap_π.{u, w} k Ω M g U.unop z
  have hi := fieldEquivariantFunctionInclusion_π.{u, w} k Ω M U.unop
    ((fieldGaloisCommonFiberMap.{u, w} k Ω g⁻¹).app U.unop z)
  have hdiag := (Category.assoc _ _ _).trans
    ((congrArg (fun t => (fieldEquivariantFunctionInclusion.{u, w} k Ω M).app U ≫ t)
      hd).trans ((Category.assoc _ _ _).symm.trans
        (congrArg (fun t => t ≫ ((fieldModuleAbAction.{u, w} k Ω M).ρ g).asHom) hi)))
  have hival := fieldEquivariantFunctionInclusion_π.{u, w} k Ω M U.unop z
  have hvalue : AddCommGrpCat.ofHom
      (fieldEquivariantFunctionEvaluation.{u, w} k Ω M U.unop
        ((fieldGaloisCommonFiberMap.{u, w} k Ω g⁻¹).app U.unop z).down) ≫
      ((fieldModuleAbAction.{u, w} k Ω M).ρ g).asHom =
    AddCommGrpCat.ofHom (fieldEquivariantFunctionEvaluation.{u, w} k Ω M U.unop z.down) := by
    ext h
    have hh := congrArg (fun a : DiscreteAbelianAction.underlying M => g • a)
      (h.map_smul g⁻¹ (show (fieldGeometricPoint k Ω).fiber.obj U.unop from z.down))
    exact hh.trans (smul_inv_smul g (h z.down))
  exact hdiag.trans (hvalue.trans hival.symm)

/-- A fixed section of the SAME common skyscraper yields its literal ORIGINAL-index function. -/
def fieldEquivariantFunctionOfInvariantSection
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (U : (Spec (.of k)).Etale)
    (q : (fieldSkyscraper.{u, w} k Ω M).obj.obj (op U))
    (hq : ∀ g : Gal(Ω/k), (fieldSkyscraperDiagonalMap.{u, w} k Ω M g).hom.app (op U) q = q) :
    FieldEquivariantFunctions.{u, w} k Ω U M where
  toFun z := Pi.π (fun _ : (smallEtaleGeometricPointCommon.{u, w}
    (Spec.algebraMap k Ω)).fiber.obj U => (fieldModuleAbAction.{u, w} k Ω M).V)
      (ULift.up z) q
  map_smul' g z := by
    let Φ := smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)
    let C := (fieldModuleAbAction.{u, w} k Ω M).V
    let : DistribMulAction Gal(Ω/k) C := DiscreteAbelianAction.instDistribMulAction M
    let y : Φ.fiber.obj U := ULift.up (g • z)
    have hfixed := congrArg (fun a => Pi.π (fun _ : Φ.fiber.obj U => C) y a) (hq g)
    have hcoord := congrArg (fun a => a q)
      (fieldSkyscraperDiagonalMap_π.{u, w} k Ω M g U y)
    change Pi.π (fun _ : Φ.fiber.obj U => C) y
        ((fieldSkyscraperDiagonalMap.{u, w} k Ω M g).hom.app (op U) q) =
      g • Pi.π (fun _ : Φ.fiber.obj U => C)
        ((fieldGaloisCommonFiberMap.{u, w} k Ω g⁻¹).app U y) q at hcoord
    have hy : (fieldGaloisCommonFiberMap.{u, w} k Ω g⁻¹).app U y = ULift.up z := by
      apply ULift.ext
      change g⁻¹ • (g • z) = z
      exact inv_smul_smul g z
    exact hfixed.symm.trans (hcoord.trans
      (congrArg (fun a => g • Pi.π (fun _ : Φ.fiber.obj U => C) a q) hy))


/-- The literal function presheaf is a cone of the actual invariant-skyscraper diagram. -/
def fieldInvariantFunctionCone
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    Cone (fieldSkyscraperInvariantDiagram.{u, w} k Ω M ⋙
      sheafToPresheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) where
  pt := fieldEquivariantFunctionPresheaf.{u, w} k Ω M
  π := {
    app := fun _ => fieldEquivariantFunctionInclusion.{u, w} k Ω M
    naturality := fun _ _ g => by
      change fieldEquivariantFunctionInclusion.{u, w} k Ω M =
        fieldEquivariantFunctionInclusion.{u, w} k Ω M ≫
          (fieldSkyscraperDiagonalMap.{u, w} k Ω M g).hom
      exact (fieldEquivariantFunctionInclusion_invariant.{u, w} k Ω M g).symm }

/-- The universal map at an original object is recovered from the actual product projections. -/
def fieldInvariantFunctionConeLift
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) (U : (Spec (.of k)).Etale)
    (c : Cone ((fieldSkyscraperInvariantDiagram.{u, w} k Ω M ⋙
      sheafToPresheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) ⋙
        (CategoryTheory.evaluation (Spec (.of k)).Etaleᵒᵖ AddCommGrpCat.{max u w}).obj (op U))) :
    c.pt ⟶ AddCommGrpCat.of (FieldEquivariantFunctions.{u, w} k Ω U M) :=
  AddCommGrpCat.ofHom {
    toFun := fun x => fieldEquivariantFunctionOfInvariantSection.{u, w} k Ω M U
      (c.π.app (SingleObj.star Gal(Ω/k)) x) (fun g => by
        have hw := c.w (j := SingleObj.star Gal(Ω/k)) (j' := SingleObj.star Gal(Ω/k)) g
        change c.π.app (SingleObj.star Gal(Ω/k)) ≫
            (fieldSkyscraperDiagonalMap.{u, w} k Ω M g).hom.app (op U) =
          c.π.app (SingleObj.star Gal(Ω/k)) at hw
        exact congrArg (fun a => a x) hw)
    map_zero' := by
      ext z
      exact ((Pi.π (fun _ : (smallEtaleGeometricPointCommon.{u, w}
        (Spec.algebraMap k Ω)).fiber.obj U => (fieldModuleAbAction.{u, w} k Ω M).V)
          (ULift.up z)).hom.comp (c.π.app (SingleObj.star Gal(Ω/k))).hom).map_zero
    map_add' := fun x y => by
      ext z
      exact ((Pi.π (fun _ : (smallEtaleGeometricPointCommon.{u, w}
        (Spec.algebraMap k Ω)).fiber.obj U => (fieldModuleAbAction.{u, w} k Ω M).V)
          (ULift.up z)).hom.comp (c.π.app (SingleObj.star Gal(Ω/k))).hom).map_add x y }

/-- The actual cone is limiting at EVERY original site object. -/
def fieldInvariantFunctionPointwiseLimit
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) (U : (Spec (.of k)).Etale) :
    IsLimit (((CategoryTheory.evaluation (Spec (.of k)).Etaleᵒᵖ AddCommGrpCat.{max u w}).obj
      (op U)).mapCone (fieldInvariantFunctionCone.{u, w} k Ω M)) where
  lift c := fieldInvariantFunctionConeLift.{u, w} k Ω M U c
  fac c j := by
    cases j
    apply Pi.hom_ext
    intro z
    have hi := fieldEquivariantFunctionInclusion_π.{u, w} k Ω M U z
    have hc := (Category.assoc (fieldInvariantFunctionConeLift.{u, w} k Ω M U c) _ _).trans
      (congrArg (fun a => fieldInvariantFunctionConeLift.{u, w} k Ω M U c ≫ a) hi)
    refine hc.trans ?_
    ext x
    change Pi.π (fun _ : (smallEtaleGeometricPointCommon.{u, w}
      (Spec.algebraMap k Ω)).fiber.obj U => (fieldModuleAbAction.{u, w} k Ω M).V)
        (ULift.up z.down) (c.π.app (SingleObj.star Gal(Ω/k)) x) =
      Pi.π (fun _ : (smallEtaleGeometricPointCommon.{u, w}
        (Spec.algebraMap k Ω)).fiber.obj U => (fieldModuleAbAction.{u, w} k Ω M).V)
          z (c.π.app (SingleObj.star Gal(Ω/k)) x)
    cases z
    rfl
  uniq c m hm := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    apply MulActionHom.ext
    intro z
    have hh := congrArg (fun a => (a ≫ Pi.π (fun _ : (smallEtaleGeometricPointCommon.{u, w}
      (Spec.algebraMap k Ω)).fiber.obj U => (fieldModuleAbAction.{u, w} k Ω M).V)
        (ULift.up z)) x) (hm (SingleObj.star Gal(Ω/k)))
    have hi := congrArg (fun a => a (m x))
      (fieldEquivariantFunctionInclusion_π.{u, w} k Ω M U (ULift.up z))
    exact hi.symm.trans hh

/-- Sheafness of the literal original-index functions is derived from the genuine
invariant limit. -/
theorem fieldEquivariantFunctionPresheaf_isSheaf
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    Presheaf.IsSheaf (Spec (.of k)).smallEtaleTopology
      (fieldEquivariantFunctionPresheaf.{u, w} k Ω M) :=
  Sheaf.isSheaf_of_isLimit (fieldSkyscraperInvariantDiagram.{u, w} k Ω M)
    (fieldInvariantFunctionCone.{u, w} k Ω M)
      (evaluationJointlyReflectsLimits _ (fun U =>
        fieldInvariantFunctionPointwiseLimit.{u, w} k Ω M U.unop))


/-- The genuine inverse sheaf has the literal original-index equivariant functions as values. -/
def fieldInvariantSkyscraperInverseSheafObj
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w} :=
  ⟨fieldEquivariantFunctionPresheaf.{u, w} k Ω M,
    fieldEquivariantFunctionPresheaf_isSheaf.{u, w} k Ω M⟩

/-- One functor on ALL original modules, with their same additive equivariant arrows. -/
def fieldInvariantSkyscraperInverseSheaf :
    DiscreteAbelianAction.{u, max u w} Gal(Ω/k) ⥤
      Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w} where
  obj M := fieldInvariantSkyscraperInverseSheafObj.{u, w} k Ω M
  map t := ⟨fieldEquivariantFunctionPresheafMap.{u, w} k Ω t⟩
  map_id M := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    ext h
    rfl
  map_comp t t' := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    ext h
    rfl

/-- The SAME actual inverse sheaf is an invariant cone in sheaves. -/
def fieldInvariantSkyscraperSheafCone
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    Cone (fieldSkyscraperInvariantDiagram.{u, w} k Ω M) where
  pt := fieldInvariantSkyscraperInverseSheafObj.{u, w} k Ω M
  π := {
    app := fun _ => ⟨fieldEquivariantFunctionInclusion.{u, w} k Ω M⟩
    naturality := fun _ _ g => by
      apply Sheaf.hom_ext
      exact (fieldEquivariantFunctionInclusion_invariant.{u, w} k Ω M g).symm }

/-- The canonical invariant cone is genuinely limiting in the actual common sheaf category. -/
def fieldInvariantSkyscraperSheafIsLimit
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    IsLimit (fieldInvariantSkyscraperSheafCone.{u, w} k Ω M) :=
  isLimitOfReflects
    (sheafToPresheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (show IsLimit (fieldInvariantFunctionCone.{u, w} k Ω M) from
      evaluationJointlyReflectsLimits _ (fun U =>
        fieldInvariantFunctionPointwiseLimit.{u, w} k Ω M U.unop))

/-- The fixed literal sheaf is identified with the genuine stock invariant limit. -/
def fieldInvariantSkyscraperLimitIso
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    limit (fieldSkyscraperInvariantDiagram.{u, w} k Ω M) ≅
      fieldInvariantSkyscraperInverseSheafObj.{u, w} k Ω M :=
  limit.isoLimitCone ⟨fieldInvariantSkyscraperSheafCone.{u, w} k Ω M,
    fieldInvariantSkyscraperSheafIsLimit.{u, w} k Ω M⟩


/-- The canonical stock-limit comparison has the SAME original invariant inclusion. -/
@[reassoc]
theorem fieldInvariantSkyscraperLimitIso_hom_inclusion
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    (fieldInvariantSkyscraperLimitIso.{u, w} k Ω M).hom ≫
      (fieldInvariantSkyscraperSheafCone.{u, w} k Ω M).π.app (SingleObj.star Gal(Ω/k)) =
        limit.π (fieldSkyscraperInvariantDiagram.{u, w} k Ω M) (SingleObj.star Gal(Ω/k)) :=
  limit.isoLimitCone_hom_π _ _

/-- The comparison inverse also recovers the SAME original invariant inclusion. -/
@[reassoc]
theorem fieldInvariantSkyscraperLimitIso_inv_π
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    (fieldInvariantSkyscraperLimitIso.{u, w} k Ω M).inv ≫
      limit.π (fieldSkyscraperInvariantDiagram.{u, w} k Ω M) (SingleObj.star Gal(Ω/k)) =
        (fieldInvariantSkyscraperSheafCone.{u, w} k Ω M).π.app (SingleObj.star Gal(Ω/k)) :=
  limit.isoLimitCone_inv_π _ _


/-- On original algebra embeddings the SAME Galois automorphism acts by postcomposition. -/
instance fieldAlgebraEmbeddingMulAction (A : Type u) [CommRing A] [Algebra k A] :
    MulAction Gal(Ω/k) (A →ₐ[k] Ω) where
  smul g ξ := g.toAlgHom.comp ξ
  one_smul ξ := by ext a; rfl
  mul_smul g h ξ := by ext a; rfl

/-- The accepted ORIGINAL finite-algebra fiber comparison is genuinely equivariant. -/
def fieldFiniteEtaleFiberEquivariant (A : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ) :
    (fieldGeometricPoint k Ω).fiber.obj ((fieldFiniteEtaleToEtale k).obj A) →[Gal(Ω/k)]
      (A.unop →ₐ[k] Ω) where
  toFun := (fieldFiniteEtaleGeometricFiberIso k Ω).hom.app A
  map_smul' g z := by
    exact fieldGaloisSpec_homEquivAlgHom k Ω g z.left z.w

/-- The inverse of that SAME actual spectrum/algebra comparison is equivariant as well. -/
def fieldFiniteEtaleFiberEquivariantInv (A : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ) :
    (A.unop →ₐ[k] Ω) →[Gal(Ω/k)]
      (fieldGeometricPoint k Ω).fiber.obj ((fieldFiniteEtaleToEtale k).obj A) :=
  MulActionHom.inverse (fieldFiniteEtaleFiberEquivariant k Ω A)
    ((fieldFiniteEtaleGeometricFiberIso k Ω).inv.app A)
    (fieldFiniteEtaleFiberEquiv k Ω A).symm_apply_apply
    (fieldFiniteEtaleFiberEquiv k Ω A).apply_symm_apply

/-- For EVERY original finite étale algebra, the inverse value is the literal Hom_G group. -/
def fieldInvariantFiniteEtaleSectionsEquiv
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (A : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ) :
    ((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M).obj.obj
      (op ((fieldFiniteEtaleToEtale k).obj A)) ≃+
        ((A.unop →ₐ[k] Ω) →[Gal(Ω/k)] DiscreteAbelianAction.underlying M) where
  toFun h := h.comp (fieldFiniteEtaleFiberEquivariantInv k Ω A)
  invFun h := h.comp (fieldFiniteEtaleFiberEquivariant k Ω A)
  left_inv h := by
    apply MulActionHom.ext
    intro z
    let h0 : FieldEquivariantFunctions.{u, w} k Ω ((fieldFiniteEtaleToEtale k).obj A) M := h
    exact congrArg h0 ((fieldFiniteEtaleFiberEquiv k Ω A).symm_apply_apply z)
  right_inv h := by
    apply MulActionHom.ext
    intro ξ
    exact congrArg h ((fieldFiniteEtaleFiberEquiv k Ω A).apply_symm_apply ξ)
  map_add' h h' := by ext ξ; rfl

/-- The comparison evaluates on the SAME original lift of an actual algebra embedding. -/
theorem fieldInvariantFiniteEtaleSectionsEquiv_apply
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (A : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ)
    (h : ((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M).obj.obj
      (op ((fieldFiniteEtaleToEtale k).obj A))) (ξ : A.unop →ₐ[k] Ω) :
    fieldInvariantFiniteEtaleSectionsEquiv.{u, w} k Ω M A h ξ =
      (show FieldEquivariantFunctions.{u, w} k Ω ((fieldFiniteEtaleToEtale k).obj A) M from h)
        ((fieldFiniteEtaleGeometricFiberIso k Ω).inv.app A ξ) := rfl

/-- Every ORIGINAL finite-algebra arrow has its literal embedding-precomposition restriction. -/
theorem fieldInvariantFiniteEtaleSectionsEquiv_restrict
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    {A B : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ} (r : A ⟶ B)
    (h : ((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M).obj.obj
      (op ((fieldFiniteEtaleToEtale k).obj B))) (ξ : A.unop →ₐ[k] Ω) :
    fieldInvariantFiniteEtaleSectionsEquiv.{u, w} k Ω M A
        (((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M).obj.map
          ((fieldFiniteEtaleToEtale k).map r).op h) ξ =
      fieldInvariantFiniteEtaleSectionsEquiv.{u, w} k Ω M B h (ξ.comp r.unop.hom.hom) := by
  let h0 : FieldEquivariantFunctions.{u, w} k Ω ((fieldFiniteEtaleToEtale k).obj B) M := h
  change h0 ((fieldGeometricPoint k Ω).fiber.map ((fieldFiniteEtaleToEtale k).map r)
      ((fieldFiniteEtaleGeometricFiberIso k Ω).inv.app A ξ)) =
    h0 ((fieldFiniteEtaleGeometricFiberIso k Ω).inv.app B (ξ.comp r.unop.hom.hom))
  apply congrArg h0
  apply (fieldFiniteEtaleFiberEquiv k Ω B).injective
  have hn := fieldFiniteEtaleFiberEquiv_naturality k Ω r
    ((fieldFiniteEtaleFiberEquiv k Ω A).symm ξ)
  exact hn.trans ((congrArg (fun a => a.comp r.unop.hom.hom)
    ((fieldFiniteEtaleFiberEquiv k Ω A).apply_symm_apply ξ)).trans
      ((fieldFiniteEtaleFiberEquiv k Ω B).apply_symm_apply (ξ.comp r.unop.hom.hom)).symm)

/-- All module arrows are their SAME original additive postcomposition on finite-algebra values. -/
theorem fieldInvariantFiniteEtaleSectionsEquiv_map
    {M N : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)} (t : M ⟶ N)
    (A : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ)
    (h : ((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M).obj.obj
      (op ((fieldFiniteEtaleToEtale k).obj A))) (ξ : A.unop →ₐ[k] Ω) :
    fieldInvariantFiniteEtaleSectionsEquiv.{u, w} k Ω N A
        (((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).map t).hom.app
          (op ((fieldFiniteEtaleToEtale k).obj A)) h) ξ =
      DiscreteAbelianAction.homToAdd t
        (fieldInvariantFiniteEtaleSectionsEquiv.{u, w} k Ω M A h ξ) :=
  rfl


/-- The actual coefficient action arrow is induced by the original stored module morphism. -/
def fieldModuleAbActionMap
    {M N : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)} (t : M ⟶ N) :
    fieldModuleAbAction.{u, w} k Ω M ⟶ fieldModuleAbAction.{u, w} k Ω N :=
  ((forget₂ (TopModuleCat.{max u w} ℤ) (ModuleCat.{max u w} ℤ) ⋙
    forget₂ (ModuleCat.{max u w} ℤ) AddCommGrpCat.{max u w}).mapAction Gal(Ω/k)).map t.hom.hom

omit [IsSepClosure k Ω] in
/-- Its group map is the SAME accepted original additive module map. -/
theorem fieldModuleAbActionMap_hom
    {M N : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)} (t : M ⟶ N) :
    (fieldModuleAbActionMap.{u, w} k Ω t).hom =
      (DiscreteAbelianAction.forget Gal(Ω/k)).map t := rfl

/-- Every original module arrow commutes with the SAME actual skyscraper diagonal. -/
theorem fieldSkyscraperDiagonalMap_naturality
    {M N : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)} (t : M ⟶ N) (g : Gal(Ω/k)) :
    fieldSkyscraperDiagonalMap.{u, w} k Ω M g ≫
      (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafFunctor.map
        (fieldModuleAbActionMap.{u, w} k Ω t).hom =
    (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafFunctor.map
        (fieldModuleAbActionMap.{u, w} k Ω t).hom ≫
      fieldSkyscraperDiagonalMap.{u, w} k Ω N g := by
  let Φ := smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)
  let I := fieldSkyscraperIndexMap.{u, w} k Ω g⁻¹
  let CM := (fieldModuleAbAction.{u, w} k Ω M).V
  let CN := (fieldModuleAbAction.{u, w} k Ω N).V
  let a := ((fieldModuleAbAction.{u, w} k Ω M).ρ g).asHom
  let b := ((fieldModuleAbAction.{u, w} k Ω N).ρ g).asHom
  let f := (fieldModuleAbActionMap.{u, w} k Ω t).hom
  have hc : a ≫ f = f ≫ b := (fieldModuleAbActionMap.{u, w} k Ω t).comm g
  have hn : Φ.skyscraperSheafFunctor.map f ≫ I.app CN =
      I.app CM ≫ Φ.skyscraperSheafFunctor.map f := I.naturality f
  change (I.app CM ≫ Φ.skyscraperSheafFunctor.map a) ≫ Φ.skyscraperSheafFunctor.map f =
    Φ.skyscraperSheafFunctor.map f ≫ (I.app CN ≫ Φ.skyscraperSheafFunctor.map b)
  calc
    _ = I.app CM ≫ Φ.skyscraperSheafFunctor.map (a ≫ f) :=
      (Category.assoc _ _ _).trans (congrArg (fun q => I.app CM ≫ q)
        (Φ.skyscraperSheafFunctor.map_comp a f).symm)
    _ = I.app CM ≫ Φ.skyscraperSheafFunctor.map (f ≫ b) :=
      congrArg (fun q => I.app CM ≫ Φ.skyscraperSheafFunctor.map q) hc
    _ = I.app CM ≫ (Φ.skyscraperSheafFunctor.map f ≫ Φ.skyscraperSheafFunctor.map b) :=
      congrArg (fun q => I.app CM ≫ q) (Φ.skyscraperSheafFunctor.map_comp f b)
    _ = (I.app CM ≫ Φ.skyscraperSheafFunctor.map f) ≫ Φ.skyscraperSheafFunctor.map b :=
      (Category.assoc _ _ _).symm
    _ = (Φ.skyscraperSheafFunctor.map f ≫ I.app CN) ≫ Φ.skyscraperSheafFunctor.map b :=
      congrArg (fun q => q ≫ Φ.skyscraperSheafFunctor.map b) hn.symm
    _ = _ := Category.assoc _ _ _

/-- The invariant diagrams retain every original module map on the SAME skyscraper. -/
def fieldSkyscraperInvariantDiagramMap
    {M N : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)} (t : M ⟶ N) :
    fieldSkyscraperInvariantDiagram.{u, w} k Ω M ⟶
      fieldSkyscraperInvariantDiagram.{u, w} k Ω N :=
  SingleObj.natTrans
    ((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafFunctor.map
      (fieldModuleAbActionMap.{u, w} k Ω t).hom)
    (fieldSkyscraperDiagonalMap_naturality.{u, w} k Ω t)

/-- One functor fixes all actual invariant diagrams and their original coefficient maps. -/
def fieldSkyscraperInvariantDiagrams :
    DiscreteAbelianAction.{u, max u w} Gal(Ω/k) ⥤
      SingleObj Gal(Ω/k) ⥤
        Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w} where
  obj M := fieldSkyscraperInvariantDiagram.{u, w} k Ω M
  map t := fieldSkyscraperInvariantDiagramMap.{u, w} k Ω t
  map_id M := by
    apply NatTrans.ext
    funext j
    exact (congrArg
      (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafFunctor.map
      ((DiscreteAbelianAction.forget Gal(Ω/k)).map_id M)).trans
      ((smallEtaleGeometricPointCommon.{u, w}
        (Spec.algebraMap k Ω)).skyscraperSheafFunctor.map_id _)
  map_comp t t' := by
    apply NatTrans.ext
    funext j
    exact (congrArg
      (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafFunctor.map
      ((DiscreteAbelianAction.forget Gal(Ω/k)).map_comp t t')).trans
      ((smallEtaleGeometricPointCommon.{u, w}
        (Spec.algebraMap k Ω)).skyscraperSheafFunctor.map_comp _ _)

/-- The invariant inclusion is natural for EVERY original module arrow. -/
theorem fieldInvariantSkyscraperInclusion_naturality
    {M N : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)} (t : M ⟶ N) :
    (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).map t ≫
      (fieldInvariantSkyscraperSheafCone.{u, w} k Ω N).π.app (SingleObj.star Gal(Ω/k)) =
    (fieldInvariantSkyscraperSheafCone.{u, w} k Ω M).π.app (SingleObj.star Gal(Ω/k)) ≫
      (fieldSkyscraperInvariantDiagramMap.{u, w} k Ω t).app (SingleObj.star Gal(Ω/k)) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply Pi.hom_ext
  intro z
  let Φ := smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)
  let CM := (fieldModuleAbAction.{u, w} k Ω M).V
  let CN := (fieldModuleAbAction.{u, w} k Ω N).V
  let f := (fieldModuleAbActionMap.{u, w} k Ω t).hom
  let iM := (fieldEquivariantFunctionInclusion.{u, w} k Ω M).app U
  let iN := (fieldEquivariantFunctionInclusion.{u, w} k Ω N).app U
  let a := ((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).map t).hom.app U
  have hN := fieldEquivariantFunctionInclusion_π.{u, w} k Ω N U.unop z
  have hmap : (Φ.skyscraperSheafFunctor.map f).hom.app U ≫
      Pi.π (fun _ : Φ.fiber.obj U.unop => CN) z =
    Pi.π (fun _ : Φ.fiber.obj U.unop => CM) z ≫ f := Pi.map_π (fun _ => f) z
  have hM := fieldEquivariantFunctionInclusion_π.{u, w} k Ω M U.unop z
  have hleft := (Category.assoc a iN _).trans (congrArg (fun q => a ≫ q) hN)
  have hright := (Category.assoc iM _ _).trans
    ((congrArg (fun q => iM ≫ q) hmap).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (fun q => q ≫ f) hM)))
  refine hleft.trans (Eq.trans ?_ hright.symm)
  ext h
  rfl

/-- The comparison to the genuine invariant limit is ONE natural additive sheaf isomorphism. -/
def fieldInvariantSkyscraperLimitNatIso :
    fieldSkyscraperInvariantDiagrams.{u, w} k Ω ⋙ lim ≅
      fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω :=
  NatIso.ofComponents (fieldInvariantSkyscraperLimitIso.{u, w} k Ω) (fun {M N} t => by
    apply (fieldInvariantSkyscraperSheafIsLimit.{u, w} k Ω N).hom_ext
    intro j
    cases j
    have hN := fieldInvariantSkyscraperLimitIso_hom_inclusion.{u, w} k Ω N
    have hM := fieldInvariantSkyscraperLimitIso_hom_inclusion.{u, w} k Ω M
    have hi := fieldInvariantSkyscraperInclusion_naturality.{u, w} k Ω t
    have hl := (Category.assoc _ _ _).trans
      ((congrArg (fun q => limMap (fieldSkyscraperInvariantDiagramMap.{u, w} k Ω t) ≫ q)
        hN).trans (limMap_π (fieldSkyscraperInvariantDiagramMap.{u, w} k Ω t)
          (SingleObj.star Gal(Ω/k))))
    have hr := (Category.assoc _ _ _).trans
      ((congrArg (fun q => (fieldInvariantSkyscraperLimitIso.{u, w} k Ω M).hom ≫ q)
        hi).trans ((Category.assoc _ _ _).symm.trans
          (congrArg (fun q => q ≫
            (fieldSkyscraperInvariantDiagramMap.{u, w} k Ω t).app (SingleObj.star Gal(Ω/k))) hM)))
    exact hl.trans hr.symm)


/-- The object formula retains the SAME original-index pointwise abelian group. -/
theorem fieldInvariantSkyscraperInverseSheaf_value
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) (U : (Spec (.of k)).Etale) :
    ((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M).obj.obj (op U) =
      AddCommGrpCat.of (FieldEquivariantFunctions.{u, w} k Ω U M) := rfl

/-- Every original restriction is the literal original geometric-fiber precomposition. -/
theorem fieldInvariantSkyscraperInverseSheaf_restrict_apply
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    {U V : (Spec (.of k)).Etale} (r : V ⟶ U)
    (h : FieldEquivariantFunctions.{u, w} k Ω U M)
    (z : (fieldGeometricPoint k Ω).fiber.obj V) :
    (show FieldEquivariantFunctions.{u, w} k Ω V M from
      ((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M).obj.map r.op h) z =
        h ((fieldGeometricPoint k Ω).fiber.map r z) := rfl

/-- Every original module arrow acts by its SAME additive function, point by point. -/
theorem fieldInvariantSkyscraperInverseSheaf_map_apply
    {M N : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)} (t : M ⟶ N)
    (U : (Spec (.of k)).Etale) (h : FieldEquivariantFunctions.{u, w} k Ω U M)
    (z : (fieldGeometricPoint k Ω).fiber.obj U) :
    (show FieldEquivariantFunctions.{u, w} k Ω U N from
      ((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).map t).hom.app (op U) h) z =
        DiscreteAbelianAction.homToAdd t (h z) := rfl

/-- The inverse finite-algebra comparison uses the SAME original embedding at every point. -/
theorem fieldInvariantFiniteEtaleSectionsEquiv_symm_apply
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (A : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ)
    (h : (A.unop →ₐ[k] Ω) →[Gal(Ω/k)] DiscreteAbelianAction.underlying M)
    (z : (fieldGeometricPoint k Ω).fiber.obj ((fieldFiniteEtaleToEtale k).obj A)) :
    (show FieldEquivariantFunctions.{u, w} k Ω ((fieldFiniteEtaleToEtale k).obj A) M from
      (fieldInvariantFiniteEtaleSectionsEquiv.{u, w} k Ω M A).symm h) z =
        h ((fieldFiniteEtaleGeometricFiberIso k Ω).hom.app A z) := rfl

/-- The source construction fixes the actual diagonal, inclusion, invariant limit and all maps. -/
def FieldInvariantSkyscraperLimitLaws : Prop :=
  (∀ M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k),
    Nonempty (IsLimit (fieldInvariantSkyscraperSheafCone.{u, w} k Ω M))) ∧
  (∀ M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k),
    fieldSkyscraperDiagonalMap.{u, w} k Ω M 1 = 𝟙 _) ∧
  (∀ (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) (g h : Gal(Ω/k)),
    fieldSkyscraperDiagonalMap.{u, w} k Ω M (g * h) =
      fieldSkyscraperDiagonalMap.{u, w} k Ω M h ≫
        fieldSkyscraperDiagonalMap.{u, w} k Ω M g) ∧
  (∀ (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) (g : Gal(Ω/k))
      (U : (Spec (.of k)).Etale)
      (z : (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).fiber.obj U),
    (fieldSkyscraperDiagonalMap.{u, w} k Ω M g).hom.app (op U) ≫
        Pi.π (fun _ : (smallEtaleGeometricPointCommon.{u, w}
          (Spec.algebraMap k Ω)).fiber.obj U => (fieldModuleAbAction.{u, w} k Ω M).V) z =
      Pi.π (fun _ : (smallEtaleGeometricPointCommon.{u, w}
        (Spec.algebraMap k Ω)).fiber.obj U => (fieldModuleAbAction.{u, w} k Ω M).V)
        ((fieldGaloisCommonFiberMap.{u, w} k Ω g⁻¹).app U z) ≫
          ((fieldModuleAbAction.{u, w} k Ω M).ρ g).asHom) ∧
  (∀ (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) (U : (Spec (.of k)).Etale)
      (z : (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).fiber.obj U),
    (fieldEquivariantFunctionInclusion.{u, w} k Ω M).app (op U) ≫
      Pi.π (fun _ : (smallEtaleGeometricPointCommon.{u, w}
        (Spec.algebraMap k Ω)).fiber.obj U => (fieldModuleAbAction.{u, w} k Ω M).V) z =
        AddCommGrpCat.ofHom (fieldEquivariantFunctionEvaluation.{u, w} k Ω M U z.down)) ∧
  (∀ M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k),
    (fieldInvariantSkyscraperLimitNatIso.{u, w} k Ω).app M =
      fieldInvariantSkyscraperLimitIso.{u, w} k Ω M) ∧
  (∀ M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k),
    (fieldInvariantSkyscraperLimitIso.{u, w} k Ω M).hom ≫
      (fieldInvariantSkyscraperSheafCone.{u, w} k Ω M).π.app (SingleObj.star Gal(Ω/k)) =
        limit.π (fieldSkyscraperInvariantDiagram.{u, w} k Ω M) (SingleObj.star Gal(Ω/k))) ∧
  (∀ M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k),
    (fieldInvariantSkyscraperLimitIso.{u, w} k Ω M).inv ≫
      limit.π (fieldSkyscraperInvariantDiagram.{u, w} k Ω M) (SingleObj.star Gal(Ω/k)) =
        (fieldInvariantSkyscraperSheafCone.{u, w} k Ω M).π.app (SingleObj.star Gal(Ω/k))) ∧
  (∀ {M N : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)} (t : M ⟶ N) (g : Gal(Ω/k)),
    fieldSkyscraperDiagonalMap.{u, w} k Ω M g ≫
      (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafFunctor.map
        (fieldModuleAbActionMap.{u, w} k Ω t).hom =
    (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafFunctor.map
        (fieldModuleAbActionMap.{u, w} k Ω t).hom ≫
      fieldSkyscraperDiagonalMap.{u, w} k Ω N g) ∧
  (∀ {M N : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)} (t : M ⟶ N),
    (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).map t ≫
      (fieldInvariantSkyscraperSheafCone.{u, w} k Ω N).π.app (SingleObj.star Gal(Ω/k)) =
    (fieldInvariantSkyscraperSheafCone.{u, w} k Ω M).π.app (SingleObj.star Gal(Ω/k)) ≫
      (fieldSkyscraperInvariantDiagramMap.{u, w} k Ω t).app (SingleObj.star Gal(Ω/k))) ∧
  ∀ {M N : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)} (t : M ⟶ N),
    limMap (fieldSkyscraperInvariantDiagramMap.{u, w} k Ω t) ≫
      (fieldInvariantSkyscraperLimitIso.{u, w} k Ω N).hom =
    (fieldInvariantSkyscraperLimitIso.{u, w} k Ω M).hom ≫
      (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).map t

/-- ALL original objects, restrictions, module maps and pointwise operations are retained. -/
def FieldInvariantSkyscraperOriginalValuesLaws : Prop :=
  (∀ (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) (U : (Spec (.of k)).Etale),
    ((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M).obj.obj (op U) =
      AddCommGrpCat.of (FieldEquivariantFunctions.{u, w} k Ω U M)) ∧
  (∀ (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) {U V : (Spec (.of k)).Etale}
      (r : V ⟶ U) (h : FieldEquivariantFunctions.{u, w} k Ω U M)
      (z : (fieldGeometricPoint k Ω).fiber.obj V),
    (show FieldEquivariantFunctions.{u, w} k Ω V M from
      ((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M).obj.map r.op h) z =
        h ((fieldGeometricPoint k Ω).fiber.map r z)) ∧
  (∀ {M N : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)} (t : M ⟶ N)
      (U : (Spec (.of k)).Etale) (h : FieldEquivariantFunctions.{u, w} k Ω U M)
      (z : (fieldGeometricPoint k Ω).fiber.obj U),
    (show FieldEquivariantFunctions.{u, w} k Ω U N from
      ((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).map t).hom.app (op U) h) z =
        DiscreteAbelianAction.homToAdd t (h z)) ∧
  (∀ M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k),
    (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).map (𝟙 M) = 𝟙 _) ∧
  (∀ {M N P : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)} (t : M ⟶ N) (t' : N ⟶ P),
    (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).map (t ≫ t') =
      (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).map t ≫
        (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).map t') ∧
  (∀ (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) (U : (Spec (.of k)).Etale)
      (h h' : FieldEquivariantFunctions.{u, w} k Ω U M)
      (z : (fieldGeometricPoint k Ω).fiber.obj U),
    (h + h') z = h z + h' z) ∧
  (∀ (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) (U : (Spec (.of k)).Etale)
      (h : FieldEquivariantFunctions.{u, w} k Ω U M)
      (z : (fieldGeometricPoint k Ω).fiber.obj U), (-h) z = -(h z)) ∧
  ∀ (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) (U : (Spec (.of k)).Etale)
      (z : (fieldGeometricPoint k Ω).fiber.obj U),
    (0 : FieldEquivariantFunctions.{u, w} k Ω U M) z = 0

/-- EVERY finite algebra and algebra/module arrow uses the SAME original fiber family. -/
def FieldInvariantSkyscraperFiniteValuesLaws : Prop :=
  (∀ (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
      (A : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ)
      (h : ((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M).obj.obj
        (op ((fieldFiniteEtaleToEtale k).obj A))) (ξ : A.unop →ₐ[k] Ω),
    fieldInvariantFiniteEtaleSectionsEquiv.{u, w} k Ω M A h ξ =
      (show FieldEquivariantFunctions.{u, w} k Ω ((fieldFiniteEtaleToEtale k).obj A) M from h)
        ((fieldFiniteEtaleGeometricFiberIso k Ω).inv.app A ξ)) ∧
  (∀ (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
      (A : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ)
      (h : (A.unop →ₐ[k] Ω) →[Gal(Ω/k)] DiscreteAbelianAction.underlying M)
      (z : (fieldGeometricPoint k Ω).fiber.obj ((fieldFiniteEtaleToEtale k).obj A)),
    (show FieldEquivariantFunctions.{u, w} k Ω ((fieldFiniteEtaleToEtale k).obj A) M from
      (fieldInvariantFiniteEtaleSectionsEquiv.{u, w} k Ω M A).symm h) z =
        h ((fieldFiniteEtaleGeometricFiberIso k Ω).hom.app A z)) ∧
  (∀ (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
      {A B : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ} (r : A ⟶ B)
      (h : ((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M).obj.obj
        (op ((fieldFiniteEtaleToEtale k).obj B))) (ξ : A.unop →ₐ[k] Ω),
    fieldInvariantFiniteEtaleSectionsEquiv.{u, w} k Ω M A
        (((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M).obj.map
          ((fieldFiniteEtaleToEtale k).map r).op h) ξ =
      fieldInvariantFiniteEtaleSectionsEquiv.{u, w} k Ω M B h (ξ.comp r.unop.hom.hom)) ∧
  (∀ {M N : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)} (t : M ⟶ N)
      (A : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ)
      (h : ((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M).obj.obj
        (op ((fieldFiniteEtaleToEtale k).obj A))) (ξ : A.unop →ₐ[k] Ω),
    fieldInvariantFiniteEtaleSectionsEquiv.{u, w} k Ω N A
        (((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).map t).hom.app
          (op ((fieldFiniteEtaleToEtale k).obj A)) h) ξ =
      DiscreteAbelianAction.homToAdd t
        (fieldInvariantFiniteEtaleSectionsEquiv.{u, w} k Ω M A h ξ)) ∧
  ∀ (A : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ) (g : Gal(Ω/k))
      (z : (fieldGeometricPoint k Ω).fiber.obj ((fieldFiniteEtaleToEtale k).obj A)),
    (fieldFiniteEtaleGeometricFiberIso k Ω).hom.app A (g • z) =
      g.toAlgHom.comp ((fieldFiniteEtaleGeometricFiberIso k Ω).hom.app A z)

/-- The full original-site inverse-sheaf construction, including its genuine invariant limit. -/
theorem original_field_invariant_skyscraper_inverse_sheaf :
    FieldInvariantSkyscraperLimitLaws.{u, w} k Ω ∧
      FieldInvariantSkyscraperOriginalValuesLaws.{u, w} k Ω ∧
        FieldInvariantSkyscraperFiniteValuesLaws.{u, w} k Ω := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨fun M => ⟨fieldInvariantSkyscraperSheafIsLimit.{u, w} k Ω M⟩,
      fieldSkyscraperDiagonalMap_one.{u, w} k Ω,
      fieldSkyscraperDiagonalMap_mul.{u, w} k Ω,
      fieldSkyscraperDiagonalMap_π.{u, w} k Ω,
      fieldEquivariantFunctionInclusion_π.{u, w} k Ω,
      fun _ => rfl,
      fieldInvariantSkyscraperLimitIso_hom_inclusion.{u, w} k Ω,
      fieldInvariantSkyscraperLimitIso_inv_π.{u, w} k Ω,
      fieldSkyscraperDiagonalMap_naturality.{u, w} k Ω,
      fieldInvariantSkyscraperInclusion_naturality.{u, w} k Ω, ?_⟩
    intro M N t
    exact (fieldInvariantSkyscraperLimitNatIso.{u, w} k Ω).hom.naturality t
  · exact ⟨fieldInvariantSkyscraperInverseSheaf_value.{u, w} k Ω,
      fieldInvariantSkyscraperInverseSheaf_restrict_apply.{u, w} k Ω,
      fieldInvariantSkyscraperInverseSheaf_map_apply.{u, w} k Ω,
      (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).map_id,
      (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).map_comp,
      fun _ _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ => rfl⟩
  · refine ⟨fieldInvariantFiniteEtaleSectionsEquiv_apply.{u, w} k Ω,
      fieldInvariantFiniteEtaleSectionsEquiv_symm_apply.{u, w} k Ω,
      fieldInvariantFiniteEtaleSectionsEquiv_restrict.{u, w} k Ω,
      fieldInvariantFiniteEtaleSectionsEquiv_map.{u, w} k Ω, ?_⟩
    intro A g z
    exact (fieldFiniteEtaleFiberEquivariant k Ω A).map_smul g z

end AlgebraicGeometry.Scheme.DerivedSections
