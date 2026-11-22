/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.InjectiveMappingSupport
import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyCategory
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanWhitehead
import Mathlib.AlgebraicTopology.ModelCategory.Homotopy
import Mathlib.AlgebraicTopology.SimplicialSet.PiZero
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# Original injective mapping components and homotopy classes

The original scalar interval cylinder and native homotopy quotients relate
the actual mapping end to the canonical model localization on the same
presheaf category. The source site and its ordinary Hom universes are retained.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u v w

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MonoidalCategory
open CartesianMonoidalCategory MonoidalClosed Opposite
open scoped MonoidalClosed Simplicial SSet.modelCategoryQuillen

attribute [local instance] SimplicialPresheaf.InjectiveKan.modelCategory
attribute [local instance] SimplicialPresheaf.scalarEnrichment

@[instance_reducible]
private def coefficientScalarCategory : EnrichedCategory SSet.{u} SSet.{u} := by
  letI : MonoidalClosed SSet.{u} := FunctorToTypes.monoidalClosed
  exact MonoidalClosed.enrichedCategorySelf SSet.{u}

@[instance_reducible]
private def coefficientScalarOrdinary : EnrichedOrdinaryCategory SSet.{u} SSet.{u} := by
  letI : MonoidalClosed SSet.{u} := FunctorToTypes.monoidalClosed
  exact MonoidalClosed.enrichedOrdinaryCategorySelf SSet.{u}

attribute [local instance 2000] coefficientScalarCategory coefficientScalarOrdinary

namespace SimplicialPresheaf.InjectiveKan

variable {D : Type w} [Category.{v} D] [Small.{u} D] [LocallySmall.{u} D]

private def scalarProjection (A : SimplicialPresheaf.{u} D) (K : SSet.{u}) :
    ((scalarTensor.obj A).obj K) ⟶ A where
  app d := fst (A.obj d) K
  naturality := by
    intro d e f
    ext n x
    rfl

private def scalarIntervalZero (A : SimplicialPresheaf.{u} D) :
    A ⟶ ((scalarTensor.obj A).obj (Δ[1] : SSet.{u})) where
  app d := SSet.ι₀ (X := A.obj d)
  naturality := by
    intro d e f
    ext n x
    rfl

private def scalarIntervalOne (A : SimplicialPresheaf.{u} D) :
    A ⟶ ((scalarTensor.obj A).obj (Δ[1] : SSet.{u})) where
  app d := SSet.ι₁ (X := A.obj d)
  naturality := by
    intro d e f
    ext n x
    rfl

private abbrev originalScalarCylinder (A : SimplicialPresheaf.{u} D) : Cylinder A where
  I := (scalarTensor.obj A).obj (Δ[1] : SSet.{u})
  i₀ := scalarIntervalZero A
  i₁ := scalarIntervalOne A
  π := scalarProjection A (Δ[1] : SSet.{u})
  i₀_π := by
    ext d n x
    rfl
  i₁_π := by
    ext d n x
    rfl
  weakEquivalence_π := by
    apply (weakEquivalence_iff _).mpr
    change (data D).model.categoryWithWeakEquivalences.weakEquivalences _
    rw [(data D).weakEquivalences_eq]
    intro d
    exact (weakEquivalence_iff _).mp
      (SSet.modelCategoryQuillen.standardCylinder (A.obj d)).weakEquivalence_π

private def scalarZeroToUnit : (Δ[0] : SSet.{u}) ≅ 𝟙_ SSet.{u} :=
  SSet.stdSimplex.isTerminalObj₀.uniqueUpToIso isTerminalTensorUnit

private def scalarZeroUnit (A : SimplicialPresheaf.{u} D) :
    ((scalarTensor.obj A).obj (Δ[0] : SSet.{u})) ≅ A :=
  ((scalarTensor.obj A).mapIso scalarZeroToUnit).trans (ρ_ A)

omit [Small.{u} D] [LocallySmall.{u} D] in
private theorem scalarZeroUnit_hom (A : SimplicialPresheaf.{u} D) :
    (scalarZeroUnit A).hom = scalarProjection A (Δ[0] : SSet.{u}) := by
  ext d n x
  rfl

private instance originalScalarCylinder_good (A : SimplicialPresheaf.{u} D) :
    (originalScalarCylinder A).IsGood where
  cofibration_i := by
    apply (cofibration_iff _).mpr
    change (data D).model.categoryWithCofibrations.cofibrations _
    rw [(data D).cofibrations_eq]
    apply (NatTrans.mono_iff_mono_app _).mpr
    intro d
    let ev := (evaluation Dᵒᵖ SSet.{u}).obj d
    let c := coprodComparison ev A A
    let _ : IsIso c := by
      dsimp [c]
      infer_instance
    let i₀ : A.obj d ⟶ (originalScalarCylinder A).I.obj d :=
      (originalScalarCylinder A).i₀.app d
    let i₁ : A.obj d ⟶ (originalScalarCylinder A).I.obj d :=
      (originalScalarCylinder A).i₁.app d
    have hc : c ≫ (originalScalarCylinder A).i.app d = coprod.desc i₀ i₁ := by
      dsimp [c, ev, coprodComparison]
      apply coprod.hom_ext
      · rw [coprod.inl_desc_assoc, coprod.inl_desc]
        change ((coprod.inl : A ⟶ A ⨿ A) ≫ (originalScalarCylinder A).i).app d = _
        rw [(originalScalarCylinder A).inl_i]
      · rw [coprod.inr_desc_assoc, coprod.inr_desc]
        change ((coprod.inr : A ⟶ A ⨿ A) ≫ (originalScalarCylinder A).i).app d = _
        rw [(originalScalarCylinder A).inr_i]
    have hs : Mono (coprod.desc i₀ i₁) := by
      have h := (cofibration_iff _).mp
        (SSet.modelCategoryQuillen.standardCylinder_isGood (A.obj d)).cofibration_i
      change Mono (SSet.modelCategoryQuillen.standardCylinder (A.obj d)).i at h
      exact h
    let _ : Mono (c ≫ (originalScalarCylinder A).i.app d) := by
      rw [hc]
      exact hs
    have he : (originalScalarCylinder A).i.app d =
        inv c ≫ (c ≫ (originalScalarCylinder A).i.app d) := by simp
    rw [he]
    infer_instance

private abbrev zeroHomEquiv (A Z : SimplicialPresheaf.{u} D) :
    (innerHom A Z) _⦋0⦌ ≃ (A ⟶ Z) :=
  (innerHomSimplexEquiv A Z (op ⦋0⦌)).trans
    (Iso.homCongr (scalarZeroUnit A) (Iso.refl Z))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem originalHomUnit_projection (A Z : SimplicialPresheaf.{u} D)
    (g : A ⟶ Z) (d : Dᵒᵖ) :
    (SSet.unitHomEquiv (innerHom A Z)).symm (innerHomHomEquiv A Z g) ≫ innerHomπ A Z d =
      curry' (g.app d) := by
  simp only [innerHomHomEquiv, Equiv.trans_apply, Equiv.symm_apply_apply]
  rw [Enriched.FunctorCategory.homEquiv_apply_π]
  rfl

private theorem scalarZero_transpose_vertex (A Z : SimplicialPresheaf.{u} D) (g : A ⟶ Z) :
    scalarTensorHomEquiv A (Δ[0] : SSet.{u}) Z ((scalarZeroUnit A).hom ≫ g) =
      SSet.yonedaEquiv.symm (innerHomHomEquiv A Z g) := by
  have h : scalarTensorHomEquiv A (Δ[0] : SSet.{u}) Z ((scalarZeroUnit A).hom ≫ g) =
      scalarZeroToUnit.hom ≫
        (SSet.unitHomEquiv (innerHom A Z)).symm (innerHomHomEquiv A Z g) := by
    apply innerHom_ext
    intro d
    rw [scalarTensorHomEquiv_π, Category.assoc, originalHomUnit_projection]
    change curry (((A.obj d ◁ scalarZeroToUnit.hom) ≫ (ρ_ (A.obj d)).hom) ≫ g.app d) = _
    rw [Category.assoc, curry_natural_left]
    rfl
  rw [h]
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  have hu : SSet.yonedaEquiv scalarZeroToUnit.hom = PUnit.unit := PUnit.ext _ _
  rw [hu]
  exact (SSet.unitHomEquiv (innerHom A Z)).apply_symm_apply _

private theorem zeroHomEquiv_vertex (A Z : SimplicialPresheaf.{u} D) (g : A ⟶ Z) :
    zeroHomEquiv A Z (innerHomHomEquiv A Z g) = g := by
  change (scalarZeroUnit A).inv ≫
      (scalarTensorHomEquiv A (Δ[0] : SSet.{u}) Z).symm
        (SSet.yonedaEquiv.symm (innerHomHomEquiv A Z g)) = g
  rw [← scalarZero_transpose_vertex, Equiv.symm_apply_apply,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

private theorem zeroHomEquiv_source {A B : SimplicialPresheaf.{u} D} (f : A ⟶ B)
    (Z : SimplicialPresheaf.{u} D) (x : (innerHom B Z) _⦋0⦌) :
    zeroHomEquiv A Z ((innerHomPre f Z).app (op ⦋0⦌) x) = f ≫ zeroHomEquiv B Z x := by
  obtain ⟨g, rfl⟩ := (innerHomHomEquiv B Z).surjective x
  rw [innerHomHomEquiv_precomp, zeroHomEquiv_vertex, zeroHomEquiv_vertex]

private theorem zeroHomEquiv_target (A : SimplicialPresheaf.{u} D)
    {Z Z' : SimplicialPresheaf.{u} D} (g : Z ⟶ Z') (x : (innerHom A Z) _⦋0⦌) :
    zeroHomEquiv A Z' ((innerHomPost A g).app (op ⦋0⦌) x) = zeroHomEquiv A Z x ≫ g := by
  obtain ⟨f, rfl⟩ := (innerHomHomEquiv A Z).surjective x
  rw [innerHomHomEquiv_postcomp, zeroHomEquiv_vertex, zeroHomEquiv_vertex]

/-- Compatibility name for `SimplicialPresheaf.innerHomHomEquiv_precomp`. -/
theorem rawMappingVertex_precomp {A B : SimplicialPresheaf.{u} D} (f : A ⟶ B)
    (Z : SimplicialPresheaf.{u} D) (g : B ⟶ Z) :
    (innerHomPre f Z).app (op ⦋0⦌) (innerHomHomEquiv B Z g) =
      innerHomHomEquiv A Z (f ≫ g) := innerHomHomEquiv_precomp f Z g

/-- Compatibility name for `SimplicialPresheaf.innerHomHomEquiv_postcomp`. -/
theorem rawMappingVertex_postcomp (A : SimplicialPresheaf.{u} D)
    {Z Z' : SimplicialPresheaf.{u} D} (g : Z ⟶ Z') (f : A ⟶ Z) :
    (innerHomPost A g).app (op ⦋0⦌) (innerHomHomEquiv A Z f) =
      innerHomHomEquiv A Z' (f ≫ g) := innerHomHomEquiv_postcomp A g f

private theorem scalarZero_face_zero (A : SimplicialPresheaf.{u} D) :
    (scalarZeroUnit A).inv ≫ (scalarTensor.obj A).map
        (SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 2))) =
      (originalScalarCylinder A).i₀ := by
  apply (cancel_epi (scalarZeroUnit A).hom).mp
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp, scalarZeroUnit_hom]
  ext d n x
  apply Prod.ext
  · rfl
  · change ((SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 2))).app n x.2) =
      ((SSet.ι₀ (X := A.obj d)).app n x.1).2
    apply SSet.stdSimplex.objEquiv.injective
    ext j
    change ↑((SimplexCategory.δ (1 : Fin 2)).toOrderHom
      ((SSet.stdSimplex.objEquiv x.2).toOrderHom j)) = (0 : ℕ)
    rw [Fin.eq_zero ((SSet.stdSimplex.objEquiv x.2).toOrderHom j)]
    rfl

private theorem scalarZero_face_one (A : SimplicialPresheaf.{u} D) :
    (scalarZeroUnit A).inv ≫ (scalarTensor.obj A).map
        (SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 2))) =
      (originalScalarCylinder A).i₁ := by
  apply (cancel_epi (scalarZeroUnit A).hom).mp
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp, scalarZeroUnit_hom]
  ext d n x
  apply Prod.ext
  · rfl
  · change ((SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 2))).app n x.2) =
      ((SSet.ι₁ (X := A.obj d)).app n x.1).2
    apply SSet.stdSimplex.objEquiv.injective
    ext j
    change ↑((SimplexCategory.δ (0 : Fin 2)).toOrderHom
      ((SSet.stdSimplex.objEquiv x.2).toOrderHom j)) = (1 : ℕ)
    rw [Fin.eq_zero ((SSet.stdSimplex.objEquiv x.2).toOrderHom j)]
    rfl

private def edgeLeftHomotopy (A Z : SimplicialPresheaf.{u} D)
    {x y : (innerHom A Z) _⦋0⦌} (e : (innerHom A Z).Edge x y) :
    (originalScalarCylinder A).LeftHomotopy (zeroHomEquiv A Z x) (zeroHomEquiv A Z y) where
  h := innerHomSimplexEquiv A Z (op ⦋1⦌) e.edge
  h₀ := by
    rw [← scalarZero_face_zero, Category.assoc]
    have h := innerHomSimplexEquiv_operator A Z (SimplexCategory.δ (1 : Fin 2)).op e.edge
    have h' : (scalarTensor.obj A).map (SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 2))) ≫
        innerHomSimplexEquiv A Z (op ⦋1⦌) e.edge =
      innerHomSimplexEquiv A Z (op ⦋0⦌) ((innerHom A Z).δ (1 : Fin 2) e.edge) := by
      simpa only [Quiver.Hom.unop_op, SimplicialObject.δ] using h.symm
    rw [h', e.src_eq]
    rfl
  h₁ := by
    rw [← scalarZero_face_one, Category.assoc]
    have h := innerHomSimplexEquiv_operator A Z (SimplexCategory.δ (0 : Fin 2)).op e.edge
    have h' : (scalarTensor.obj A).map (SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 2))) ≫
        innerHomSimplexEquiv A Z (op ⦋1⦌) e.edge =
      innerHomSimplexEquiv A Z (op ⦋0⦌) ((innerHom A Z).δ (0 : Fin 2) e.edge) := by
      simpa only [Quiver.Hom.unop_op, SimplicialObject.δ] using h.symm
    rw [h', e.tgt_eq]
    rfl

private def leftHomotopyEdge (A Z : SimplicialPresheaf.{u} D) {f g : A ⟶ Z}
    (h : (originalScalarCylinder A).LeftHomotopy f g) :
    (innerHom A Z).Edge ((zeroHomEquiv A Z).symm f) ((zeroHomEquiv A Z).symm g) where
  edge := (innerHomSimplexEquiv A Z (op ⦋1⦌)).symm h.h
  src_eq := by
    apply (zeroHomEquiv A Z).injective
    change (scalarZeroUnit A).inv ≫ innerHomSimplexEquiv A Z (op ⦋0⦌)
      ((innerHom A Z).map (SimplexCategory.δ (1 : Fin 2)).op
        ((innerHomSimplexEquiv A Z (op ⦋1⦌)).symm h.h)) = _
    rw [innerHomSimplexEquiv_operator, Equiv.apply_symm_apply, Quiver.Hom.unop_op,
      ← Category.assoc, scalarZero_face_zero, h.h₀, Equiv.apply_symm_apply]
  tgt_eq := by
    apply (zeroHomEquiv A Z).injective
    change (scalarZeroUnit A).inv ≫ innerHomSimplexEquiv A Z (op ⦋0⦌)
      ((innerHom A Z).map (SimplexCategory.δ (0 : Fin 2)).op
        ((innerHomSimplexEquiv A Z (op ⦋1⦌)).symm h.h)) = _
    rw [innerHomSimplexEquiv_operator, Equiv.apply_symm_apply, Quiver.Hom.unop_op,
      ← Category.assoc, scalarZero_face_one, h.h₁, Equiv.apply_symm_apply]

private def componentToClass (A Z : SimplicialPresheaf.{u} D) :
    SSet.π₀ (innerHom A Z) → LeftHomotopyClass A Z :=
  SSet.π₀.lift (fun x => LeftHomotopyClass.mk (zeroHomEquiv A Z x))
    (fun _ _ e => LeftHomotopyClass.sound (edgeLeftHomotopy A Z e).leftHomotopyRel)

private def classToComponent (A Z : SimplicialPresheaf.{u} D) (hZ : IsFibrant Z) :
    LeftHomotopyClass A Z → SSet.π₀ (innerHom A Z) := by
  let _ : IsCofibrant A := (data D).all_cofibrant A
  let _ : IsFibrant Z := hZ
  exact Quot.lift (fun f => SSet.π₀.mk ((zeroHomEquiv A Z).symm f))
    (fun _ _ h => SSet.π₀.sound
      (leftHomotopyEdge A Z (h.leftHomotopy (originalScalarCylinder A))))

/-- Original end components are exactly left-homotopy classes in the actual injective model. -/
def rawMappingComponentEquiv (A Z : SimplicialPresheaf.{u} D) (hZ : IsFibrant Z) :
    SSet.π₀ (innerHom A Z) ≃ LeftHomotopyClass A Z where
  toFun := componentToClass A Z
  invFun := classToComponent A Z hZ
  left_inv c := by
    obtain ⟨x, rfl⟩ := c.mk_surjective
    change SSet.π₀.mk ((zeroHomEquiv A Z).symm (zeroHomEquiv A Z x)) = SSet.π₀.mk x
    rw [Equiv.symm_apply_apply]
  right_inv c := by
    obtain ⟨f, rfl⟩ := LeftHomotopyClass.mk_surjective c
    change LeftHomotopyClass.mk (zeroHomEquiv A Z ((zeroHomEquiv A Z).symm f)) =
      LeftHomotopyClass.mk f
    rw [Equiv.apply_symm_apply]

/-- The component of every ORIGINAL map is its same native left-homotopy class. -/
theorem rawMappingComponentEquiv_mk (A Z : SimplicialPresheaf.{u} D) (hZ : IsFibrant Z)
    (g : A ⟶ Z) :
    rawMappingComponentEquiv A Z hZ (SSet.π₀.mk (innerHomHomEquiv A Z g)) =
      LeftHomotopyClass.mk g := by
  change LeftHomotopyClass.mk (zeroHomEquiv A Z (innerHomHomEquiv A Z g)) = _
  rw [zeroHomEquiv_vertex]

/-- The native quotient source action on the ORIGINAL category, at any fibrant target. -/
def rawMappingClassPrecomp {A B : SimplicialPresheaf.{u} D} (f : A ⟶ B)
    (Z : SimplicialPresheaf.{u} D) (hZ : IsFibrant Z) :
    LeftHomotopyClass B Z → LeftHomotopyClass A Z := by
  let _ : IsFibrant Z := hZ
  exact Quot.map (fun g => f ≫ g) (fun _ _ h => h.precomp f)

/-- The original quotient source action has its exact representative formula. -/
theorem rawMappingClassPrecomp_mk {A B : SimplicialPresheaf.{u} D} (f : A ⟶ B)
    (Z : SimplicialPresheaf.{u} D) (hZ : IsFibrant Z) (g : B ⟶ Z) :
    rawMappingClassPrecomp f Z hZ (LeftHomotopyClass.mk g) = LeftHomotopyClass.mk (f ≫ g) := rfl

/-- Components preserve every original source arrow, without a cofibration condition. -/
theorem rawMappingComponentEquiv_precomp {A B : SimplicialPresheaf.{u} D} (f : A ⟶ B)
    (Z : SimplicialPresheaf.{u} D) (hZ : IsFibrant Z) (c : SSet.π₀ (innerHom B Z)) :
    rawMappingComponentEquiv A Z hZ (SSet.mapπ₀ (innerHomPre f Z) c) =
      rawMappingClassPrecomp f Z hZ (rawMappingComponentEquiv B Z hZ c) := by
  obtain ⟨x, rfl⟩ := c.mk_surjective
  change LeftHomotopyClass.mk (zeroHomEquiv A Z ((innerHomPre f Z).app (op ⦋0⦌) x)) =
    LeftHomotopyClass.mk (f ≫ zeroHomEquiv B Z x)
  rw [zeroHomEquiv_source]

/-- Components preserve every actual target arrow between original fibrant targets. -/
theorem rawMappingComponentEquiv_postcomp (A : SimplicialPresheaf.{u} D)
    {Z Z' : SimplicialPresheaf.{u} D} (g : Z ⟶ Z')
    (hZ : IsFibrant Z) (hZ' : IsFibrant Z') (c : SSet.π₀ (innerHom A Z)) :
    rawMappingComponentEquiv A Z' hZ' (SSet.mapπ₀ (innerHomPost A g) c) =
      (rawMappingComponentEquiv A Z hZ c).postcomp g := by
  obtain ⟨x, rfl⟩ := c.mk_surjective
  change LeftHomotopyClass.mk (zeroHomEquiv A Z' ((innerHomPost A g).app (op ⦋0⦌) x)) =
    LeftHomotopyClass.mk (zeroHomEquiv A Z x ≫ g)
  rw [zeroHomEquiv_target]

/-- Source identity is identity on the actual original quotient. -/
theorem rawMappingClassPrecomp_id (A Z : SimplicialPresheaf.{u} D) (hZ : IsFibrant Z)
    (c : LeftHomotopyClass A Z) : rawMappingClassPrecomp (𝟙 A) Z hZ c = c := by
  obtain ⟨g, rfl⟩ := LeftHomotopyClass.mk_surjective c
  rw [rawMappingClassPrecomp_mk, Category.id_comp]

/-- Composition of arbitrary original source arrows is the same quotient source action. -/
theorem rawMappingClassPrecomp_comp {A B C : SimplicialPresheaf.{u} D}
    (f : A ⟶ B) (g : B ⟶ C) (Z : SimplicialPresheaf.{u} D) (hZ : IsFibrant Z)
    (c : LeftHomotopyClass C Z) :
    rawMappingClassPrecomp f Z hZ (rawMappingClassPrecomp g Z hZ c) =
      rawMappingClassPrecomp (f ≫ g) Z hZ c := by
  obtain ⟨k, rfl⟩ := LeftHomotopyClass.mk_surjective c
  rw [rawMappingClassPrecomp_mk, rawMappingClassPrecomp_mk,
    rawMappingClassPrecomp_mk, Category.assoc]

/-- The same components represent morphisms in the ORIGINAL canonical model localization. -/
def rawMappingHoEquiv (A Z : SimplicialPresheaf.{u} D) (hZ : IsFibrant Z) :
    SSet.π₀ (innerHom A Z) ≃
      ((toHomotopyCategory (SimplicialPresheaf.{u} D)).obj A ⟶
        (toHomotopyCategory (SimplicialPresheaf.{u} D)).obj Z) := by
  let _ : IsCofibrant A := (data D).all_cofibrant A
  let _ : IsFibrant Z := hZ
  exact (rawMappingComponentEquiv A Z hZ).trans
    (leftHomotopyClassEquivOfIsLocalization (toHomotopyCategory (SimplicialPresheaf.{u} D)))

/-- Every original map retains its exact canonical Ho image. -/
theorem rawMappingHoEquiv_mk (A Z : SimplicialPresheaf.{u} D) (hZ : IsFibrant Z)
    (g : A ⟶ Z) :
    rawMappingHoEquiv A Z hZ (SSet.π₀.mk (innerHomHomEquiv A Z g)) =
      (toHomotopyCategory (SimplicialPresheaf.{u} D)).map g := by
  let _ : IsCofibrant A := (data D).all_cofibrant A
  let _ : IsFibrant Z := hZ
  change leftHomotopyClassEquivOfIsLocalization (toHomotopyCategory (SimplicialPresheaf.{u} D))
      (rawMappingComponentEquiv A Z hZ (SSet.π₀.mk (innerHomHomEquiv A Z g))) = _
  rw [rawMappingComponentEquiv_mk, leftHomotopyClassEquivOfIsLocalization_mk]

/-- Every original source arrow gives the exact precomposition by its ORIGINAL Ho image. -/
theorem rawMappingHoEquiv_precomp {A B : SimplicialPresheaf.{u} D} (f : A ⟶ B)
    (Z : SimplicialPresheaf.{u} D) (hZ : IsFibrant Z) (c : SSet.π₀ (innerHom B Z)) :
    rawMappingHoEquiv A Z hZ (SSet.mapπ₀ (innerHomPre f Z) c) =
      (toHomotopyCategory (SimplicialPresheaf.{u} D)).map f ≫ rawMappingHoEquiv B Z hZ c := by
  obtain ⟨x, rfl⟩ := c.mk_surjective
  obtain ⟨g, rfl⟩ := (innerHomHomEquiv B Z).surjective x
  rw [SSet.mapπ₀_mk, innerHomHomEquiv_precomp, rawMappingHoEquiv_mk,
    rawMappingHoEquiv_mk, Functor.map_comp]

/-- Every original target arrow gives the exact postcomposition by its ORIGINAL Ho image. -/
theorem rawMappingHoEquiv_postcomp (A : SimplicialPresheaf.{u} D)
    {Z Z' : SimplicialPresheaf.{u} D} (g : Z ⟶ Z')
    (hZ : IsFibrant Z) (hZ' : IsFibrant Z') (c : SSet.π₀ (innerHom A Z)) :
    rawMappingHoEquiv A Z' hZ' (SSet.mapπ₀ (innerHomPost A g) c) =
      rawMappingHoEquiv A Z hZ c ≫ (toHomotopyCategory (SimplicialPresheaf.{u} D)).map g := by
  obtain ⟨x, rfl⟩ := c.mk_surjective
  obtain ⟨f, rfl⟩ := (innerHomHomEquiv A Z).surjective x
  rw [SSet.mapπ₀_mk, innerHomHomEquiv_postcomp, rawMappingHoEquiv_mk,
    rawMappingHoEquiv_mk, Functor.map_comp]

/-- The actual identity map represents the identity morphism of ORIGINAL canonical Ho. -/
theorem rawMappingHoEquiv_identity (A : SimplicialPresheaf.{u} D) (hA : IsFibrant A) :
    rawMappingHoEquiv A A hA (SSet.π₀.mk (innerHomHomEquiv A A (𝟙 A))) =
      𝟙 ((toHomotopyCategory (SimplicialPresheaf.{u} D)).obj A) := by
  rw [rawMappingHoEquiv_mk]
  exact (toHomotopyCategory (SimplicialPresheaf.{u} D)).map_id A

/-- Every original composition keeps its canonical Ho composition, without intermediate fibrancy. -/
theorem rawMappingHoEquiv_composition {A B Z : SimplicialPresheaf.{u} D}
    (f : A ⟶ B) (g : B ⟶ Z) (hZ : IsFibrant Z) :
    rawMappingHoEquiv A Z hZ (SSet.π₀.mk (innerHomHomEquiv A Z (f ≫ g))) =
      (toHomotopyCategory (SimplicialPresheaf.{u} D)).map f ≫
        (toHomotopyCategory (SimplicialPresheaf.{u} D)).map g := by
  rw [rawMappingHoEquiv_mk, Functor.map_comp]

/-- Original pre/postcomposition exchange is preserved on every mapping component. -/
theorem rawMappingComponentEquiv_exchange {A B Z Z' : SimplicialPresheaf.{u} D}
    (f : A ⟶ B) (g : Z ⟶ Z') (hZ : IsFibrant Z) (hZ' : IsFibrant Z')
    (c : SSet.π₀ (innerHom B Z)) :
    rawMappingComponentEquiv A Z' hZ'
        (SSet.mapπ₀ (innerHomPre f Z ≫ innerHomPost A g) c) =
      rawMappingClassPrecomp f Z' hZ'
        ((rawMappingComponentEquiv B Z hZ c).postcomp g) := by
  rw [SSet.mapπ₀_comp_apply]
  rw [rawMappingComponentEquiv_postcomp A g hZ hZ' (SSet.mapπ₀ (innerHomPre f Z) c)]
  rw [rawMappingComponentEquiv_precomp f Z hZ c]
  obtain ⟨k, hk⟩ := LeftHomotopyClass.mk_surjective (rawMappingComponentEquiv B Z hZ c)
  rw [← hk]
  rw [LeftHomotopyClass.postcomp_mk, rawMappingClassPrecomp_mk,
    rawMappingClassPrecomp_mk, LeftHomotopyClass.postcomp_mk, Category.assoc]

end SimplicialPresheaf.InjectiveKan
