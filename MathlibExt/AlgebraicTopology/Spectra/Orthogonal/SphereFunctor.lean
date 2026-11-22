/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.OnePointAction
public import MathlibExt.Topology.Category.PointedCGWH.Closed
public import MathlibExt.CategoryTheory.Enriched.Monoidal.Functor
public import MathlibExt.CategoryTheory.Enriched.Monoidal.ExternalTensor
public import MathlibExt.CategoryTheory.Enriched.GradedYoneda

/-!
# The native enriched orthogonal representation-sphere functor

The full freely based native isometry hom objects act on representation spheres.
The action is transposed only after the required braiding. The lax unit and
tensorator use the original one-point representation identifications; no action,
coherence, closed structure or model-category dictionary is supplied.

This is the coefficient functor on the bare orthogonal index. It does not identify
the weighted sphere operator category with the source full index or construct a
spectrum model.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory BraidedCategory
open Matrix TopologicalSpace
open scoped MonoidalClosed MonoidalCategory ZeroObject

attribute [local instance] HasZeroObject.zeroMorphismsOfZeroObject

universe u v

namespace CategoryTheory.Spectra

attribute [local instance] OrthogonalIndex.enrichedCategory

private theorem sphereAction_transpose_identity (n : OrthogonalIndex) :
    (@eId PointedCGWH.{u, v} _ _ OrthogonalIndex
        (OrthogonalIndex.enrichedCategory.{u, v}) n) ≫
      MonoidalClosed.curry
        ((β_ (PointedCGWH.orthogonalSphere.{u, v} n)
          (OrthogonalIndex.hom.{u, v} n n)).hom ≫
          PointedCGWH.orthogonalSphereAction.{u, v} n n) =
      eId PointedCGWH.{u, v} (PointedCGWH.orthogonalSphere.{u, v} n) := by
  let e : 𝟙_ PointedCGWH.{u, v} ⟶ OrthogonalIndex.hom.{u, v} n n :=
    @eId PointedCGWH.{u, v} _ _ OrthogonalIndex
      (OrthogonalIndex.enrichedCategory.{u, v}) n
  change e ≫ MonoidalClosed.curry
      ((β_ (PointedCGWH.orthogonalSphere.{u, v} n)
        (OrthogonalIndex.hom.{u, v} n n)).hom ≫
        PointedCGWH.orthogonalSphereAction.{u, v} n n) = _
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry,
    MonoidalClosed.enrichedCategorySelf_id, MonoidalClosed.id_eq,
    MonoidalClosed.uncurry_curry]
  have h := congrArg
    (fun f => (λ_ (PointedCGWH.orthogonalSphere.{u, v} n)).hom ≫ f)
    (PointedCGWH.orthogonalSphereAction_identity.{u, v} n)
  simp only [Iso.hom_inv_id_assoc, Category.comp_id,
    tensorHom_id] at h
  change e ▷ PointedCGWH.orthogonalSphere.{u, v} n ≫
    PointedCGWH.orthogonalSphereAction.{u, v} n n = _ at h
  rw [braiding_naturality_right_assoc, h]
  simp only [braiding_tensorUnit_right, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

private theorem sphereAction_transpose_composition (m n p : OrthogonalIndex) :
    (@eComp PointedCGWH.{u, v} _ _ OrthogonalIndex
        (OrthogonalIndex.enrichedCategory.{u, v}) m n p) ≫
      MonoidalClosed.curry
        ((β_ (PointedCGWH.orthogonalSphere.{u, v} m)
          (OrthogonalIndex.hom.{u, v} m p)).hom ≫
          PointedCGWH.orthogonalSphereAction.{u, v} m p) =
      (MonoidalClosed.curry
          ((β_ (PointedCGWH.orthogonalSphere.{u, v} m)
            (OrthogonalIndex.hom.{u, v} m n)).hom ≫
            PointedCGWH.orthogonalSphereAction.{u, v} m n) ⊗ₘ
        MonoidalClosed.curry
          ((β_ (PointedCGWH.orthogonalSphere.{u, v} n)
            (OrthogonalIndex.hom.{u, v} n p)).hom ≫
            PointedCGWH.orthogonalSphereAction.{u, v} n p)) ≫
      eComp PointedCGWH.{u, v}
        (PointedCGWH.orthogonalSphere.{u, v} m)
        (PointedCGWH.orthogonalSphere.{u, v} n)
        (PointedCGWH.orthogonalSphere.{u, v} p) := by
  let c : OrthogonalIndex.hom.{u, v} m n ⊗
      OrthogonalIndex.hom.{u, v} n p ⟶ OrthogonalIndex.hom.{u, v} m p :=
    @eComp PointedCGWH.{u, v} _ _ OrthogonalIndex
      (OrthogonalIndex.enrichedCategory.{u, v}) m n p
  change c ≫ MonoidalClosed.curry
      ((β_ (PointedCGWH.orthogonalSphere.{u, v} m)
        (OrthogonalIndex.hom.{u, v} m p)).hom ≫
        PointedCGWH.orthogonalSphereAction.{u, v} m p) = _
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry,
    MonoidalClosed.uncurry_eComp, MonoidalClosed.uncurry_curry,
    MonoidalClosed.uncurry_curry]
  rw [braiding_naturality_right_assoc]
  have h := PointedCGWH.orthogonalSphereAction_composition.{u, v} m n p
  simp only [tensorHom_id, id_tensorHom] at h
  change c ▷ PointedCGWH.orthogonalSphere.{u, v} m ≫
    PointedCGWH.orthogonalSphereAction.{u, v} m p = _ at h
  rw [h, braiding_tensor_right_hom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc,
    ← whiskerLeft_comp_assoc, SymmetricCategory.symmetry,
    whiskerLeft_id, Category.id_comp, comp_whiskerRight]

/-- The native representation-sphere functor, on the entire based isometry
hom object, with no externally supplied action or functor laws. -/
def orthogonalSphereFunctor :
    letI : EnrichedCategory PointedCGWH.{u, v} OrthogonalIndex :=
      OrthogonalIndex.enrichedCategory.{u, v}
    EnrichedFunctor PointedCGWH.{u, v} OrthogonalIndex PointedCGWH.{u, v} := by
  letI : EnrichedCategory PointedCGWH.{u, v} OrthogonalIndex :=
    OrthogonalIndex.enrichedCategory.{u, v}
  exact
    { obj := PointedCGWH.orthogonalSphere.{u, v}
      map := fun m n => MonoidalClosed.curry
        ((β_ (PointedCGWH.orthogonalSphere.{u, v} m)
          (OrthogonalIndex.hom.{u, v} m n)).hom ≫
          PointedCGWH.orthogonalSphereAction.{u, v} m n)
      map_id := (by exact sphereAction_transpose_identity)
      map_comp := (by exact sphereAction_transpose_composition) }

/-- Objects are precisely the original one-point representation spheres. -/
@[simp]
theorem orthogonalSphereFunctor_obj (n : OrthogonalIndex) :
    orthogonalSphereFunctor.{u, v}.obj n =
      PointedCGWH.orthogonalSphere.{u, v} n := rfl

/-- The full uncurried functor action is the original joint action, preceded
by the required sphere/isometry braiding. -/
theorem orthogonalSphereFunctor_uncurry (m n : OrthogonalIndex) :
    MonoidalClosed.uncurry (orthogonalSphereFunctor.{u, v}.map m n) =
      (β_ (PointedCGWH.orthogonalSphere.{u, v} m)
        (OrthogonalIndex.hom.{u, v} m n)).hom ≫
        PointedCGWH.orthogonalSphereAction.{u, v} m n := by
  exact MonoidalClosed.uncurry_curry _

/-- The actual ordinary image of a native generalized point. The native
ordinary/enriched hom equivalence is the identity on precisely these points,
including the disjoint basepoint at unequal dimensions. -/
def orthogonalSphereMap {m n : OrthogonalIndex}
    (f : 𝟙_ PointedCGWH.{u, v} ⟶ OrthogonalIndex.hom.{u, v} m n) :
    PointedCGWH.orthogonalSphere.{u, v} m ⟶
      PointedCGWH.orthogonalSphere.{u, v} n :=
  (eHomEquiv PointedCGWH.{u, v}).symm
    (f ≫ orthogonalSphereFunctor.{u, v}.map m n)

/-- The ordinary image is exactly the native unit-point action, rather than
a separately defined matrix action. -/
theorem orthogonalSphereMap_eq {m n : OrthogonalIndex}
    (f : 𝟙_ PointedCGWH.{u, v} ⟶ OrthogonalIndex.hom.{u, v} m n) :
    orthogonalSphereMap.{u, v} f =
      (λ_ (PointedCGWH.orthogonalSphere.{u, v} m)).inv ≫
        (f ▷ PointedCGWH.orthogonalSphere.{u, v} m) ≫
        PointedCGWH.orthogonalSphereAction.{u, v} m n := by
  rw [orthogonalSphereMap, MonoidalClosed.enrichedOrdinaryCategorySelf_homEquiv_symm]
  dsimp only [MonoidalClosed.uncurry']
  change (ρ_ (PointedCGWH.orthogonalSphere.{u, v} m)).inv ≫
      MonoidalClosed.uncurry
        (f ≫ MonoidalClosed.curry
          ((β_ (PointedCGWH.orthogonalSphere.{u, v} m)
            (OrthogonalIndex.hom.{u, v} m n)).hom ≫
            PointedCGWH.orthogonalSphereAction.{u, v} m n)) = _
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry,
    braiding_naturality_right_assoc, braiding_tensorUnit_right]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- Four independent objects, not the repeated-object tensor-swap
specialization: interchange and the two individual braidings are compatible
with the braiding of the two full tensor blocks. -/
private theorem sphere_tensorμ_braiding
    {C : Type*} [Category* C] [MonoidalCategory C] [SymmetricCategory C]
    (X Y A B : C) :
    tensorμ X Y A B ≫ ((β_ X A).hom ⊗ₘ (β_ Y B).hom) =
      (β_ (X ⊗ Y) (A ⊗ B)).hom ≫ tensorμ A B X Y := by
  simp only [tensorμ, SymmetricCategory.braiding_swap_eq_inv_braiding, tensorHom_def,
    whiskerRight_tensor, tensor_whiskerLeft, Category.assoc,
    pentagon_hom_inv_inv_inv_inv_assoc, braiding_tensor_right_inv,
    braiding_tensor_left_inv, whiskerLeft_comp, comp_whiskerRight, whisker_assoc,
    pentagon_inv_inv_hom_hom_inv, pentagon_inv_assoc, Iso.inv_hom_id_assoc,
    whiskerLeft_hom_inv_assoc, Iso.cancel_iso_hom_left]
  have hCancel : (β_ B X).inv ≫ (β_ X B).inv = 𝟙 (X ⊗ B) := by
    rw [← SymmetricCategory.braiding_swap_eq_inv_braiding,
      ← SymmetricCategory.braiding_swap_eq_inv_braiding,
      SymmetricCategory.symmetry]
  rw [← whiskerLeft_comp_assoc A ((β_ B X).inv ▷ Y) ((β_ X B).inv ▷ Y),
    ← comp_whiskerRight, hCancel]
  simp only [id_whiskerRight, whiskerLeft_id, Category.id_comp]
  calc
    _ = ((X ◁ (α_ Y A B).inv) ≫ (X ◁ (β_ A Y).inv ▷ B)) ⊗≫
        ((β_ A X).inv ⊗ₘ (β_ B Y).inv) := by
      rw [tensorHom_def]
      monoidal
    _ = _ := by
      rw [tensorHom_def']
      monoidal


private theorem sphere_unit_input
    (H S : PointedCGWH.{u, v})
    (f : 𝟙_ PointedCGWH.{u, v} ⟶ H) (z : S.right) :
    ((λ_ S).inv ≫ (f ▷ S)).right z =
      (CategoryTheory.Pointed.smashPresentation
        CGWH.point CGWH.point_isTerminal H S).2.1.inl
        (Classical.choose
          ((CGWH.prodComparisonToTop_bijective H.right S.right).2
            (f.right
              ((coprod.inr : CGWH.point.{u, v} ⟶
                CGWH.point.{u, v} ⨿ CGWH.point.{u, v}) PUnit.unit), z))) := by
  let _ : BraidedCategory CGWH.{u, v} := BraidedCategory.ofCartesianMonoidalCategory
  let _ : SymmetricCategory CGWH.{u, v} := inferInstance
  let P := CGWH.point.{u, v}
  let hP := CGWH.point_isTerminal.{u, v}
  let U : PointedCGWH.{u, v} := 𝟙_ PointedCGWH.{u, v}
  let q (A B : PointedCGWH.{u, v}) :
      A.right ⊗ B.right ⟶ (A ⊗ B).right :=
    (CategoryTheory.Pointed.smashPresentation P hP A B).2.1.inl
  let p := hP.uniqueUpToIso CartesianMonoidalCategory.isTerminalTensorUnit
  let free : P ⟶ U.right := coprod.inr
  let k : S.right ⟶ H.right ⊗ S.right :=
    (λ_ S.right).inv ≫ (p.inv ▷ S.right) ≫
      (free ▷ S.right) ≫ (f.right ▷ S.right)
  let ell : S.right ⟶ H.right ⊗ S.right :=
    CartesianMonoidalCategory.lift
      (hP.from S.right ≫ free ≫ f.right) (𝟙 S.right)
  have hUnitor : (λ_ S).inv.right =
      (λ_ S.right).inv ≫ (p.inv ▷ S.right) ≫
        (free ▷ S.right) ≫ q U S :=
    CategoryTheory.Pointed.smashLeftUnitor_inv_free P hP S
  have hQuotient : q U S ≫ (f ▷ S).right =
      (f.right ▷ S.right) ≫ q H S := by
    have h := CategoryTheory.Pointed.smashQuotient_naturality P hP f (𝟙 S)
    simp only [tensorHom_id, Under.id_right] at h
    exact h
  have hInput : ((λ_ S).inv ≫ (f ▷ S)).right = k ≫ q H S := by
    rw [Under.comp_right, hUnitor]
    dsimp only [k]
    simp only [Category.assoc]
    rw [hQuotient]
  have hCartesian : k = ell := by
    have hPair : k = (λ_ S.right).inv ≫
        ((p.inv ≫ free ≫ f.right) ⊗ₘ 𝟙 S.right) := by
      simp only [k, tensorHom_id, comp_whiskerRight]
    apply CartesianMonoidalCategory.hom_ext
    · dsimp only [ell]
      rw [hPair, Category.assoc, CartesianMonoidalCategory.tensorHom_fst,
        CartesianMonoidalCategory.lift_fst]
      have hPoint :
          (λ_ S.right).inv ≫
            CartesianMonoidalCategory.fst (𝟙_ CGWH.{u, v}) S.right ≫ p.inv =
          hP.from S.right := hP.hom_ext _ _
      simpa only [Category.assoc] using
        congrArg (fun g => g ≫ free ≫ f.right) hPoint
    · dsimp only [ell]
      rw [hPair, Category.assoc, CartesianMonoidalCategory.tensorHom_snd,
        Category.comp_id, CartesianMonoidalCategory.leftUnitor_inv_snd,
        CartesianMonoidalCategory.lift_snd]
  rw [hInput, ConcreteCategory.comp_apply]
  let chosen : (H.right ⊗ S.right : CGWH.{u, v}) :=
    Classical.choose ((CGWH.prodComparisonToTop_bijective H.right S.right).2
      (f.right (free PUnit.unit), z))
  change q H S (k z) = q H S chosen
  apply congrArg (fun w => q H S w)
  have hChosen : CGWH.tensorEquivProd H.right S.right chosen =
      (f.right (free PUnit.unit), z) :=
    (CGWH.tensorEquivProd_eq_prodComparisonToTop H.right S.right chosen).trans
      (Classical.choose_spec
        ((CGWH.prodComparisonToTop_bijective H.right S.right).2
          (f.right (free PUnit.unit), z)))
  apply (CGWH.tensorEquivProd H.right S.right).injective
  rw [hChosen, hCartesian]
  apply Prod.ext
  · rw [CGWH.tensorEquivProd_apply_fst]
    have h := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.lift_fst
        (hP.from S.right ≫ free ≫ f.right) (𝟙 S.right)) z
    simp only [ConcreteCategory.comp_apply] at h
    rw [h]
    have hz : hP.from S.right z = (PUnit.unit : P) := by
      change @Eq PUnit _ _
      exact Subsingleton.elim _ _
    simp only [hz]
  · rw [CGWH.tensorEquivProd_apply_snd]
    simpa only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using
      ConcreteCategory.congr_hom
        (CartesianMonoidalCategory.lift_snd
          (hP.from S.right ≫ free ≫ f.right) (𝟙 S.right)) z

private theorem sphere_pointed_zero_right (A B : PointedCGWH.{u, v}) :
    (0 : A ⟶ B).right = CGWH.point_isTerminal.from A.right ≫ B.hom := by
  let Z : PointedCGWH.{u, v} := Under.mk (𝟙 CGWH.point.{u, v})
  let p : A ⟶ Z := Under.homMk (CGWH.point_isTerminal.from A.right)
    (CGWH.point_isTerminal.hom_ext _ _)
  let q : Z ⟶ B := Under.homMk B.hom (by simp [Z])
  have hZ : IsZero Z := (show IsInitial Z from Under.mkIdInitial).isZero
  have h : p ≫ q = 0 := by rw [hZ.eq_zero_of_src q, comp_zero]
  exact (congrArg Under.Hom.right h).symm

/-- Every native ordinary image fixes the sphere's point at infinity. -/
theorem orthogonalSphereMap_infty {m n : OrthogonalIndex}
    (f : 𝟙_ PointedCGWH.{u, v} ⟶ OrthogonalIndex.hom.{u, v} m n) :
    (orthogonalSphereMap.{u, v} f).right OnePoint.infty = OnePoint.infty := by
  exact ConcreteCategory.congr_hom (Under.w (orthogonalSphereMap.{u, v} f)) PUnit.unit

/-- A genuine matrix point acts by its original finite matrix-vector formula. -/
theorem orthogonalSphereMap_matrixPoint_coe {m n : OrthogonalIndex}
    (A : OrthogonalMatrixHom m n) (x : EuclideanSpace ℝ (Fin m)) :
    (orthogonalSphereMap.{u, v} (OrthogonalIndex.matrixPoint.{u, v} A)).right
        ((ULift.up x : ULift.{v, 0} (EuclideanSpace ℝ (Fin m))) :
          OnePoint (ULift.{v, 0} (EuclideanSpace ℝ (Fin m)))) =
      ((ULift.up ((EuclideanSpace.equiv (Fin n) ℝ).symm (A.1 *ᵥ x.ofLp)) :
        ULift.{v, 0} (EuclideanSpace ℝ (Fin n))) :
          OnePoint (ULift.{v, 0} (EuclideanSpace ℝ (Fin n)))) := by
  rw [orthogonalSphereMap_eq]
  let z : (PointedCGWH.orthogonalSphere.{u, v} m).right :=
    ((ULift.up x : ULift.{v, 0} (EuclideanSpace ℝ (Fin m))) :
      OnePoint (ULift.{v, 0} (EuclideanSpace ℝ (Fin m))))
  change (PointedCGWH.orthogonalSphereAction.{u, v} m n).right
    (((λ_ (PointedCGWH.orthogonalSphere.{u, v} m)).inv ≫
      (OrthogonalIndex.matrixPoint.{u, v} A ▷
        PointedCGWH.orthogonalSphere.{u, v} m)).right z) = _
  have hInput := sphere_unit_input
    (OrthogonalIndex.hom.{u, v} m n)
    (PointedCGWH.orthogonalSphere.{u, v} m)
    (OrthogonalIndex.matrixPoint.{u, v} A) z
  exact (congrArg (PointedCGWH.orthogonalSphereAction.{u, v} m n).right hInput).trans
    (PointedCGWH.orthogonalSphereAction_coe.{u, v} A x)

/-- The added native zero point acts by the actual zero based map, including
at unequal dimensions. -/
theorem orthogonalSphereMap_zero (m n : OrthogonalIndex) :
    orthogonalSphereMap.{u, v}
      (0 : 𝟙_ PointedCGWH.{u, v} ⟶ OrthogonalIndex.hom.{u, v} m n) =
      (0 : PointedCGWH.orthogonalSphere.{u, v} m ⟶
        PointedCGWH.orthogonalSphere.{u, v} n) := by
  rw [orthogonalSphereMap_eq]
  apply Under.UnderMorphism.ext
  apply ConcreteCategory.hom_ext
  intro z
  let H := OrthogonalIndex.hom.{u, v} m n
  let S := PointedCGWH.orthogonalSphere.{u, v} m
  let T := PointedCGWH.orthogonalSphere.{u, v} n
  let f : 𝟙_ PointedCGWH.{u, v} ⟶ H := 0
  let t : (𝟙_ PointedCGWH.{u, v}).right :=
    (coprod.inr : CGWH.point.{u, v} ⟶
      CGWH.point.{u, v} ⨿ CGWH.point.{u, v}) PUnit.unit
  let q : H.right ⊗ S.right ⟶ (H ⊗ S).right :=
    (CategoryTheory.Pointed.smashPresentation
      CGWH.point CGWH.point_isTerminal H S).2.1.inl
  change (PointedCGWH.orthogonalSphereAction.{u, v} m n).right
    (((λ_ S).inv ≫ (f ▷ S)).right z) = (0 : S ⟶ T).right z
  have hPoint :
      CGWH.point_isTerminal.from (𝟙_ PointedCGWH.{u, v}).right
        t =
      (PUnit.unit : CGWH.point.{u, v}) := by
    change @Eq PUnit _ _
    exact Subsingleton.elim _ _
  have hZeroPoint : f.right t = H.hom PUnit.unit := by
    rw [sphere_pointed_zero_right, ConcreteCategory.comp_apply, hPoint]
  let c : (H.right ⊗ S.right : CGWH.{u, v}) :=
    Classical.choose ((CGWH.prodComparisonToTop_bijective H.right S.right).2
      (f.right t, z))
  let cBase : (H.right ⊗ S.right : CGWH.{u, v}) :=
    Classical.choose ((CGWH.prodComparisonToTop_bijective H.right S.right).2
      (H.hom PUnit.unit, z))
  have hc : c = cBase := by
    have hc₁ : CGWH.prodComparisonToTop H.right S.right c = (f.right t, z) :=
      Classical.choose_spec
        ((CGWH.prodComparisonToTop_bijective H.right S.right).2 (f.right t, z))
    have hc₂ : CGWH.prodComparisonToTop H.right S.right cBase =
        (H.hom PUnit.unit, z) :=
      Classical.choose_spec
        ((CGWH.prodComparisonToTop_bijective H.right S.right).2
          (H.hom PUnit.unit, z))
    have hPair : (f.right t, z) = (H.hom PUnit.unit, z) := Prod.ext hZeroPoint rfl
    exact (CGWH.prodComparisonToTop_bijective H.right S.right).1
      (hc₁.trans (hPair.trans hc₂.symm))
  have hInput : ((λ_ S).inv ≫ (f ▷ S)).right z = q c :=
    sphere_unit_input H S f z
  have hInputBase := hInput.trans (congrArg (fun w => q w) hc)
  have hAction : (PointedCGWH.orthogonalSphereAction.{u, v} m n).right
      (q cBase) = OnePoint.infty :=
    PointedCGWH.orthogonalSphereAction_parameterBasepoint.{u, v} m n z
  have hTarget : (0 : S ⟶ T).right z = OnePoint.infty := by
    rw [sphere_pointed_zero_right, ConcreteCategory.comp_apply]
    rfl
  exact ((congrArg (PointedCGWH.orthogonalSphereAction.{u, v} m n).right
    hInputBase).trans hAction).trans hTarget.symm

/-- The ordinary image of a raw isometry matrix is the actual compactified
lift of the existing Euclidean isometric equivalence. This is equality of
native based maps, not only equality of finite point sets. -/
theorem orthogonalSphereMap_matrixPoint {m n : OrthogonalIndex}
    (A : OrthogonalMatrixHom m n) :
    orthogonalSphereMap.{u, v} (OrthogonalIndex.matrixPoint.{u, v} A) =
      (PointedCGWH.onePointHomeomorphOfHomeomorph.{u, v}
        ((Homeomorph.ulift (X := EuclideanSpace ℝ (Fin m))).trans
          (((OrthogonalMatrixHom.equivLinearIsometryEquiv m n A).toHomeomorph).trans
            (Homeomorph.ulift (X := EuclideanSpace ℝ (Fin n))).symm))).hom := by
  apply Under.UnderMorphism.ext
  apply ConcreteCategory.hom_ext
  intro z
  induction z using OnePoint.rec with
  | infty =>
      rw [orthogonalSphereMap_infty]
      rfl
  | coe x =>
      rcases x with ⟨x⟩
      rw [orthogonalSphereMap_matrixPoint_coe]
      change ((ULift.up ((EuclideanSpace.equiv (Fin n) ℝ).symm
          (A.1 *ᵥ x.ofLp)) : ULift.{v, 0} (EuclideanSpace ℝ (Fin n))) :
            OnePoint (ULift.{v, 0} (EuclideanSpace ℝ (Fin n)))) =
        ((ULift.up (OrthogonalMatrixHom.equivLinearIsometryEquiv m n A x) :
          ULift.{v, 0} (EuclideanSpace ℝ (Fin n))) :
            OnePoint (ULift.{v, 0} (EuclideanSpace ℝ (Fin n))))
      apply congrArg (fun y : EuclideanSpace ℝ (Fin n) =>
        ((ULift.up y : ULift.{v, 0} (EuclideanSpace ℝ (Fin n))) :
          OnePoint (ULift.{v, 0} (EuclideanSpace ℝ (Fin n)))))
      change _ = Matrix.toLpLin 2 2 A.1 x
      rw [Matrix.toLpLin_apply]
      rfl

/-- The original one-point isomorphism induced by an actual finite-coordinate
equivalence. No coherence or isometry action is supplied as additional data. -/
def orthogonalSphereCoordinateIso {m n : OrthogonalIndex} (e : Fin m ≃ Fin n) :
    PointedCGWH.orthogonalSphere.{u, v} m ≅
      PointedCGWH.orthogonalSphere.{u, v} n :=
  PointedCGWH.onePointHomeomorphOfHomeomorph.{u, v}
    ((Homeomorph.ulift (X := EuclideanSpace ℝ (Fin m))).trans
      ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e).toHomeomorph.trans
        (Homeomorph.ulift (X := EuclideanSpace ℝ (Fin n))).symm))

private def sphere_coordinate_matrix {m n : OrthogonalIndex} (e : Fin m ≃ Fin n) :
    OrthogonalMatrixHom m n :=
  (OrthogonalMatrixHom.equivLinearIsometryEquiv m n).symm
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e)

private theorem sphere_coordinate_matrix_apply {m n : OrthogonalIndex}
    (e : Fin m ≃ Fin n) (i : Fin n) (j : Fin m) :
    (sphere_coordinate_matrix e).1 i j = if i = e j then 1 else 0 := by
  change LinearMap.toMatrix
      (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e).toLinearEquiv.toLinearMap i j = _
  rw [LinearMap.toMatrix_apply]
  change (EuclideanSpace.basisFun (Fin n) ℝ).repr
      ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e)
        ((EuclideanSpace.basisFun (Fin m) ℝ) j)) i = _
  rw [EuclideanSpace.basisFun_apply, EuclideanSpace.piLpCongrLeft_single,
    EuclideanSpace.basisFun_repr]
  simp only [PiLp.single_apply]

private theorem sphere_coordinate_matrix_image {m n : OrthogonalIndex}
    (e : Fin m ≃ Fin n) :
    orthogonalSphereMap.{u, v}
        (OrthogonalIndex.matrixPoint.{u, v} (sphere_coordinate_matrix e)) =
      (orthogonalSphereCoordinateIso.{u, v} e).hom := by
  rw [orthogonalSphereMap_matrixPoint]
  dsimp only [sphere_coordinate_matrix]
  rw [Equiv.apply_symm_apply]
  rfl


/-- The image formula uses the exact native ordinary/enriched dictionary;
arbitrary native arrows, including zeros, are precisely these unit points. -/
theorem orthogonalSphereMap_nativeImage (m n : OrthogonalIndex) :
    letI : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
    letI : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
      OrthogonalIndex.enrichedOrdinaryCategory.{u, v}
    ∀ f : m ⟶ n,
      (eHomEquiv PointedCGWH.{u, v}).symm
        (eHomEquiv PointedCGWH.{u, v} f ≫
          orthogonalSphereFunctor.{u, v}.map m n) =
      orthogonalSphereMap.{u, v} f := by
  let _ : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
  let _ : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
    OrthogonalIndex.enrichedOrdinaryCategory.{u, v}
  intro f
  rfl

private theorem sphere_index_associator_point (m n p : OrthogonalIndex) :
    letI : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
    letI : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
    (α_ m n p).hom =
      OrthogonalIndex.matrixPoint.{u, v}
        (sphere_coordinate_matrix (finCongr (Nat.add_assoc m n p))) := by
  let _ : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
  let _ : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
  change OrthogonalIndex.matrixPoint.{u, v} _ =
    OrthogonalIndex.matrixPoint.{u, v}
      (sphere_coordinate_matrix (finCongr (Nat.add_assoc m n p)))
  apply congrArg OrthogonalIndex.matrixPoint.{u, v}
  apply OrthogonalMatrixHom.ext
  ext i j
  rw [sphere_coordinate_matrix_apply]
  change (if (finCongr (Nat.add_assoc m n p)).symm i = j then (1 : ℝ) else 0) =
    if i = finCongr (Nat.add_assoc m n p) j then 1 else 0
  simp only [Equiv.symm_apply_eq]

private theorem sphere_index_left_unitor_point (n : OrthogonalIndex) :
    letI : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
    letI : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
    (λ_ n).hom =
      OrthogonalIndex.matrixPoint.{u, v}
        (sphere_coordinate_matrix (finCongr (Nat.zero_add n))) := by
  let _ : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
  let _ : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
  change OrthogonalIndex.matrixPoint.{u, v} _ =
    OrthogonalIndex.matrixPoint.{u, v}
      (sphere_coordinate_matrix (finCongr (Nat.zero_add n)))
  apply congrArg OrthogonalIndex.matrixPoint.{u, v}
  apply OrthogonalMatrixHom.ext
  ext i j
  rw [sphere_coordinate_matrix_apply]
  change (if (finCongr (Nat.zero_add n)).symm i = j then (1 : ℝ) else 0) =
    if i = finCongr (Nat.zero_add n) j then 1 else 0
  simp only [Equiv.symm_apply_eq]

private theorem sphere_index_right_unitor_point (n : OrthogonalIndex) :
    letI : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
    letI : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
    (ρ_ n).hom =
      OrthogonalIndex.matrixPoint.{u, v}
        (sphere_coordinate_matrix (finCongr (Nat.add_zero n))) := by
  let _ : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
  let _ : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
  change OrthogonalIndex.matrixPoint.{u, v} _ =
    OrthogonalIndex.matrixPoint.{u, v}
      (sphere_coordinate_matrix (finCongr (Nat.add_zero n)))
  apply congrArg OrthogonalIndex.matrixPoint.{u, v}
  apply OrthogonalMatrixHom.ext
  ext i j
  rw [sphere_coordinate_matrix_apply]
  change (if (finCongr (Nat.add_zero n)).symm i = j then (1 : ℝ) else 0) =
    if i = finCongr (Nat.add_zero n) j then 1 else 0
  simp only [Equiv.symm_apply_eq]

private theorem sphere_index_braiding_point (m n : OrthogonalIndex) :
    letI : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
    letI : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
    letI : SymmetricCategory OrthogonalIndex := OrthogonalIndex.symmetricCategory.{u, v}
    (β_ m n).hom =
      OrthogonalIndex.matrixPoint.{u, v}
        (sphere_coordinate_matrix (finAddFlip : Fin (m + n) ≃ Fin (n + m))) := by
  let _ : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
  let _ : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
  let _ : SymmetricCategory OrthogonalIndex := OrthogonalIndex.symmetricCategory.{u, v}
  change OrthogonalIndex.matrixPoint.{u, v} (OrthogonalIndex.blockSwap m n) = _
  apply congrArg OrthogonalIndex.matrixPoint.{u, v}
  apply OrthogonalMatrixHom.ext
  ext i j
  rw [OrthogonalIndex.blockSwap_matrix, sphere_coordinate_matrix_apply]

/-- The actual index associator maps to the original compactified coordinate
reassociation, not to a caller-supplied coherence map. -/
theorem orthogonalSphereMap_associator (m n p : OrthogonalIndex) :
    letI : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
    letI : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
    orthogonalSphereMap.{u, v} (α_ m n p).hom =
      (orthogonalSphereCoordinateIso.{u, v} (finCongr (Nat.add_assoc m n p))).hom := by
  let _ : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
  let _ : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
  rw [sphere_index_associator_point]
  exact sphere_coordinate_matrix_image _

/-- The actual left index unitor maps to deletion of the left zero block. -/
theorem orthogonalSphereMap_leftUnitor (n : OrthogonalIndex) :
    letI : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
    letI : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
    orthogonalSphereMap.{u, v} (λ_ n).hom =
      (orthogonalSphereCoordinateIso.{u, v} (finCongr (Nat.zero_add n))).hom := by
  let _ : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
  let _ : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
  rw [sphere_index_left_unitor_point]
  exact sphere_coordinate_matrix_image _

/-- The actual right index unitor maps to deletion of the right zero block. -/
theorem orthogonalSphereMap_rightUnitor (n : OrthogonalIndex) :
    letI : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
    letI : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
    orthogonalSphereMap.{u, v} (ρ_ n).hom =
      (orthogonalSphereCoordinateIso.{u, v} (finCongr (Nat.add_zero n))).hom := by
  let _ : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
  let _ : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
  rw [sphere_index_right_unitor_point]
  exact sphere_coordinate_matrix_image _

/-- The actual block-swap braiding maps to the original compactified ordered
coordinate swap, with both independent degree blocks retained. -/
theorem orthogonalSphereMap_braiding (m n : OrthogonalIndex) :
    letI : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
    letI : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
    letI : SymmetricCategory OrthogonalIndex := OrthogonalIndex.symmetricCategory.{u, v}
    orthogonalSphereMap.{u, v} (β_ m n).hom =
      (orthogonalSphereCoordinateIso.{u, v}
        (finAddFlip : Fin (m + n) ≃ Fin (n + m))).hom := by
  let _ : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
  let _ : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
  let _ : SymmetricCategory OrthogonalIndex := OrthogonalIndex.symmetricCategory.{u, v}
  rw [sphere_index_braiding_point]
  exact sphere_coordinate_matrix_image _


private theorem sphere_tensor_naturality (m n p q : OrthogonalIndex) :
    (orthogonalSphereFunctor.{u, v}.map m n ⊗ₘ
        orthogonalSphereFunctor.{u, v}.map p q) ≫
      (MonoidalClosed.enrichedMonoidalCategoryDataSelf PointedCGWH.{u, v}).tensorMap
        (PointedCGWH.orthogonalSphere.{u, v} m)
        (PointedCGWH.orthogonalSphere.{u, v} n)
        (PointedCGWH.orthogonalSphere.{u, v} p)
        (PointedCGWH.orthogonalSphere.{u, v} q) ≫
      eHomWhiskerLeft PointedCGWH.{u, v}
        (PointedCGWH.orthogonalSphere.{u, v} m ⊗
          PointedCGWH.orthogonalSphere.{u, v} p)
        (PointedCGWH.orthogonalSphereTensorIso.{u, v} n q).inv =
    OrthogonalIndex.tensorMap.{u, v} m n p q ≫
      orthogonalSphereFunctor.{u, v}.map (m + p) (n + q) ≫
      eHomWhiskerRight PointedCGWH.{u, v}
        (PointedCGWH.orthogonalSphereTensorIso.{u, v} m p).inv
        (PointedCGWH.orthogonalSphere.{u, v} (n + q)) := by
  let S₁ := PointedCGWH.orthogonalSphere.{u, v} m
  let S₂ := PointedCGWH.orthogonalSphere.{u, v} p
  let T₁ := PointedCGWH.orthogonalSphere.{u, v} n
  let T₂ := PointedCGWH.orthogonalSphere.{u, v} q
  let S := PointedCGWH.orthogonalSphere.{u, v} (m + p)
  let T := PointedCGWH.orthogonalSphere.{u, v} (n + q)
  let H₁ := OrthogonalIndex.hom.{u, v} m n
  let H₂ := OrthogonalIndex.hom.{u, v} p q
  let H := OrthogonalIndex.hom.{u, v} (m + p) (n + q)
  let deltaS := PointedCGWH.orthogonalSphereTensorIso.{u, v} m p
  let deltaT := PointedCGWH.orthogonalSphereTensorIso.{u, v} n q
  let f : H₁ ⟶ (ihom S₁).obj T₁ := orthogonalSphereFunctor.{u, v}.map m n
  let g : H₂ ⟶ (ihom S₂).obj T₂ := orthogonalSphereFunctor.{u, v}.map p q
  let total : H ⟶ (ihom S).obj T :=
    orthogonalSphereFunctor.{u, v}.map (m + p) (n + q)
  let tau : H₁ ⊗ H₂ ⟶ H := OrthogonalIndex.tensorMap.{u, v} m n p q
  let a₁ := PointedCGWH.orthogonalSphereAction.{u, v} m n
  let a₂ := PointedCGWH.orthogonalSphereAction.{u, v} p q
  let a := PointedCGWH.orthogonalSphereAction.{u, v} (m + p) (n + q)
  change (f ⊗ₘ g) ≫
      (MonoidalClosed.enrichedMonoidalCategoryDataSelf PointedCGWH.{u, v}).tensorMap
        S₁ T₁ S₂ T₂ ≫
      eHomWhiskerLeft PointedCGWH.{u, v} (S₁ ⊗ S₂) deltaT.inv =
    tau ≫ total ≫ eHomWhiskerRight PointedCGWH.{u, v} deltaS.inv T
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerLeft,
    MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerRight]
  simp only [← Category.assoc]
  rw [MonoidalClosed.uncurry_natural_right, MonoidalClosed.uncurry_pre_app]
  conv_rhs => rw [MonoidalClosed.uncurry_natural_left]
  have hExternal :
      MonoidalClosed.uncurry
        ((f ⊗ₘ g) ≫
          (MonoidalClosed.enrichedMonoidalCategoryDataSelf PointedCGWH.{u, v}).tensorMap
            S₁ T₁ S₂ T₂) =
        tensorμ S₁ S₂ H₁ H₂ ≫
          (MonoidalClosed.uncurry f ⊗ₘ MonoidalClosed.uncurry g) :=
    EnrichedFunctor.externalTensor_uncurry
      orthogonalSphereFunctor.{u, v} orthogonalSphereFunctor.{u, v}
      (m, p) (n, q)
  have hf : MonoidalClosed.uncurry f = (β_ S₁ H₁).hom ≫ a₁ :=
    orthogonalSphereFunctor_uncurry m n
  have hg : MonoidalClosed.uncurry g = (β_ S₂ H₂).hom ≫ a₂ :=
    orthogonalSphereFunctor_uncurry p q
  have htotal : MonoidalClosed.uncurry total = (β_ S H).hom ≫ a :=
    orthogonalSphereFunctor_uncurry (m + p) (n + q)
  rw [hExternal, hf, hg, htotal]
  have hOriginal :
      (tau ⊗ₘ deltaS.inv) ≫ a ≫ deltaT.hom =
        tensorμ H₁ H₂ S₁ S₂ ≫ (a₁ ⊗ₘ a₂) :=
    PointedCGWH.orthogonalSphereAction_blockSum.{u, v} m n p q
  have hBlock := congrArg (fun k => k ≫ deltaT.inv) hOriginal
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at hBlock
  simp only [Category.assoc]
  rw [braiding_naturality_right_assoc, braiding_naturality_left_assoc,
    ← tensorHom_def'_assoc, hBlock]
  simp only [← tensorHom_comp_tensorHom, Category.assoc]
  simpa only [Category.assoc] using
    congrArg (fun k => k ≫ (a₁ ⊗ₘ a₂) ≫ deltaT.inv)
      (sphere_tensorμ_braiding S₁ S₂ H₁ H₂)


private theorem sphere_left_unit_coherence (n : OrthogonalIndex) :
    letI : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
    letI : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
    (λ_ (PointedCGWH.orthogonalSphere.{u, v} n)).hom =
      PointedCGWH.orthogonalSphereZeroIso.{u, v}.inv ▷
          PointedCGWH.orthogonalSphere.{u, v} n ≫
        (PointedCGWH.orthogonalSphereTensorIso.{u, v} 0 n).inv ≫
        orthogonalSphereMap.{u, v} (λ_ n).hom := by
  let _ : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
  let _ : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
  rw [orthogonalSphereMap_leftUnitor]
  have h :
      (orthogonalSphereCoordinateIso.{u, v} (finCongr (Nat.zero_add n))).hom =
        (PointedCGWH.orthogonalSphereTensorIso.{u, v} 0 n).hom ≫
          PointedCGWH.orthogonalSphereZeroIso.{u, v}.hom ▷
            PointedCGWH.orthogonalSphere.{u, v} n ≫
          (λ_ (PointedCGWH.orthogonalSphere.{u, v} n)).hom := by
    have hOriginal := PointedCGWH.orthogonalSphereTensorIso_leftUnit.{u, v} n
    simp only [tensorHom_id] at hOriginal
    exact hOriginal
  rw [h]
  simp only [Iso.inv_hom_id_assoc]
  rw [← comp_whiskerRight_assoc]
  simp only [Iso.inv_hom_id, id_whiskerRight, Category.id_comp]

private theorem sphere_right_unit_coherence (n : OrthogonalIndex) :
    letI : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
    letI : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
    (ρ_ (PointedCGWH.orthogonalSphere.{u, v} n)).hom =
      PointedCGWH.orthogonalSphere.{u, v} n ◁
          PointedCGWH.orthogonalSphereZeroIso.{u, v}.inv ≫
        (PointedCGWH.orthogonalSphereTensorIso.{u, v} n 0).inv ≫
        orthogonalSphereMap.{u, v} (ρ_ n).hom := by
  let _ : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
  let _ : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
  rw [orthogonalSphereMap_rightUnitor]
  have h :
      (orthogonalSphereCoordinateIso.{u, v} (finCongr (Nat.add_zero n))).hom =
        (PointedCGWH.orthogonalSphereTensorIso.{u, v} n 0).hom ≫
          PointedCGWH.orthogonalSphere.{u, v} n ◁
            PointedCGWH.orthogonalSphereZeroIso.{u, v}.hom ≫
          (ρ_ (PointedCGWH.orthogonalSphere.{u, v} n)).hom := by
    have hOriginal := PointedCGWH.orthogonalSphereTensorIso_rightUnit.{u, v} n
    simp only [id_tensorHom] at hOriginal
    exact hOriginal
  rw [h]
  simp only [Iso.inv_hom_id_assoc]
  rw [← whiskerLeft_comp_assoc]
  simp only [Iso.inv_hom_id, whiskerLeft_id, Category.id_comp]

private theorem sphere_associativity_coherence (m n p : OrthogonalIndex) :
    letI : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
    letI : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
    (PointedCGWH.orthogonalSphereTensorIso.{u, v} m n).inv ▷
        PointedCGWH.orthogonalSphere.{u, v} p ≫
      (PointedCGWH.orthogonalSphereTensorIso.{u, v} (m + n) p).inv ≫
      orthogonalSphereMap.{u, v} (α_ m n p).hom =
    (α_ (PointedCGWH.orthogonalSphere.{u, v} m)
      (PointedCGWH.orthogonalSphere.{u, v} n)
      (PointedCGWH.orthogonalSphere.{u, v} p)).hom ≫
      PointedCGWH.orthogonalSphere.{u, v} m ◁
        (PointedCGWH.orthogonalSphereTensorIso.{u, v} n p).inv ≫
      (PointedCGWH.orthogonalSphereTensorIso.{u, v} m (n + p)).inv := by
  let _ : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
  let _ : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
  rw [orthogonalSphereMap_associator]
  have h :
      (orthogonalSphereCoordinateIso.{u, v} (finCongr (Nat.add_assoc m n p))).hom ≫
        (PointedCGWH.orthogonalSphereTensorIso.{u, v} m (n + p)).hom ≫
        PointedCGWH.orthogonalSphere.{u, v} m ◁
          (PointedCGWH.orthogonalSphereTensorIso.{u, v} n p).hom =
      (PointedCGWH.orthogonalSphereTensorIso.{u, v} (m + n) p).hom ≫
        (PointedCGWH.orthogonalSphereTensorIso.{u, v} m n).hom ▷
          PointedCGWH.orthogonalSphere.{u, v} p ≫
        (α_ (PointedCGWH.orthogonalSphere.{u, v} m)
          (PointedCGWH.orthogonalSphere.{u, v} n)
          (PointedCGWH.orthogonalSphere.{u, v} p)).hom := by
    have hOriginal := PointedCGWH.orthogonalSphereTensorIso_associativity.{u, v} m n p
    simp only [tensorHom_id, id_tensorHom] at hOriginal
    exact hOriginal
  apply (cancel_mono
    ((PointedCGWH.orthogonalSphereTensorIso.{u, v} m (n + p)).hom ≫
      PointedCGWH.orthogonalSphere.{u, v} m ◁
        (PointedCGWH.orthogonalSphereTensorIso.{u, v} n p).hom)).1
  simp only [Category.assoc]
  slice_lhs 3 5 => rw [h]
  simp only [Iso.inv_hom_id_assoc,
    ← comp_whiskerRight_assoc, Iso.inv_hom_id, id_whiskerRight, Category.id_comp,
    ← whiskerLeft_comp, whiskerLeft_id, Category.comp_id]

private theorem sphere_braided_coherence (m n : OrthogonalIndex) :
    letI : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
    letI : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
    letI : SymmetricCategory OrthogonalIndex := OrthogonalIndex.symmetricCategory.{u, v}
    (PointedCGWH.orthogonalSphereTensorIso.{u, v} m n).inv ≫
        orthogonalSphereMap.{u, v} (β_ m n).hom =
      (β_ (PointedCGWH.orthogonalSphere.{u, v} m)
        (PointedCGWH.orthogonalSphere.{u, v} n)).hom ≫
        (PointedCGWH.orthogonalSphereTensorIso.{u, v} n m).inv := by
  let _ : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
  let _ : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
  let _ : SymmetricCategory OrthogonalIndex := OrthogonalIndex.symmetricCategory.{u, v}
  rw [orthogonalSphereMap_braiding]
  have h :
      (orthogonalSphereCoordinateIso.{u, v}
        (finAddFlip : Fin (m + n) ≃ Fin (n + m))).hom ≫
        (PointedCGWH.orthogonalSphereTensorIso.{u, v} n m).hom =
      (PointedCGWH.orthogonalSphereTensorIso.{u, v} m n).hom ≫
        (β_ (PointedCGWH.orthogonalSphere.{u, v} m)
          (PointedCGWH.orthogonalSphere.{u, v} n)).hom := by
    exact PointedCGWH.orthogonalSphereTensorIso_blockSwap.{u, v} m n
  apply (cancel_mono (PointedCGWH.orthogonalSphereTensorIso.{u, v} n m).hom).1
  simp only [Category.assoc]
  rw [h]
  simp only [Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

/-- The native enriched lax monoidal sphere data: the original unit
identification and inverse ordered sphere splitting, with the entire Hom
naturality square and literal ordinary unit/associator images proved. -/
def orthogonalSphereMonoidalData :
    letI : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
    letI : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
    letI : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
      OrthogonalIndex.enrichedOrdinaryCategory.{u, v}
    EnrichedFunctor.LaxMonoidalData
      OrthogonalIndex.enrichedMonoidalData.{u, v}
      (MonoidalClosed.enrichedMonoidalCategoryDataSelf PointedCGWH.{u, v})
      orthogonalSphereFunctor.{u, v} := by
  letI : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
  letI : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
  letI : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
    OrthogonalIndex.enrichedOrdinaryCategory.{u, v}
  refine
    { epsilon := PointedCGWH.orthogonalSphereUnitIso.{u, v}.hom
      mu := fun m n => (PointedCGWH.orthogonalSphereTensorIso.{u, v} m n).inv
      mu_naturality := ?_
      unit := ?_
      assoc := ?_ }
  · intro m n p q
    change
      (orthogonalSphereFunctor.{u, v}.map m n ⊗ₘ
          orthogonalSphereFunctor.{u, v}.map p q) ≫
        (MonoidalClosed.enrichedMonoidalCategoryDataSelf PointedCGWH.{u, v}).tensorMap
          (PointedCGWH.orthogonalSphere.{u, v} m)
          (PointedCGWH.orthogonalSphere.{u, v} n)
          (PointedCGWH.orthogonalSphere.{u, v} p)
          (PointedCGWH.orthogonalSphere.{u, v} q) ≫
        eHomWhiskerLeft PointedCGWH.{u, v}
          (PointedCGWH.orthogonalSphere.{u, v} m ⊗
            PointedCGWH.orthogonalSphere.{u, v} p)
          (PointedCGWH.orthogonalSphereTensorIso.{u, v} n q).inv =
      OrthogonalIndex.tensorMap.{u, v} m n p q ≫
        orthogonalSphereFunctor.{u, v}.map (m + p) (n + q) ≫
        eHomWhiskerRight PointedCGWH.{u, v}
          (PointedCGWH.orthogonalSphereTensorIso.{u, v} m p).inv
          (PointedCGWH.orthogonalSphere.{u, v} (n + q))
    exact (by exact sphere_tensor_naturality m n p q)
  · intro n
    change
      ((λ_ (PointedCGWH.orthogonalSphere.{u, v} n)).hom =
        PointedCGWH.orthogonalSphereZeroIso.{u, v}.inv ▷
            PointedCGWH.orthogonalSphere.{u, v} n ≫
          (PointedCGWH.orthogonalSphereTensorIso.{u, v} 0 n).inv ≫
          orthogonalSphereMap.{u, v} (λ_ n).hom) ∧
      ((ρ_ (PointedCGWH.orthogonalSphere.{u, v} n)).hom =
        PointedCGWH.orthogonalSphere.{u, v} n ◁
            PointedCGWH.orthogonalSphereZeroIso.{u, v}.inv ≫
          (PointedCGWH.orthogonalSphereTensorIso.{u, v} n 0).inv ≫
          orthogonalSphereMap.{u, v} (ρ_ n).hom)
    exact (by exact ⟨sphere_left_unit_coherence n, sphere_right_unit_coherence n⟩)
  · intro m n p
    change
      (PointedCGWH.orthogonalSphereTensorIso.{u, v} m n).inv ▷
          PointedCGWH.orthogonalSphere.{u, v} p ≫
        (PointedCGWH.orthogonalSphereTensorIso.{u, v} (m + n) p).inv ≫
        orthogonalSphereMap.{u, v} (α_ m n p).hom =
      (α_ (PointedCGWH.orthogonalSphere.{u, v} m)
        (PointedCGWH.orthogonalSphere.{u, v} n)
        (PointedCGWH.orthogonalSphere.{u, v} p)).hom ≫
        PointedCGWH.orthogonalSphere.{u, v} m ◁
          (PointedCGWH.orthogonalSphereTensorIso.{u, v} n p).inv ≫
        (PointedCGWH.orthogonalSphereTensorIso.{u, v} m (n + p)).inv
    exact (by exact sphere_associativity_coherence m n p)

/-- The lax unit is the original sphere-unit isomorphism's forward map. -/
@[simp]
theorem orthogonalSphereMonoidalData_epsilon :
    letI : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
    letI : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
    letI : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
      OrthogonalIndex.enrichedOrdinaryCategory.{u, v}
    orthogonalSphereMonoidalData.{u, v}.epsilon =
      PointedCGWH.orthogonalSphereUnitIso.{u, v}.hom := rfl

/-- The lax tensorator is the actual inverse of the original ordered sphere
splitting, not another isomorphism selected by an existence witness. -/
@[simp]
theorem orthogonalSphereMonoidalData_mu (m n : OrthogonalIndex) :
    letI : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
    letI : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
    letI : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
      OrthogonalIndex.enrichedOrdinaryCategory.{u, v}
    orthogonalSphereMonoidalData.{u, v}.mu m n =
      (PointedCGWH.orthogonalSphereTensorIso.{u, v} m n).inv := rfl

/-- Actual isomorphism witnesses for the native unit and every tensorator. -/
theorem orthogonalSphereStrongData :
    letI : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
    letI : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
    letI : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
      OrthogonalIndex.enrichedOrdinaryCategory.{u, v}
    EnrichedFunctor.StrongMonoidalData orthogonalSphereMonoidalData.{u, v} := by
  let _ : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
  let _ : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
  let _ : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
    OrthogonalIndex.enrichedOrdinaryCategory.{u, v}
  constructor
  · change IsIso PointedCGWH.orthogonalSphereUnitIso.{u, v}.hom
    infer_instance
  · intro m n
    change IsIso (PointedCGWH.orthogonalSphereTensorIso.{u, v} m n).inv
    infer_instance

/-- The original tensorator intertwines the actual native index block swap
with the native smash symmetry; no braided-coherence hypothesis is supplied. -/
theorem orthogonalSphereBraidedData :
    letI : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
    letI : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
    letI : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
      OrthogonalIndex.enrichedOrdinaryCategory.{u, v}
    letI : SymmetricCategory OrthogonalIndex := OrthogonalIndex.symmetricCategory.{u, v}
    EnrichedFunctor.LaxBraidedData orthogonalSphereMonoidalData.{u, v} := by
  let _ : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
  let _ : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
  let _ : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
    OrthogonalIndex.enrichedOrdinaryCategory.{u, v}
  let _ : SymmetricCategory OrthogonalIndex := OrthogonalIndex.symmetricCategory.{u, v}
  constructor
  intro m n
  change (PointedCGWH.orthogonalSphereTensorIso.{u, v} m n).inv ≫
      orthogonalSphereMap.{u, v} (β_ m n).hom =
    (β_ (PointedCGWH.orthogonalSphere.{u, v} m)
      (PointedCGWH.orthogonalSphere.{u, v} n)).hom ≫
      (PointedCGWH.orthogonalSphereTensorIso.{u, v} n m).inv
  exact sphere_braided_coherence m n

end CategoryTheory.Spectra
