/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.Index
public import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.MatrixIndex
public import MathlibExt.Topology.Category.PointedCGWH.OnePoint
public import Mathlib.Topology.Maps.Proper.CompactlyGenerated
public import Mathlib.Topology.Compactification.OnePoint.Sphere

/-!
# Orthogonal representation spheres and their one-point action

This file constructs the one-point compactification of the lifted standard
Euclidean representation, its direct-sum splitting, and the joint action of
the native enriched orthogonal indexing category.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CategoryTheory.Spectra Filter Matrix TopologicalSpace
open scoped ZeroObject

attribute [local instance] HasZeroObject.zeroMorphismsOfZeroObject

universe u v

namespace PointedCGWH

private theorem chosenNativeProduct_eq_tensorEquivProd
    (A B : CGWH.{u, v}) (a : A) (b : B) :
    Classical.choose
        ((CGWH.prodComparisonToTop_bijective A B).2 (a, b)) =
      (CGWH.tensorEquivProd A B).symm (a, b) := by
  apply (CGWH.prodComparisonToTop_bijective A B).1
  have hChosen :
      CGWH.prodComparisonToTop A B
          (Classical.choose
            ((CGWH.prodComparisonToTop_bijective A B).2 (a, b))) =
        (a, b) :=
    Classical.choose_spec
      ((CGWH.prodComparisonToTop_bijective A B).2 (a, b))
  have hCanonical :
      CGWH.prodComparisonToTop A B
          ((CGWH.tensorEquivProd A B).symm (a, b)) =
        (a, b) := by
    rw [← CGWH.tensorEquivProd_eq_prodComparisonToTop]
    exact (CGWH.tensorEquivProd A B).apply_symm_apply (a, b)
  exact hChosen.trans hCanonical.symm

private theorem nativeProductMap_choose
    {A B A' B' : CGWH.{u, v}}
    (f : A ⟶ A') (g : B ⟶ B') (a : A) (b : B) :
    (f ⊗ₘ g)
        (Classical.choose
          ((CGWH.prodComparisonToTop_bijective A B).2 (a, b))) =
      Classical.choose
        ((CGWH.prodComparisonToTop_bijective A' B').2 (f a, g b)) := by
  have hInput :
      (f ⊗ₘ g)
          (Classical.choose
            ((CGWH.prodComparisonToTop_bijective A B).2 (a, b))) =
        (f ⊗ₘ g) ((CGWH.tensorEquivProd A B).symm (a, b)) :=
    congrArg (fun z => (f ⊗ₘ g) z)
      (chosenNativeProduct_eq_tensorEquivProd A B a b)
  have hMap :
      (f ⊗ₘ g) ((CGWH.tensorEquivProd A B).symm (a, b)) =
        (CGWH.tensorEquivProd A' B').symm (f a, g b) :=
    CGWH.tensorEquivProd_symm_map f g a b
  have hOutput :
      (CGWH.tensorEquivProd A' B').symm (f a, g b) =
        Classical.choose
          ((CGWH.prodComparisonToTop_bijective A' B').2 (f a, g b)) :=
    (chosenNativeProduct_eq_tensorEquivProd A' B' (f a) (g b)).symm
  exact hInput.trans (hMap.trans hOutput)

/-- The Euclidean coordinate space lifted to the selected universe. -/
abbrev liftedEuclidean (n : OrthogonalIndex) :=
  ULift.{v, 0} (EuclideanSpace ℝ (Fin n))

/-- The orthogonal matrix space lifted to the selected universe. -/
abbrev liftedMatrix (m n : OrthogonalIndex) :=
  ULift.{v, 0} (OrthogonalMatrixHom m n)

private theorem euclideanOnePointGenerated (n : OrthogonalIndex) :
    UCompactlyGeneratedSpace.{u} (OnePoint (liftedEuclidean.{v} n)) := by
  let eLift : OnePoint (liftedEuclidean.{v} n) ≃ₜ
      OnePoint (EuclideanSpace ℝ (Fin n)) :=
    Homeomorph.onePointCongr
      (Homeomorph.ulift (X := EuclideanSpace ℝ (Fin n)))
  let eSphere := onePointEquivSphereOfFinrankEq
    (V := EuclideanSpace ℝ (Fin n))
    (ι := Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) + 1)) (by simp)
  let e := eLift.trans eSphere
  let _ : SequentialSpace (OnePoint (liftedEuclidean.{v} n)) :=
    e.symm.isQuotientMap.sequentialSpace
  infer_instance

private theorem euclideanProductOnePointGenerated (m n : OrthogonalIndex) :
    UCompactlyGeneratedSpace.{u}
      (OnePoint (liftedEuclidean.{v} m × liftedEuclidean.{v} n)) :=
  onePointProduct_generated _ _
    (euclideanOnePointGenerated.{u, v} m)
    (euclideanOnePointGenerated.{u, v} n)

/-- The homeomorphism splitting a lifted Euclidean space into two coordinate blocks. -/
noncomputable def liftedFinAddHomeomorph (m n : OrthogonalIndex) :
    liftedEuclidean.{v} (m + n) ≃ₜ
      liftedEuclidean.{v} m × liftedEuclidean.{v} n :=
  (Homeomorph.ulift
      (X := EuclideanSpace ℝ (Fin (m + n)))).trans <|
    (EuclideanSpace.finAddEquivProd (n := m) (m := n)).toHomeomorph.trans <|
      Homeomorph.prodCongr
        (Homeomorph.ulift (X := EuclideanSpace ℝ (Fin m))).symm
        (Homeomorph.ulift (X := EuclideanSpace ℝ (Fin n))).symm

/-- Split a lifted vector into its two ordered coordinate blocks. -/
noncomputable def orthogonalSphereSplitHomeomorph (m n : OrthogonalIndex) :
    ULift.{v, 0} (EuclideanSpace ℝ (Fin (m + n))) ≃ₜ
      ULift.{v, 0} (EuclideanSpace ℝ (Fin m)) ×
        ULift.{v, 0} (EuclideanSpace ℝ (Fin n)) :=
  liftedFinAddHomeomorph m n

/-- The ordered coordinate split is the original finite-dimensional product equivalence. -/
theorem orthogonalSphereSplitHomeomorph_apply (m n : OrthogonalIndex)
    (x : ULift.{v, 0} (EuclideanSpace ℝ (Fin (m + n)))) :
    orthogonalSphereSplitHomeomorph.{v} m n x =
      (ULift.up ((EuclideanSpace.finAddEquivProd (n := m) (m := n)) x.down).1,
        ULift.up ((EuclideanSpace.finAddEquivProd (n := m) (m := n)) x.down).2) := rfl

/-- The homeomorphism from the zero-dimensional coordinate space to the CGWH point. -/
noncomputable def sphereZeroCarrierHomeomorph :
    liftedEuclidean.{v} 0 ≃ₜ (CGWH.point.{u, v} : Type v) := by
  letI : Unique (CGWH.point.{u, v} : Type v) := by
    change Unique PUnit
    infer_instance
  letI : T2Space (CGWH.point.{u, v} : Type v) := by
    change T2Space PUnit
    infer_instance
  let e : liftedEuclidean.{v} 0 ≃ (CGWH.point.{u, v} : Type v) :=
    Equiv.ofUnique _ _
  apply Continuous.homeoOfEquivCompactToT2 (f := e)
  exact continuous_of_discreteTopology

/-- The one-point compactification of the lifted standard orthogonal
representation in degree `n`. -/
noncomputable def orthogonalSphere
    (n : OrthogonalIndex) : PointedCGWH.{u, v} :=
  onePointOf (liftedEuclidean.{v} n)

/-- The degree-zero representation sphere is the native smash unit. -/
noncomputable def orthogonalSphereZeroIso :
    orthogonalSphere.{u, v} 0 ≅ 𝟙_ PointedCGWH.{u, v} := by
  letI : CompactSpace (CGWH.point.{u, v} : Type v) := by
    change CompactSpace PUnit
    infer_instance
  letI : T2Space (CGWH.point.{u, v} : Type v) := by
    change T2Space PUnit
    infer_instance
  exact (onePointHomeomorphOfHomeomorph
    (sphereZeroCarrierHomeomorph.{u, v})).trans
      (addBasepointIsoOnePointOfCompact CGWH.point).symm

/-- The monoidal-unit map into the degree-zero representation sphere. -/
noncomputable def orthogonalSphereUnitIso :
    𝟙_ PointedCGWH.{u, v} ≅ orthogonalSphere.{u, v} 0 :=
  orthogonalSphereZeroIso.{u, v}.symm

/-- Splitting a representation sphere along an ordered direct sum. -/
noncomputable def orthogonalSphereTensorIso
    (m n : OrthogonalIndex) :
    orthogonalSphere.{u, v} (m + n) ≅
      orthogonalSphere.{u, v} m ⊗ orthogonalSphere.{u, v} n :=
  (onePointHomeomorphOfHomeomorph
    (liftedFinAddHomeomorph.{v} m n)).trans
      (onePointProdSmashIso _ _
        (by exact euclideanOnePointGenerated.{u, v} m)
        (by exact euclideanOnePointGenerated.{u, v} n))

/-- The pointed isomorphism presenting an orthogonal Hom object as a one-point extension. -/
noncomputable def homToOnePointIso (m n : OrthogonalIndex) :
    letI : CompactSpace (liftedMatrix.{v} m n) := inferInstance
    letI : LocallyCompactSpace (liftedMatrix.{v} m n) := inferInstance
    OrthogonalIndex.hom.{u, v} m n ≅
      onePointOf.{u, v} (liftedMatrix.{v} m n) := by
  let _ : PseudoMetrizableSpace (liftedMatrix.{v} m n) :=
    Homeomorph.ulift.isInducing.pseudoMetrizableSpace
  let _ : CompactSpace (liftedMatrix.{v} m n) := inferInstance
  let _ : T2Space (liftedMatrix.{v} m n) := inferInstance
  let _ : LocallyCompactSpace (liftedMatrix.{v} m n) := inferInstance
  change (Under.costar CGWH.point).obj
      (CGWH.of.{u, v} (liftedMatrix.{v} m n)) ≅
    onePointOf.{u, v} (liftedMatrix.{v} m n)
  exact addBasepointIsoOnePointOfCompact
    (CGWH.of.{u, v} (liftedMatrix.{v} m n))

private theorem compactMatrixOnePointGenerated (m n : OrthogonalIndex) :
    UCompactlyGeneratedSpace.{u}
      (OnePoint (liftedMatrix.{v} m n)) := by
  let _ : PseudoMetrizableSpace (liftedMatrix.{v} m n) :=
    Homeomorph.ulift.isInducing.pseudoMetrizableSpace
  let _ : CompactSpace (liftedMatrix.{v} m n) := inferInstance
  let _ : T2Space (liftedMatrix.{v} m n) := inferInstance
  let e : PUnit.{v + 1} ⊕ liftedMatrix.{v} m n ≃ₜ
      OnePoint (liftedMatrix.{v} m n) := by
    let f : PUnit.{v + 1} ⊕ liftedMatrix.{v} m n ≃
        OnePoint (liftedMatrix.{v} m n) :=
      { toFun := Sum.elim (fun _ ↦ OnePoint.infty) (fun x ↦ x)
        invFun := OnePoint.rec (Sum.inl PUnit.unit) Sum.inr
        left_inv := by
          intro z
          rcases z with p | x
          · cases p
            rfl
          · rfl
        right_inv := by
          intro z
          induction z using OnePoint.rec <;> rfl }
    apply Continuous.homeoOfEquivCompactToT2 (f := f)
    apply continuous_sum_dom.2
    constructor
    · change Continuous (fun _ : PUnit.{v + 1} ↦
        (OnePoint.infty : OnePoint (liftedMatrix.{v} m n)))
      exact continuous_const
    · change Continuous ((↑) : liftedMatrix.{v} m n →
        OnePoint (liftedMatrix.{v} m n))
      exact OnePoint.continuous_coe
  let _ : UCompactlyGeneratedSpace.{u} PUnit.{v + 1} := inferInstance
  let _ : UCompactlyGeneratedSpace.{u} (liftedMatrix.{v} m n) :=
    inferInstance
  let _ : UCompactlyGeneratedSpace.{u}
      (PUnit.{v + 1} ⊕ liftedMatrix.{v} m n) := inferInstance
  exact uCompactlyGeneratedSpace_of_coinduced e.continuous
    e.isQuotientMap.eq_coinduced

/-- Evaluation of a lifted orthogonal matrix on a lifted Euclidean vector. -/
def liftedEvaluation {m n : OrthogonalIndex} :
    liftedMatrix.{v} m n × liftedEuclidean.{v} m →
      liftedEuclidean.{v} n :=
  fun z ↦ ULift.up <|
    (EuclideanSpace.equiv (Fin n) ℝ).symm
      (z.1.down.1 *ᵥ z.2.down.ofLp)

private theorem liftedEvaluation_continuous {m n : OrthogonalIndex} :
    Continuous (liftedEvaluation.{v} (m := m) (n := n)) := by
  exact continuous_uliftUp.comp
    ((EuclideanSpace.equiv (Fin n) ℝ).symm.continuous.comp <|
      OrthogonalMatrixHom.continuous_evaluation.comp
        ((continuous_uliftDown.comp continuous_fst).prodMk
          (continuous_uliftDown.comp continuous_snd)))

private noncomputable def actionHomeomorph (m n : OrthogonalIndex) :
    liftedMatrix.{v} m n × liftedEuclidean.{v} m ≃ₜ
      liftedMatrix.{v} m n × liftedEuclidean.{v} n where
  toFun z := (z.1, liftedEvaluation z)
  invFun z := (z.1, ULift.up <|
    (EuclideanSpace.equiv (Fin m) ℝ).symm
      (z.1.down.transpose.1 *ᵥ z.2.down.ofLp))
  left_inv z := by
    rcases z with ⟨⟨A⟩, ⟨x⟩⟩
    apply Prod.ext
    · rfl
    · apply ULift.ext
      apply WithLp.ofLp_injective
      change A.1.transpose *ᵥ (A.1 *ᵥ x.ofLp) = x.ofLp
      rw [Matrix.mulVec_mulVec, A.2.1, Matrix.one_mulVec]
  right_inv z := by
    rcases z with ⟨⟨A⟩, ⟨y⟩⟩
    apply Prod.ext
    · rfl
    · apply ULift.ext
      apply WithLp.ofLp_injective
      change A.1 *ᵥ (A.1.transpose *ᵥ y.ofLp) = y.ofLp
      rw [Matrix.mulVec_mulVec, A.2.2, Matrix.one_mulVec]
  continuous_toFun :=
    continuous_fst.prodMk liftedEvaluation_continuous
  continuous_invFun := continuous_fst.prodMk <| continuous_uliftUp.comp <|
    (EuclideanSpace.equiv (Fin m) ℝ).symm.continuous.comp <|
      OrthogonalMatrixHom.continuous_evaluation.comp <|
        ((OrthogonalMatrixHom.continuous_transpose.comp
          (continuous_uliftDown.comp continuous_fst)).prodMk
            (continuous_uliftDown.comp continuous_snd))

/-- Joint matrix evaluation is proper on the original lifted parameter and
vector spaces, including degree zero and the empty unequal-degree cases. -/
theorem orthogonalSphereAction_isProperMap (m n : OrthogonalIndex) :
    IsProperMap fun z :
        ULift.{v, 0} (OrthogonalMatrixHom m n) ×
          ULift.{v, 0} (EuclideanSpace ℝ (Fin m)) ↦
      (ULift.up
        ((EuclideanSpace.equiv (Fin n) ℝ).symm
          (z.1.down.1 *ᵥ z.2.down.ofLp)) :
        ULift.{v, 0} (EuclideanSpace ℝ (Fin n))) := by
  change IsProperMap (liftedEvaluation.{v} (m := m) (n := n))
  let _ : CompactSpace (liftedMatrix.{v} m n) := inferInstance
  exact isProperMap_snd_of_compactSpace.comp
    (actionHomeomorph.{v} m n).isProperMap

private theorem evaluationTendstoCoclosedCompact (m n : OrthogonalIndex) :
    Tendsto (liftedEvaluation.{v} (m := m) (n := n))
      (coclosedCompact
        (liftedMatrix.{v} m n × liftedEuclidean.{v} m))
      (coclosedCompact (liftedEuclidean.{v} n)) := by
  have hProper := orthogonalSphereAction_isProperMap.{v} m n
  change IsProperMap (liftedEvaluation.{v} (m := m) (n := n)) at hProper
  have h := (isProperMap_iff_tendsto_cocompact.mp
    hProper).2
  simpa only [coclosedCompact_eq_cocompact] using h

/-- The joint orthogonal action on one-point representation spheres. -/
noncomputable def orthogonalSphereAction (m n : OrthogonalIndex) :
    OrthogonalIndex.hom.{u, v} m n ⊗ orthogonalSphere.{u, v} m ⟶
      orthogonalSphere.{u, v} n := by
  let K := liftedMatrix.{v} m n
  let E := liftedEuclidean.{v} m
  let _ : CompactSpace K := inferInstance
  let _ : T2Space K := inferInstance
  let _ : LocallyCompactSpace K := inferInstance
  let f : C(K × E, liftedEuclidean.{v} n) :=
    ⟨liftedEvaluation, by exact liftedEvaluation_continuous⟩
  exact ((homToOnePointIso.{u, v} m n).hom ⊗ₘ
        𝟙 (orthogonalSphere.{u, v} m)) ≫
      (onePointProdSmashIso K E
        (by exact compactMatrixOnePointGenerated.{u, v} m n)
        (by exact euclideanOnePointGenerated.{u, v} m)).inv ≫
      onePointMapOfProper f (by exact evaluationTendstoCoclosedCompact.{v} m n)

/-- Joint continuity of the raw matrix action, including the whole infinity
face uniformly in the matrix parameter. -/
theorem orthogonalSphereAction_continuous (m n : OrthogonalIndex) :
    Continuous fun z :
        ULift.{v, 0} (OrthogonalMatrixHom m n) ×
          OnePoint (ULift.{v, 0} (EuclideanSpace ℝ (Fin m))) ↦
      (OnePoint.rec
        (OnePoint.infty :
          OnePoint (ULift.{v, 0} (EuclideanSpace ℝ (Fin n))))
        (fun x : ULift.{v, 0} (EuclideanSpace ℝ (Fin m)) ↦
          ((ULift.up <|
            (EuclideanSpace.equiv (Fin n) ℝ).symm
              (z.1.down.1 *ᵥ x.down.ofLp) :
                ULift.{v, 0} (EuclideanSpace ℝ (Fin n))) :
            OnePoint (ULift.{v, 0} (EuclideanSpace ℝ (Fin n)))))
        z.2 : OnePoint
          (ULift.{v, 0} (EuclideanSpace ℝ (Fin n)))) := by
  let K := liftedMatrix.{v} m n
  let E := liftedEuclidean.{v} m
  let N := liftedEuclidean.{v} n
  let _ : CompactSpace K := inferInstance
  let _ : T2Space K := inferInstance
  let _ : LocallyCompactSpace K := inferInstance
  let f : C(K × E, N) := ⟨liftedEvaluation, liftedEvaluation_continuous⟩
  let F := onePointMapOfProper.{v, v} f
    (evaluationTendstoCoclosedCompact.{v} m n)
  let embedFinite : K × OnePoint E → OnePoint K × OnePoint E :=
    fun z ↦ ((z.1 : OnePoint K), z.2)
  have hInclude : Continuous embedFinite :=
    (OnePoint.continuous_coe.comp continuous_fst).prodMk continuous_snd
  have hCollapse : Continuous (rawCollapse K E ∘ embedFinite) :=
    (rawCollapse_continuous K E).comp hInclude
  let _ : UCompactlyGeneratedSpace.{v} (OnePoint K) :=
    compactMatrixOnePointGenerated.{v, v} m n
  let _ : UCompactlyGeneratedSpace.{v} (OnePoint E) :=
    euclideanOnePointGenerated.{v, v} m
  let _ : UCompactlyGeneratedSpace.{v} (OnePoint (K × E)) :=
    onePointProduct_generated K E inferInstance inferInstance
  let _ : UCompactlyGeneratedSpace.{v} (OnePoint N) :=
    euclideanOnePointGenerated.{v, v} n
  let cKE := CompactlyGenerated.coreflectionCounitHomeoData.{v, v} (OnePoint (K × E))
  let cN := CompactlyGenerated.coreflectionCounitHomeoData.{v, v} (OnePoint N)
  have hCollapseCore :
      Continuous (cKE.1.symm ∘ rawCollapse K E ∘ embedFinite) :=
    cKE.1.symm.continuous.comp hCollapse
  have hTotal :
      Continuous (cN.1 ∘ F.right ∘ cKE.1.symm ∘
        rawCollapse K E ∘ embedFinite) :=
    cN.1.continuous.comp
      ((ConcreteCategory.hom F.right).continuous.comp hCollapseCore)
  convert hTotal using 1
  funext z
  rcases z with ⟨A, z⟩
  induction z using OnePoint.rec with
  | infty =>
      dsimp only [Function.comp_apply, embedFinite, rawCollapse]
      change OnePoint.infty = cN.1 (F.right (cKE.1.symm OnePoint.infty))
      have hc : cKE.1.symm OnePoint.infty = OnePoint.infty :=
        (cKE.2 (cKE.1.symm OnePoint.infty)).symm.trans
          (cKE.1.apply_symm_apply OnePoint.infty)
      rw [hc]
      have hMap : F.right OnePoint.infty = (OnePoint.infty : OnePoint N) :=
        onePointMapOfProper_infty.{v, v} f
          (evaluationTendstoCoclosedCompact.{v} m n)
      have hCounit : cN.1 (F.right OnePoint.infty) = F.right OnePoint.infty :=
        cN.2 (F.right OnePoint.infty)
      exact (hCounit.trans hMap).symm
  | coe x =>
      dsimp only [Function.comp_apply, embedFinite, rawCollapse]
      change (liftedEvaluation (A, x) : OnePoint N) =
        cN.1 (F.right (cKE.1.symm ((A, x) : OnePoint (K × E))))
      have hc : cKE.1.symm ((A, x) : OnePoint (K × E)) =
          ((A, x) : OnePoint (K × E)) :=
        (cKE.2 (cKE.1.symm ((A, x) : OnePoint (K × E)))).symm.trans
          (cKE.1.apply_symm_apply ((A, x) : OnePoint (K × E)))
      rw [hc]
      have hMap : F.right ((A, x) : OnePoint (K × E)) =
          (liftedEvaluation (A, x) : OnePoint N) :=
        onePointMapOfProper_coe.{v, v} f
          (evaluationTendstoCoclosedCompact.{v} m n) (A, x)
      have hCounit : cN.1 (F.right ((A, x) : OnePoint (K × E))) =
          F.right ((A, x) : OnePoint (K × E)) :=
        cN.2 (F.right ((A, x) : OnePoint (K × E)))
      exact (hCounit.trans hMap).symm

private theorem homToOnePointIso_matrixPoint
    {m n : OrthogonalIndex} (A : OrthogonalMatrixHom m n) :
    let K := liftedMatrix.{v} m n
    letI : CompactSpace K := inferInstance
    letI : LocallyCompactSpace K := inferInstance
    let I := homToOnePointIso.{u, v} m n
    let t : (𝟙_ PointedCGWH.{u, v}).right :=
      (coprod.inr : CGWH.point.{u, v} ⟶
        CGWH.point.{u, v} ⨿ CGWH.point.{u, v}) PUnit.unit
    I.hom.right ((OrthogonalIndex.matrixPoint.{u, v} A).right t) =
      ((ULift.up A : K) : OnePoint K) := by
  dsimp only
  let _ : PseudoMetrizableSpace (liftedMatrix.{v} m n) :=
    Homeomorph.ulift.isInducing.pseudoMetrizableSpace
  let _ : CompactSpace (liftedMatrix.{v} m n) := inferInstance
  let _ : T2Space (liftedMatrix.{v} m n) := inferInstance
  let _ : LocallyCompactSpace (liftedMatrix.{v} m n) := inferInstance
  let X : CGWH.{u, v} := CGWH.of (liftedMatrix.{v} m n)
  let g : CGWH.point.{u, v} ⟶ X :=
    (CGWH.pointHomEquiv X).symm (ULift.up A)
  let t : (𝟙_ PointedCGWH.{u, v}).right :=
    (coprod.inr : CGWH.point.{u, v} ⟶
      CGWH.point.{u, v} ⨿ CGWH.point.{u, v}) PUnit.unit
  change (addBasepointIsoOnePointOfCompact X).hom.right
      (((Under.costar CGWH.point).map g).right t) =
    ((ULift.up A : liftedMatrix.{v} m n) :
      OnePoint (liftedMatrix.{v} m n))
  have ht : ((Under.costar CGWH.point).map g).right t =
      (coprod.inr : X ⟶ CGWH.point.{u, v} ⨿ X) (ULift.up A) := by
    change (coprod.map (𝟙 CGWH.point.{u, v}) g)
      ((coprod.inr : CGWH.point.{u, v} ⟶
        CGWH.point.{u, v} ⨿ CGWH.point.{u, v}) PUnit.unit) = _
    let unitPoint : CGWH.point.{u, v} := by
      change PUnit.{v + 1}
      exact PUnit.unit
    have hInr :
        (coprod.inr : CGWH.point.{u, v} ⟶
          CGWH.point.{u, v} ⨿ CGWH.point.{u, v}) ≫
          coprod.map (𝟙 CGWH.point.{u, v}) g =
        g ≫ (coprod.inr : X ⟶ CGWH.point.{u, v} ⨿ X) :=
      coprod.inr_map _ _
    have hAt := ConcreteCategory.congr_hom hInr unitPoint
    change (coprod.map (𝟙 CGWH.point.{u, v}) g)
        ((coprod.inr : CGWH.point.{u, v} ⟶
          CGWH.point.{u, v} ⨿ CGWH.point.{u, v}) unitPoint) =
      (coprod.inr : X ⟶ CGWH.point.{u, v} ⨿ X) (g unitPoint) at hAt
    have hPoint : g unitPoint = ULift.up A :=
      CGWH.pointHomEquiv_symm_apply_apply X (ULift.up A) unitPoint
    exact hAt.trans (congrArg
      (ConcreteCategory.hom (coprod.inr : X ⟶ CGWH.point.{u, v} ⨿ X)) hPoint)
  rw [ht]
  let rawHomeo := compactFreePointRawHomeo (X : Type v)
  let _ : UCompactlyGeneratedSpace.{u} PUnit.{v + 1} := inferInstance
  let _ : UCompactlyGeneratedSpace.{u} (X : Type v) :=
    X.toCompactlyGenerated.is_compactly_generated
  let _ : UCompactlyGeneratedSpace.{u} (PUnit.{v + 1} ⊕ X) := inferInstance
  let W : CGWH.{u, v} := CGWH.of (PUnit.{v + 1} ⊕ X)
  let i0 : CGWH.point.{u, v} ⟶ W := ConcreteCategory.ofHom
    ⟨(Sum.inl : PUnit.{v + 1} → PUnit.{v + 1} ⊕ X), continuous_inl⟩
  let i1 : X ⟶ W := ConcreteCategory.ofHom
    ⟨(Sum.inr : X → PUnit.{v + 1} ⊕ X), continuous_inr⟩
  let c : BinaryCofan CGWH.point X := BinaryCofan.mk i0 i1
  have hc : IsColimit c := BinaryCofan.isColimitMk
      (fun s ↦ ConcreteCategory.ofHom
        ⟨Sum.elim s.inl s.inr,
          continuous_sum_dom.2
            ⟨(ConcreteCategory.hom s.inl).continuous,
              (ConcreteCategory.hom s.inr).continuous⟩⟩)
      (by
        intro s
        apply ConcreteCategory.hom_ext
        intro p
        change PUnit.{v + 1} at p
        cases p
        rfl)
      (by
        intro s
        apply ConcreteCategory.hom_ext
        intro x
        rfl)
      (by
        intro s k h0 h1
        apply ConcreteCategory.hom_ext
        intro z
        rcases z with p | x
        · exact ConcreteCategory.congr_hom h0 p
        · exact ConcreteCategory.congr_hom h1 x)
  let e : CGWH.point.{u, v} ⨿ X ≅ W :=
    (coprodIsCoprod CGWH.point X).coconePointUniqueUpToIso hc
  let _ : UCompactlyGeneratedSpace.{u} (OnePoint (X : Type v)) :=
    compactMatrixOnePointGenerated.{u, v} m n
  let rawIso : W ≅ CGWH.of (OnePoint X) := CGWH.isoOfHomeo rawHomeo
  let core := CompactlyGenerated.coreflectionCounitHomeoData.{u, v} (OnePoint X)
  let coreIso : (onePointOf.{u, v} (X : Type v)).right ≅
      CGWH.of (OnePoint X) := CGWH.isoOfHomeo core.1
  change coreIso.inv (rawIso.hom
      (e.hom ((coprod.inr : X ⟶ CGWH.point.{u, v} ⨿ X) (ULift.up A)))) =
    ((ULift.up A : liftedMatrix.{v} m n) :
      OnePoint (liftedMatrix.{v} m n))
  have he : (coprod.inr : X ⟶ CGWH.point.{u, v} ⨿ X) ≫ e.hom = i1 :=
    IsColimit.comp_coconePointUniqueUpToIso_hom
      (coprodIsCoprod CGWH.point X) hc ⟨WalkingPair.right⟩
  have hex := ConcreteCategory.congr_hom he (ULift.up A)
  rw [ConcreteCategory.comp_apply] at hex
  rw [hex]
  change core.1.symm (rawHomeo (Sum.inr (ULift.up A))) =
    ((ULift.up A : liftedMatrix.{v} m n) :
      OnePoint (liftedMatrix.{v} m n))
  change core.1.symm
      ((ULift.up A : liftedMatrix.{v} m n) :
        OnePoint (liftedMatrix.{v} m n)) = _
  exact (core.2 (core.1.symm
    ((ULift.up A : liftedMatrix.{v} m n) :
      OnePoint (liftedMatrix.{v} m n)))).symm.trans
        (core.1.apply_symm_apply _)

/-- Sphere infinity is absorbing for every orthogonal action parameter. -/
theorem orthogonalSphereAction_infty (m n : OrthogonalIndex)
    (a : (OrthogonalIndex.hom.{u, v} m n).right) :
    (orthogonalSphereAction.{u, v} m n).right
        ((CategoryTheory.Pointed.smashPresentation
          CGWH.point CGWH.point_isTerminal
          (OrthogonalIndex.hom.{u, v} m n)
          (orthogonalSphere.{u, v} m)).2.1.inl
            (Classical.choose
              ((CGWH.prodComparisonToTop_bijective
                (OrthogonalIndex.hom.{u, v} m n).right
                (orthogonalSphere.{u, v} m).right).2
                  (a, OnePoint.infty)))) =
      OnePoint.infty := by
  let H := OrthogonalIndex.hom.{u, v} m n
  let K := liftedMatrix.{v} m n
  let E := liftedEuclidean.{v} m
  let _ : CompactSpace K := inferInstance
  let _ : T2Space K := inferInstance
  let _ : LocallyCompactSpace K := inferInstance
  let _ : BraidedCategory CGWH.{u, v} :=
    BraidedCategory.ofCartesianMonoidalCategory
  let _ : SymmetricCategory CGWH.{u, v} := inferInstance
  let I := homToOnePointIso.{u, v} m n
  let hK := compactMatrixOnePointGenerated.{u, v} m n
  let hE := euclideanOnePointGenerated.{u, v} m
  let μ := onePointProdSmashIso.{u, v} K E hK hE
  let f : C(K × E, liftedEuclidean.{v} n) :=
    ⟨liftedEvaluation, liftedEvaluation_continuous⟩
  let F := onePointMapOfProper.{u, v} f
    (evaluationTendstoCoclosedCompact.{v} m n)
  let c := Classical.choose
    ((CGWH.prodComparisonToTop_bijective H.right
      (onePointOf.{u, v} E).right).2
      (a, OnePoint.infty))
  let c' := Classical.choose
    ((CGWH.prodComparisonToTop_bijective
      (onePointOf.{u, v} K).right (onePointOf.{u, v} E).right).2
        (I.hom.right a, OnePoint.infty))
  let q : H.right ⊗ (onePointOf.{u, v} E).right ⟶
      (H ⊗ onePointOf.{u, v} E).right :=
    (CategoryTheory.Pointed.smashPresentation
      CGWH.point CGWH.point_isTerminal H (onePointOf.{u, v} E)).2.1.inl
  let q' : (onePointOf.{u, v} K).right ⊗
      (onePointOf.{u, v} E).right ⟶
      (onePointOf.{u, v} K ⊗ onePointOf.{u, v} E).right :=
    (CategoryTheory.Pointed.smashPresentation
      CGWH.point CGWH.point_isTerminal (onePointOf.{u, v} K)
        (onePointOf.{u, v} E)).2.1.inl
  have hnat := ConcreteCategory.congr_hom
    (CategoryTheory.Pointed.smashQuotient_naturality
      CGWH.point CGWH.point_isTerminal I.hom
        (𝟙 (onePointOf.{u, v} E))) c
  change (I.hom ⊗ₘ 𝟙 (onePointOf.{u, v} E)).right (q c) =
    q' ((I.hom.right ⊗ₘ 𝟙 (onePointOf.{u, v} E).right) c) at hnat
  have hc : (I.hom.right ⊗ₘ
      𝟙 (onePointOf.{u, v} E).right) c = c' := by
    have hMap := nativeProductMap_choose
      (A := H.right) (B := (onePointOf.{u, v} E).right)
      (A' := (onePointOf.{u, v} K).right) (B' := (onePointOf.{u, v} E).right)
      I.hom.right (𝟙 (onePointOf.{u, v} E).right) a
      (show (onePointOf.{u, v} E).right from OnePoint.infty)
    change (I.hom.right ⊗ₘ 𝟙 (onePointOf.{u, v} E).right) c =
      Classical.choose ((CGWH.prodComparisonToTop_bijective
        (onePointOf.{u, v} K).right (onePointOf.{u, v} E).right).2
        (I.hom.right a, (𝟙 (onePointOf.{u, v} E).right)
          (show (onePointOf.{u, v} E).right from OnePoint.infty))) at hMap
    exact hMap.trans (by rfl)
  have hμRaw := onePointProdSmashIso_infty_right K E hK hE
    (I.hom.right a)
  have hμ : μ.hom.right OnePoint.infty = q' c' :=
    hμRaw.trans (congrArg q'
      (chosenNativeProduct_eq_tensorEquivProd
        (onePointOf.{u, v} K).right (onePointOf.{u, v} E).right
        (I.hom.right a) OnePoint.infty).symm)
  have hInv := ConcreteCategory.congr_hom
    (congrArg Under.Hom.right μ.hom_inv_id) OnePoint.infty
  simp only [Under.comp_right, Under.id_right] at hInv
  have hμInv : μ.inv.right (q' c') = OnePoint.infty := by
    calc
      _ = μ.inv.right (μ.hom.right OnePoint.infty) :=
        congrArg μ.inv.right hμ.symm
      _ = _ := hInv
  change F.right (μ.inv.right
      ((I.hom ⊗ₘ 𝟙 (onePointOf.{u, v} E)).right (q c))) =
    OnePoint.infty
  rw [hnat, hc, hμInv]
  exact onePointMapOfProper_infty.{u, v} f
    (evaluationTendstoCoclosedCompact.{v} m n)

/-- The basepoint of the enriched hom parameter is absorbing for the
orthogonal sphere action. -/
theorem orthogonalSphereAction_parameterBasepoint
    (m n : OrthogonalIndex)
    (z : OnePoint (ULift.{v, 0} (EuclideanSpace ℝ (Fin m)))) :
    (orthogonalSphereAction.{u, v} m n).right
        ((CategoryTheory.Pointed.smashPresentation
          CGWH.point CGWH.point_isTerminal
          (OrthogonalIndex.hom.{u, v} m n)
          (orthogonalSphere.{u, v} m)).2.1.inl
            (Classical.choose
              ((CGWH.prodComparisonToTop_bijective
                (OrthogonalIndex.hom.{u, v} m n).right
                (orthogonalSphere.{u, v} m).right).2
                  ((OrthogonalIndex.hom.{u, v} m n).hom PUnit.unit, z)))) =
      OnePoint.infty := by
  let H := OrthogonalIndex.hom.{u, v} m n
  let K := liftedMatrix.{v} m n
  let E := liftedEuclidean.{v} m
  let _ : CompactSpace K := inferInstance
  let _ : T2Space K := inferInstance
  let _ : LocallyCompactSpace K := inferInstance
  let _ : BraidedCategory CGWH.{u, v} :=
    BraidedCategory.ofCartesianMonoidalCategory
  let _ : SymmetricCategory CGWH.{u, v} := inferInstance
  let I := homToOnePointIso.{u, v} m n
  let hK := compactMatrixOnePointGenerated.{u, v} m n
  let hE := euclideanOnePointGenerated.{u, v} m
  let μ := onePointProdSmashIso.{u, v} K E hK hE
  let f : C(K × E, liftedEuclidean.{v} n) :=
    ⟨liftedEvaluation, liftedEvaluation_continuous⟩
  let F := onePointMapOfProper.{u, v} f
    (evaluationTendstoCoclosedCompact.{v} m n)
  have hbase : I.hom.right (H.hom PUnit.unit) = OnePoint.infty := by
    let unitPoint : CGWH.point.{u, v} := by
      change PUnit.{v + 1}
      exact PUnit.unit
    have h := ConcreteCategory.congr_hom (Under.w I.hom) unitPoint
    change I.hom.right (H.hom unitPoint) =
      (onePointOf.{u, v} K).hom unitPoint at h
    exact h
  let c := Classical.choose
    ((CGWH.prodComparisonToTop_bijective H.right
      (onePointOf.{u, v} E).right).2 (H.hom PUnit.unit, z))
  let c' := Classical.choose
    ((CGWH.prodComparisonToTop_bijective
      (onePointOf.{u, v} K).right (onePointOf.{u, v} E).right).2
        (OnePoint.infty, z))
  let q : H.right ⊗ (onePointOf.{u, v} E).right ⟶
      (H ⊗ onePointOf.{u, v} E).right :=
    (CategoryTheory.Pointed.smashPresentation
      CGWH.point CGWH.point_isTerminal H (onePointOf.{u, v} E)).2.1.inl
  let q' : (onePointOf.{u, v} K).right ⊗
      (onePointOf.{u, v} E).right ⟶
      (onePointOf.{u, v} K ⊗ onePointOf.{u, v} E).right :=
    (CategoryTheory.Pointed.smashPresentation
      CGWH.point CGWH.point_isTerminal (onePointOf.{u, v} K)
        (onePointOf.{u, v} E)).2.1.inl
  have hnat := ConcreteCategory.congr_hom
    (CategoryTheory.Pointed.smashQuotient_naturality
      CGWH.point CGWH.point_isTerminal I.hom
        (𝟙 (onePointOf.{u, v} E))) c
  change (I.hom ⊗ₘ 𝟙 (onePointOf.{u, v} E)).right (q c) =
    q' ((I.hom.right ⊗ₘ 𝟙 (onePointOf.{u, v} E).right) c) at hnat
  have hc : (I.hom.right ⊗ₘ
      𝟙 (onePointOf.{u, v} E).right) c = c' := by
    have hMap := nativeProductMap_choose
      (A := H.right) (B := (onePointOf.{u, v} E).right)
      (A' := (onePointOf.{u, v} K).right) (B' := (onePointOf.{u, v} E).right)
      I.hom.right (𝟙 (onePointOf.{u, v} E).right) (H.hom PUnit.unit)
      (show (onePointOf.{u, v} E).right from z)
    change (I.hom.right ⊗ₘ 𝟙 (onePointOf.{u, v} E).right) c =
      Classical.choose ((CGWH.prodComparisonToTop_bijective
        (onePointOf.{u, v} K).right (onePointOf.{u, v} E).right).2
        (I.hom.right (H.hom PUnit.unit),
          (𝟙 (onePointOf.{u, v} E).right)
            (show (onePointOf.{u, v} E).right from z))) at hMap
    have hId : (𝟙 (onePointOf.{u, v} E).right)
        (show (onePointOf.{u, v} E).right from z) = z := rfl
    exact hMap.trans (by rw [hbase, hId])
  have hμRaw := onePointProdSmashIso_infty_left K E hK hE z
  have hμ : μ.hom.right OnePoint.infty = q' c' :=
    hμRaw.trans (congrArg q'
      (chosenNativeProduct_eq_tensorEquivProd
        (onePointOf.{u, v} K).right (onePointOf.{u, v} E).right
        OnePoint.infty z).symm)
  have hInv := ConcreteCategory.congr_hom
    (congrArg Under.Hom.right μ.hom_inv_id) OnePoint.infty
  simp only [Under.comp_right, Under.id_right] at hInv
  have hμInv : μ.inv.right (q' c') = OnePoint.infty := by
    calc
      _ = μ.inv.right (μ.hom.right OnePoint.infty) :=
        congrArg μ.inv.right hμ.symm
      _ = _ := hInv
  change F.right (μ.inv.right
      ((I.hom ⊗ₘ 𝟙 (onePointOf.{u, v} E)).right (q c))) =
    OnePoint.infty
  rw [hnat, hc, hμInv]
  exact onePointMapOfProper_infty.{u, v} f
    (evaluationTendstoCoclosedCompact.{v} m n)

/-- On a matrix generator and a finite vector, the action is ordinary
matrix evaluation. -/
theorem orthogonalSphereAction_coe
    {m n : OrthogonalIndex} (A : OrthogonalMatrixHom m n)
    (x : EuclideanSpace ℝ (Fin m)) :
    let t : (𝟙_ PointedCGWH.{u, v}).right :=
      (coprod.inr : CGWH.point.{u, v} ⟶
        CGWH.point.{u, v} ⨿ CGWH.point.{u, v}) PUnit.unit
    let pA := (OrthogonalIndex.matrixPoint.{u, v} A).right t
    (orthogonalSphereAction.{u, v} m n).right
        ((CategoryTheory.Pointed.smashPresentation
          CGWH.point CGWH.point_isTerminal
          (OrthogonalIndex.hom.{u, v} m n)
          (orthogonalSphere.{u, v} m)).2.1.inl
            (Classical.choose
              ((CGWH.prodComparisonToTop_bijective
                (OrthogonalIndex.hom.{u, v} m n).right
                (orthogonalSphere.{u, v} m).right).2
                  (pA,
                    ((ULift.up x : ULift.{v, 0}
                      (EuclideanSpace ℝ (Fin m))) :
                        OnePoint (ULift.{v, 0}
                          (EuclideanSpace ℝ (Fin m)))))))) =
      ((ULift.up ((EuclideanSpace.equiv (Fin n) ℝ).symm
          (A.1 *ᵥ x.ofLp)) :
            ULift.{v, 0} (EuclideanSpace ℝ (Fin n))) :
        OnePoint (ULift.{v, 0} (EuclideanSpace ℝ (Fin n)))) := by
  dsimp only
  let H := OrthogonalIndex.hom.{u, v} m n
  let K := liftedMatrix.{v} m n
  let E := liftedEuclidean.{v} m
  let _ : CompactSpace K := inferInstance
  let _ : T2Space K := inferInstance
  let _ : LocallyCompactSpace K := inferInstance
  let _ : BraidedCategory CGWH.{u, v} :=
    BraidedCategory.ofCartesianMonoidalCategory
  let _ : SymmetricCategory CGWH.{u, v} := inferInstance
  let I := homToOnePointIso.{u, v} m n
  let hK := compactMatrixOnePointGenerated.{u, v} m n
  let hE := euclideanOnePointGenerated.{u, v} m
  let μ := onePointProdSmashIso.{u, v} K E hK hE
  let f : C(K × E, liftedEuclidean.{v} n) :=
    ⟨liftedEvaluation, liftedEvaluation_continuous⟩
  let F := onePointMapOfProper.{u, v} f
    (evaluationTendstoCoclosedCompact.{v} m n)
  let t : (𝟙_ PointedCGWH.{u, v}).right :=
    (coprod.inr : CGWH.point.{u, v} ⟶
      CGWH.point.{u, v} ⨿ CGWH.point.{u, v}) PUnit.unit
  let pA := (OrthogonalIndex.matrixPoint.{u, v} A).right t
  have hmatrix : I.hom.right pA =
      ((ULift.up A : K) : OnePoint K) :=
    homToOnePointIso_matrixPoint.{u, v} A
  let x' : E := ULift.up x
  let c := Classical.choose
    ((CGWH.prodComparisonToTop_bijective H.right
      (onePointOf.{u, v} E).right).2 (pA, (x' : OnePoint E)))
  let c' := Classical.choose
    ((CGWH.prodComparisonToTop_bijective
      (onePointOf.{u, v} K).right (onePointOf.{u, v} E).right).2
        (I.hom.right pA, (x' : OnePoint E)))
  let q : H.right ⊗ (onePointOf.{u, v} E).right ⟶
      (H ⊗ onePointOf.{u, v} E).right :=
    (CategoryTheory.Pointed.smashPresentation
      CGWH.point CGWH.point_isTerminal H (onePointOf.{u, v} E)).2.1.inl
  let q' : (onePointOf.{u, v} K).right ⊗
      (onePointOf.{u, v} E).right ⟶
      (onePointOf.{u, v} K ⊗ onePointOf.{u, v} E).right :=
    (CategoryTheory.Pointed.smashPresentation
      CGWH.point CGWH.point_isTerminal (onePointOf.{u, v} K)
        (onePointOf.{u, v} E)).2.1.inl
  have hnat := ConcreteCategory.congr_hom
    (CategoryTheory.Pointed.smashQuotient_naturality
      CGWH.point CGWH.point_isTerminal I.hom
        (𝟙 (onePointOf.{u, v} E))) c
  change (I.hom ⊗ₘ 𝟙 (onePointOf.{u, v} E)).right (q c) =
    q' ((I.hom.right ⊗ₘ 𝟙 (onePointOf.{u, v} E).right) c) at hnat
  have hc : (I.hom.right ⊗ₘ
      𝟙 (onePointOf.{u, v} E).right) c = c' := by
    have hMap := nativeProductMap_choose
      (A := H.right) (B := (onePointOf.{u, v} E).right)
      (A' := (onePointOf.{u, v} K).right) (B' := (onePointOf.{u, v} E).right)
      I.hom.right (𝟙 (onePointOf.{u, v} E).right) pA
      (show (onePointOf.{u, v} E).right from (x' : OnePoint E))
    change (I.hom.right ⊗ₘ 𝟙 (onePointOf.{u, v} E).right) c =
      Classical.choose ((CGWH.prodComparisonToTop_bijective
        (onePointOf.{u, v} K).right (onePointOf.{u, v} E).right).2
        (I.hom.right pA, (𝟙 (onePointOf.{u, v} E).right)
          (show (onePointOf.{u, v} E).right from (x' : OnePoint E)))) at hMap
    exact hMap.trans (by rfl)
  have hμ := onePointProdSmashIso_coe K E hK hE
    (ULift.up A) x'
  have hcExact : c' = Classical.choose
      ((CGWH.prodComparisonToTop_bijective
        (onePointOf.{u, v} K).right (onePointOf.{u, v} E).right).2
          (((ULift.up A : K) : OnePoint K), (x' : OnePoint E))) := by
    dsimp only [c']
    rw [hmatrix]
  have hq : q' c' = μ.hom.right
      (((ULift.up A : K), x') : OnePoint (K × E)) := by
    calc
      q' c' = q' (Classical.choose
          ((CGWH.prodComparisonToTop_bijective
            (onePointOf.{u, v} K).right
            (onePointOf.{u, v} E).right).2
              (((ULift.up A : K) : OnePoint K), (x' : OnePoint E)))) :=
        congrArg q' hcExact
      _ = q' ((CGWH.tensorEquivProd
          (onePointOf.{u, v} K).right
          (onePointOf.{u, v} E).right).symm
            (((ULift.up A : K) : OnePoint K), (x' : OnePoint E))) :=
        congrArg q' (chosenNativeProduct_eq_tensorEquivProd
          (onePointOf.{u, v} K).right (onePointOf.{u, v} E).right
          ((ULift.up A : K) : OnePoint K) (x' : OnePoint E))
      _ = μ.hom.right
          (((ULift.up A : K), x') : OnePoint (K × E)) := hμ.symm
  have hInv := ConcreteCategory.congr_hom
    (congrArg Under.Hom.right μ.hom_inv_id)
      (((ULift.up A : K), x') : OnePoint (K × E))
  simp only [Under.comp_right, Under.id_right] at hInv
  have hμInv : μ.inv.right (q' c') =
      (((ULift.up A : K), x') : OnePoint (K × E)) := by
    calc
      _ = μ.inv.right
          (μ.hom.right (((ULift.up A : K), x') : OnePoint (K × E))) :=
        congrArg μ.inv.right hq
      _ = _ := hInv
  change F.right (μ.inv.right
      ((I.hom ⊗ₘ 𝟙 (onePointOf.{u, v} E)).right (q c))) = _
  rw [hnat, hc, hμInv]
  rw [onePointMapOfProper_coe.{u, v}]
  rfl

private noncomputable def liftedCoordinateHomeomorph
    {a b : OrthogonalIndex} (e : Fin a ≃ Fin b) :
    liftedEuclidean.{v} a ≃ₜ liftedEuclidean.{v} b :=
  (Homeomorph.ulift (X := EuclideanSpace ℝ (Fin a))).trans <|
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e).toHomeomorph.trans <|
      (Homeomorph.ulift (X := EuclideanSpace ℝ (Fin b))).symm

/-- Splitting an ordered direct sum intertwines coordinate block swap with
the native smash braiding. -/
theorem orthogonalSphereTensorIso_blockSwap (m n : OrthogonalIndex) :
    let e : ULift.{v, 0} (EuclideanSpace ℝ (Fin (m + n))) ≃ₜ
        ULift.{v, 0} (EuclideanSpace ℝ (Fin (n + m))) :=
      (Homeomorph.ulift
        (X := EuclideanSpace ℝ (Fin (m + n)))).trans
        ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
          (finAddFlip : Fin (m + n) ≃ Fin (n + m))).toHomeomorph.trans
            (Homeomorph.ulift
              (X := EuclideanSpace ℝ (Fin (n + m)))).symm)
    let r := onePointHomeomorphOfHomeomorph.{u, v} e
    r.hom ≫ (orthogonalSphereTensorIso.{u, v} n m).hom =
      (orthogonalSphereTensorIso.{u, v} m n).hom ≫
        (β_ (orthogonalSphere.{u, v} m)
          (orthogonalSphere.{u, v} n)).hom := by
  dsimp only
  let A := liftedEuclidean.{v} m
  let B := liftedEuclidean.{v} n
  let fAB := liftedFinAddHomeomorph.{v} m n
  let fBA := liftedFinAddHomeomorph.{v} n m
  let r := liftedCoordinateHomeomorph.{v}
    (finAddFlip : Fin (m + n) ≃ Fin (n + m))
  let s := Homeomorph.prodComm A B
  have hRaw : r.trans fBA = fAB.trans s := by
    apply Homeomorph.ext
    intro z
    apply Prod.ext
    · apply ULift.ext
      apply WithLp.ofLp_injective
      funext i
      dsimp [r, fBA, fAB, s, liftedCoordinateHomeomorph,
        liftedFinAddHomeomorph, EuclideanSpace.finAddEquivProd,
        EuclideanSpace.sumEquivProd]
      simp only [PiLp.sumPiLpEquivProdLpPiLp_apply_ofLp,
        WithLp.prodContinuousLinearEquiv_apply]
      simp [LinearIsometryEquiv.piLpCongrLeft_apply,
        Equiv.piCongrLeft'_apply, finAddFlip]
    · apply ULift.ext
      apply WithLp.ofLp_injective
      funext i
      dsimp [r, fBA, fAB, s, liftedCoordinateHomeomorph,
        liftedFinAddHomeomorph, EuclideanSpace.finAddEquivProd,
        EuclideanSpace.sumEquivProd]
      simp only [PiLp.sumPiLpEquivProdLpPiLp_apply_ofLp,
        WithLp.prodContinuousLinearEquiv_apply]
      simp [LinearIsometryEquiv.piLpCongrLeft_apply,
        Equiv.piCongrLeft'_apply, finAddFlip]
  let R := onePointHomeomorphOfHomeomorph.{u, v} r
  let FBA := onePointHomeomorphOfHomeomorph.{u, v} fBA
  let FAB := onePointHomeomorphOfHomeomorph.{u, v} fAB
  let S := onePointHomeomorphOfHomeomorph.{u, v} s
  have imageOfHomeomorph
      {X Y : Type v} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
      [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
      (e : X ≃ₜ Y) (x : X) :
      (onePointHomeomorphOfHomeomorph.{u, v} e).hom.right
        (x : OnePoint X) = (e x : OnePoint Y) := by
    let f : C(X, Y) := ⟨e, e.continuous⟩
    have hf : Tendsto f (coclosedCompact X) (coclosedCompact Y) :=
      e.map_coclosedCompact.le
    have hData : (onePointHomeomorphOfHomeomorph.{u, v} e).hom =
        onePointMapOfProper.{u, v} f hf := rfl
    exact (congrArg (fun q => q.right (x : OnePoint X)) hData).trans
      (onePointMapOfProper_coe.{u, v} f hf x)
  have hCoord : R.hom ≫ FBA.hom = FAB.hom ≫ S.hom := by
    apply Under.UnderMorphism.ext
    apply ConcreteCategory.hom_ext
    intro z
    induction z using OnePoint.rec with
    | infty =>
        let t : CGWH.point.{u, v} := by
          change PUnit
          exact PUnit.unit
        have hl := ConcreteCategory.congr_hom (Under.w (R.hom ≫ FBA.hom)) t
        have hr := ConcreteCategory.congr_hom (Under.w (FAB.hom ≫ S.hom)) t
        rw [ConcreteCategory.comp_apply] at hl hr
        exact hl.trans hr.symm
    | coe x =>
        change FBA.hom.right (R.hom.right
            (x : OnePoint (liftedEuclidean.{v} (m + n)))) =
          S.hom.right (FAB.hom.right (x : OnePoint (liftedEuclidean.{v} (m + n))))
        rw [imageOfHomeomorph r x, imageOfHomeomorph fBA (r x),
          imageOfHomeomorph fAB x, imageOfHomeomorph s (fAB x)]
        exact congrArg ((↑) : B × A → OnePoint (B × A))
          (congrArg (fun h ↦ h x) hRaw)
  let hA := euclideanOnePointGenerated.{u, v} m
  let hB := euclideanOnePointGenerated.{u, v} n
  let μAB := onePointProdSmashIso.{u, v} A B hA hB
  let μBA := onePointProdSmashIso.{u, v} B A hB hA
  have hBraiding := onePointProdSmashIso_braiding.{u, v} A B hA hB
  change R.hom ≫ (FBA.hom ≫ μBA.hom) =
    (FAB.hom ≫ μAB.hom) ≫
      (β_ (onePointOf.{u, v} A) (onePointOf.{u, v} B)).hom
  rw [← Category.assoc, hCoord, Category.assoc]
  simp only [Category.assoc]
  rw [hBraiding]

/-- The direct-sum sphere splitting respects the literal coordinate
associator and the native smash associator. -/
theorem orthogonalSphereTensorIso_associativity
    (m n p : OrthogonalIndex) :
    let e : ULift.{v, 0} (EuclideanSpace ℝ (Fin ((m + n) + p))) ≃ₜ
        ULift.{v, 0} (EuclideanSpace ℝ (Fin (m + (n + p)))) :=
      (Homeomorph.ulift
        (X := EuclideanSpace ℝ (Fin ((m + n) + p)))).trans
        ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
          (finCongr (Nat.add_assoc m n p))).toHomeomorph.trans
            (Homeomorph.ulift
              (X := EuclideanSpace ℝ (Fin (m + (n + p))))).symm)
    let r := onePointHomeomorphOfHomeomorph.{u, v} e
    r.hom ≫ (orthogonalSphereTensorIso.{u, v} m (n + p)).hom ≫
        (𝟙 (orthogonalSphere.{u, v} m) ⊗ₘ
          (orthogonalSphereTensorIso.{u, v} n p).hom) =
      (orthogonalSphereTensorIso.{u, v} (m + n) p).hom ≫
        ((orthogonalSphereTensorIso.{u, v} m n).hom ⊗ₘ
          𝟙 (orthogonalSphere.{u, v} p)) ≫
        (α_ (orthogonalSphere.{u, v} m)
          (orthogonalSphere.{u, v} n)
          (orthogonalSphere.{u, v} p)).hom := by
  dsimp only
  let A := liftedEuclidean.{v} m
  let B := liftedEuclidean.{v} n
  let C := liftedEuclidean.{v} p
  let fAB := liftedFinAddHomeomorph.{v} m n
  let fBC := liftedFinAddHomeomorph.{v} n p
  let fAB_C := liftedFinAddHomeomorph.{v} (m + n) p
  let fA_BC := liftedFinAddHomeomorph.{v} m (n + p)
  let r := liftedCoordinateHomeomorph.{v}
    (finCongr (Nat.add_assoc m n p))
  let gL := Homeomorph.prodCongr (Homeomorph.refl A) fBC
  let gR := (Homeomorph.prodCongr fAB (Homeomorph.refl C)).trans
    (Homeomorph.prodAssoc A B C)
  have hRaw : r.trans (fA_BC.trans gL) = fAB_C.trans gR := by
    apply Homeomorph.ext
    intro z
    apply Prod.ext
    · apply ULift.ext
      apply WithLp.ofLp_injective
      funext i
      dsimp [r, fAB, fBC, fAB_C, fA_BC, gL, gR,
        liftedCoordinateHomeomorph, liftedFinAddHomeomorph,
        EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd]
      simp only [PiLp.sumPiLpEquivProdLpPiLp_apply_ofLp,
        WithLp.prodContinuousLinearEquiv_apply]
      simp only [Homeomorph.apply_symm_apply, LinearIsometryEquiv.piLpCongrLeft_apply,
        Equiv.piCongrLeft'_apply, Equiv.symm_symm, finSumFinEquiv_apply_left, finCongr_symm,
        finCongr_apply, Homeomorph.refl_apply, id_eq, finSumFinEquiv_apply_right, Prod.map_apply,
        Homeomorph.trans_apply, ContinuousLinearEquiv.coe_toHomeomorph,
        ContinuousLinearEquiv.trans_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
        WithLp.prodContinuousLinearEquiv_apply, PiLp.sumPiLpEquivProdLpPiLp_apply_ofLp,
        Homeomorph.coe_prodCongr]
      change z.down.ofLp ((finCongr (Nat.add_assoc m n p)).symm
          (Fin.castAdd (n + p) i)) =
        z.down.ofLp (Fin.castAdd p (Fin.castAdd n i))
      apply congrArg z.down.ofLp
      apply Fin.ext
      rfl
    · apply Prod.ext
      · apply ULift.ext
        apply WithLp.ofLp_injective
        funext i
        dsimp [r, fAB, fBC, fAB_C, fA_BC, gL, gR,
          liftedCoordinateHomeomorph, liftedFinAddHomeomorph,
          EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd]
        simp only [PiLp.sumPiLpEquivProdLpPiLp_apply_ofLp,
          WithLp.prodContinuousLinearEquiv_apply]
        simp only [Homeomorph.apply_symm_apply, LinearIsometryEquiv.piLpCongrLeft_apply,
          Equiv.piCongrLeft'_apply, Equiv.symm_symm, finSumFinEquiv_apply_right, finCongr_symm,
          finCongr_apply, finSumFinEquiv_apply_left, Homeomorph.refl_apply, Prod.map_apply,
          Homeomorph.trans_apply, ContinuousLinearEquiv.coe_toHomeomorph,
          ContinuousLinearEquiv.trans_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
          WithLp.prodContinuousLinearEquiv_apply, PiLp.sumPiLpEquivProdLpPiLp_apply_ofLp,
          Homeomorph.coe_prodCongr, id_eq]
        change z.down.ofLp ((finCongr (Nat.add_assoc m n p)).symm
            (Fin.natAdd m (Fin.castAdd p i))) =
          z.down.ofLp (Fin.castAdd p (Fin.natAdd m i))
        apply congrArg z.down.ofLp
        apply Fin.ext
        rfl
      · apply ULift.ext
        apply WithLp.ofLp_injective
        funext i
        dsimp [r, fAB, fBC, fAB_C, fA_BC, gL, gR,
          liftedCoordinateHomeomorph, liftedFinAddHomeomorph,
          EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd]
        simp only [PiLp.sumPiLpEquivProdLpPiLp_apply_ofLp,
          WithLp.prodContinuousLinearEquiv_apply]
        simp only [Homeomorph.apply_symm_apply, LinearIsometryEquiv.piLpCongrLeft_apply,
          Equiv.piCongrLeft'_apply, Equiv.symm_symm, finSumFinEquiv_apply_right, finCongr_symm,
          finCongr_apply, Homeomorph.refl_apply, finSumFinEquiv_apply_left, Prod.map_apply,
          Homeomorph.trans_apply, ContinuousLinearEquiv.coe_toHomeomorph,
          ContinuousLinearEquiv.trans_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
          WithLp.prodContinuousLinearEquiv_apply, PiLp.sumPiLpEquivProdLpPiLp_apply_ofLp,
          Homeomorph.coe_prodCongr, id_eq]
        change z.down.ofLp ((finCongr (Nat.add_assoc m n p)).symm
            (Fin.natAdd m (Fin.natAdd n i))) =
          z.down.ofLp (Fin.natAdd (m + n) i)
        apply congrArg z.down.ofLp
        apply Fin.ext
        simp only [finCongr_symm_apply_coe, Fin.val_natAdd]
        omega
  let rPoint := onePointHomeomorphOfHomeomorph.{u, v} r
  let fA_BCPoint := onePointHomeomorphOfHomeomorph.{u, v} fA_BC
  let fAB_CPoint := onePointHomeomorphOfHomeomorph.{u, v} fAB_C
  let gLPoint := onePointHomeomorphOfHomeomorph.{u, v} gL
  let gRPoint := onePointHomeomorphOfHomeomorph.{u, v} gR
  have imageOfHomeomorph
      {X Y : Type v} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
      [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
      (e : X ≃ₜ Y) (x : X) :
      (onePointHomeomorphOfHomeomorph.{u, v} e).hom.right
        (x : OnePoint X) = (e x : OnePoint Y) := by
    let f : C(X, Y) := ⟨e, e.continuous⟩
    have hf : Tendsto f (coclosedCompact X) (coclosedCompact Y) :=
      e.map_coclosedCompact.le
    have hData : (onePointHomeomorphOfHomeomorph.{u, v} e).hom =
        onePointMapOfProper.{u, v} f hf := rfl
    exact (congrArg (fun q => q.right (x : OnePoint X)) hData).trans
      (onePointMapOfProper_coe.{u, v} f hf x)
  have hCoord : rPoint.hom ≫ fA_BCPoint.hom ≫ gLPoint.hom =
      fAB_CPoint.hom ≫ gRPoint.hom := by
    apply Under.UnderMorphism.ext
    apply ConcreteCategory.hom_ext
    intro z
    induction z using OnePoint.rec with
    | infty =>
        let t : CGWH.point.{u, v} := by
          change PUnit
          exact PUnit.unit
        have hl := ConcreteCategory.congr_hom
          (Under.w (rPoint.hom ≫ fA_BCPoint.hom ≫ gLPoint.hom)) t
        have hr := ConcreteCategory.congr_hom
          (Under.w (fAB_CPoint.hom ≫ gRPoint.hom)) t
        rw [ConcreteCategory.comp_apply] at hl hr
        exact hl.trans hr.symm
    | coe x =>
        change gLPoint.hom.right (fA_BCPoint.hom.right
            (rPoint.hom.right (x : OnePoint (liftedEuclidean.{v} ((m + n) + p))))) =
          gRPoint.hom.right (fAB_CPoint.hom.right
            (x : OnePoint (liftedEuclidean.{v} ((m + n) + p))))
        rw [imageOfHomeomorph r x, imageOfHomeomorph fA_BC (r x),
          imageOfHomeomorph gL (fA_BC (r x)), imageOfHomeomorph fAB_C x,
          imageOfHomeomorph gR (fAB_C x)]
        exact congrArg ((↑) : A × (B × C) → OnePoint (A × (B × C)))
          (congrArg (fun h ↦ h x) hRaw)
  have onePointRefl (X : Type v) [TopologicalSpace X]
      [LocallyCompactSpace X] [T2Space X] :
      (onePointHomeomorphOfHomeomorph.{u, v}
        (Homeomorph.refl X)).hom = 𝟙 (onePointOf.{u, v} X) := by
    apply Under.UnderMorphism.ext
    apply ConcreteCategory.hom_ext
    intro z
    induction z using OnePoint.rec with
    | infty =>
        exact onePointMapOfProper_infty.{u, v}
          (⟨Homeomorph.refl X, continuous_id⟩ : C(X, X))
          (Homeomorph.refl X).map_coclosedCompact.le
    | coe x =>
        exact onePointMapOfProper_coe.{u, v}
          (⟨Homeomorph.refl X, continuous_id⟩ : C(X, X))
          (Homeomorph.refl X).map_coclosedCompact.le x
  let fABPoint := onePointHomeomorphOfHomeomorph.{u, v} fAB
  let fBCPoint := onePointHomeomorphOfHomeomorph.{u, v} fBC
  let gR1 := Homeomorph.prodCongr fAB (Homeomorph.refl C)
  let assoc := Homeomorph.prodAssoc A B C
  let gR1Point := onePointHomeomorphOfHomeomorph.{u, v} gR1
  let assocPoint := onePointHomeomorphOfHomeomorph.{u, v} assoc
  have hGR : gRPoint.hom = gR1Point.hom ≫ assocPoint.hom := by
    apply Under.UnderMorphism.ext
    apply ConcreteCategory.hom_ext
    intro z
    induction z using OnePoint.rec with
    | infty =>
        let t : CGWH.point.{u, v} := by
          change PUnit
          exact PUnit.unit
        have hl := ConcreteCategory.congr_hom (Under.w gRPoint.hom) t
        have hr := ConcreteCategory.congr_hom
          (Under.w (gR1Point.hom ≫ assocPoint.hom)) t
        exact hl.trans hr.symm
    | coe x =>
        change gRPoint.hom.right (x : OnePoint (liftedEuclidean.{v} (m + n) × C)) =
          assocPoint.hom.right (gR1Point.hom.right
            (x : OnePoint (liftedEuclidean.{v} (m + n) × C)))
        rw [imageOfHomeomorph gR x, imageOfHomeomorph gR1 x,
          imageOfHomeomorph assoc (gR1 x)]
        rfl
  let hA := euclideanOnePointGenerated.{u, v} m
  let hB := euclideanOnePointGenerated.{u, v} n
  let hC := euclideanOnePointGenerated.{u, v} p
  let hAB := euclideanProductOnePointGenerated.{u, v} m n
  let hBC := euclideanProductOnePointGenerated.{u, v} n p
  let μA_EBC := onePointProdSmashIso.{u, v} A
    (liftedEuclidean.{v} (n + p)) hA
      (euclideanOnePointGenerated.{u, v} (n + p))
  let μA_BC := onePointProdSmashIso.{u, v} A (B × C) hA hBC
  let μEAB_C := onePointProdSmashIso.{u, v}
    (liftedEuclidean.{v} (m + n)) C
      (euclideanOnePointGenerated.{u, v} (m + n)) hC
  let μAB_C := onePointProdSmashIso.{u, v} (A × B) C hAB hC
  let μAB := onePointProdSmashIso.{u, v} A B hA hB
  let μBC := onePointProdSmashIso.{u, v} B C hB hC
  let idA : C(A, A) := ⟨Homeomorph.refl A, continuous_id⟩
  let mapBC : C(liftedEuclidean.{v} (n + p), B × C) :=
    ⟨fBC, fBC.continuous⟩
  let hIdA := (Homeomorph.refl A).map_coclosedCompact.le
  let hMapBC := fBC.map_coclosedCompact.le
  let hProdL := gL.map_coclosedCompact.le
  have hNatL0 := onePointProdSmashIso_naturality.{u, v}
    idA mapBC hIdA hMapBC hProdL
      (euclideanOnePointGenerated.{u, v} m)
      (euclideanOnePointGenerated.{u, v} m)
      (euclideanOnePointGenerated.{u, v} (n + p)) hBC
  have hIdAPoint : onePointMapOfProper.{u, v} idA hIdA =
      𝟙 (onePointOf.{u, v} A) := by
    calc
      _ = (onePointHomeomorphOfHomeomorph.{u, v}
          (Homeomorph.refl A)).hom := rfl
      _ = _ := onePointRefl A
  have hMapBCPoint : onePointMapOfProper.{u, v} mapBC hMapBC =
      fBCPoint.hom := by rfl
  have hProdLPoint : onePointMapOfProper.{u, v}
      (idA.prodMap mapBC) hProdL = gLPoint.hom := by rfl
  have hNatL : gLPoint.hom ≫ μA_BC.hom =
      μA_EBC.hom ≫
        (𝟙 (onePointOf.{u, v} A) ⊗ₘ fBCPoint.hom) := by
    rw [hProdLPoint, hIdAPoint, hMapBCPoint] at hNatL0
    exact hNatL0
  let mapAB : C(liftedEuclidean.{v} (m + n), A × B) :=
    ⟨fAB, fAB.continuous⟩
  let idC : C(C, C) := ⟨Homeomorph.refl C, continuous_id⟩
  let hMapAB := fAB.map_coclosedCompact.le
  let hIdC := (Homeomorph.refl C).map_coclosedCompact.le
  let hProdR := gR1.map_coclosedCompact.le
  have hNatR0 := onePointProdSmashIso_naturality.{u, v}
    mapAB idC hMapAB hIdC hProdR
      (euclideanOnePointGenerated.{u, v} (m + n)) hAB hC hC
  have hMapABPoint : onePointMapOfProper.{u, v} mapAB hMapAB =
      fABPoint.hom := by rfl
  have hIdCPoint : onePointMapOfProper.{u, v} idC hIdC =
      𝟙 (onePointOf.{u, v} C) := by
    calc
      _ = (onePointHomeomorphOfHomeomorph.{u, v}
          (Homeomorph.refl C)).hom := rfl
      _ = _ := onePointRefl C
  have hProdRPoint : onePointMapOfProper.{u, v}
      (mapAB.prodMap idC) hProdR = gR1Point.hom := by rfl
  have hNatR : gR1Point.hom ≫ μAB_C.hom =
      μEAB_C.hom ≫
        (fABPoint.hom ⊗ₘ 𝟙 (onePointOf.{u, v} C)) := by
    rw [hProdRPoint, hMapABPoint, hIdCPoint] at hNatR0
    exact hNatR0
  have hAssoc := onePointProdSmashIso_associativity.{u, v}
    A B C hA hB hC hAB hBC
  have hTensorL :
      𝟙 (onePointOf.{u, v} A) ⊗ₘ
          (fBCPoint.hom ≫ μBC.hom) =
        (𝟙 (onePointOf.{u, v} A) ⊗ₘ fBCPoint.hom) ≫
          (𝟙 (onePointOf.{u, v} A) ⊗ₘ μBC.hom) := by
    calc
      _ = ((𝟙 (onePointOf.{u, v} A)) ≫
            (𝟙 (onePointOf.{u, v} A))) ⊗ₘ
          (fBCPoint.hom ≫ μBC.hom) := by
            rw [Category.id_comp]
      _ = _ := by rw [tensorHom_comp_tensorHom]
  have hTensorR :
      (fABPoint.hom ≫ μAB.hom) ⊗ₘ
          𝟙 (onePointOf.{u, v} C) =
        (fABPoint.hom ⊗ₘ 𝟙 (onePointOf.{u, v} C)) ≫
          (μAB.hom ⊗ₘ 𝟙 (onePointOf.{u, v} C)) := by
    calc
      _ = (fABPoint.hom ≫ μAB.hom) ⊗ₘ
          ((𝟙 (onePointOf.{u, v} C)) ≫
            (𝟙 (onePointOf.{u, v} C))) := by
              rw [Category.id_comp]
      _ = _ := by rw [tensorHom_comp_tensorHom]
  have hFinal :
      rPoint.hom ≫ (fA_BCPoint.hom ≫ μA_EBC.hom) ≫
          (𝟙 (onePointOf.{u, v} A) ⊗ₘ
            (fBCPoint.hom ≫ μBC.hom)) =
        (fAB_CPoint.hom ≫ μEAB_C.hom) ≫
          ((fABPoint.hom ≫ μAB.hom) ⊗ₘ
            𝟙 (onePointOf.{u, v} C)) ≫
          (α_ (onePointOf.{u, v} A) (onePointOf.{u, v} B)
            (onePointOf.{u, v} C)).hom := by
    rw [hTensorL, hTensorR]
    simp only [Category.assoc]
    slice_lhs 3 4 => rw [← hNatL]
    slice_lhs 1 3 => rw [hCoord]
    rw [hGR]
    simp only [Category.assoc]
    slice_lhs 3 5 => rw [hAssoc]
    slice_lhs 2 3 => rw [hNatR]
    simp only [Category.assoc]
    rfl
  exact hFinal

private theorem orthogonalSphereTensorIso_coe
    (m n : OrthogonalIndex) (x : liftedEuclidean.{v} (m + n)) :
    let e := liftedFinAddHomeomorph.{v} m n
    let A := orthogonalSphere.{u, v} m
    let B := orthogonalSphere.{u, v} n
    (orthogonalSphereTensorIso.{u, v} m n).hom.right
        (x : OnePoint (liftedEuclidean.{v} (m + n))) =
      (CategoryTheory.Pointed.smashPresentation
        CGWH.point CGWH.point_isTerminal A B).2.1.inl
        (Classical.choose
          ((CGWH.prodComparisonToTop_bijective A.right B.right).2
            (((e x).1 : OnePoint (liftedEuclidean.{v} m)),
              ((e x).2 : OnePoint (liftedEuclidean.{v} n))))) := by
  dsimp only
  let e := liftedFinAddHomeomorph.{v} m n
  let hM := euclideanOnePointGenerated.{u, v} m
  let hN := euclideanOnePointGenerated.{u, v} n
  let F := onePointHomeomorphOfHomeomorph.{u, v} e
  let μ := onePointProdSmashIso.{u, v}
    (liftedEuclidean.{v} m) (liftedEuclidean.{v} n) hM hN
  change μ.hom.right (F.hom.right (x : OnePoint (liftedEuclidean.{v} (m + n)))) = _
  have imageOfHomeomorph
      {X Y : Type v} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
      [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
      (e : X ≃ₜ Y) (x : X) :
      (onePointHomeomorphOfHomeomorph.{u, v} e).hom.right
        (x : OnePoint X) = (e x : OnePoint Y) := by
    let f : C(X, Y) := ⟨e, e.continuous⟩
    have hf : Tendsto f (coclosedCompact X) (coclosedCompact Y) :=
      e.map_coclosedCompact.le
    have hData : (onePointHomeomorphOfHomeomorph.{u, v} e).hom =
        onePointMapOfProper.{u, v} f hf := rfl
    exact (congrArg (fun q => q.right (x : OnePoint X)) hData).trans
      (onePointMapOfProper_coe.{u, v} f hf x)
  have hImage : F.hom.right (x : OnePoint (liftedEuclidean.{v} (m + n))) =
      (e x : OnePoint (liftedEuclidean.{v} m × liftedEuclidean.{v} n)) :=
    imageOfHomeomorph e x
  rw [hImage]
  exact (onePointProdSmashIso_coe _ _ hM hN (e x).1 (e x).2).trans
    (congrArg
      ((CategoryTheory.Pointed.smashPresentation
        CGWH.point CGWH.point_isTerminal
        (orthogonalSphere.{u, v} m) (orthogonalSphere.{u, v} n)).2.1.inl)
      (chosenNativeProduct_eq_tensorEquivProd
        (orthogonalSphere.{u, v} m).right
        (orthogonalSphere.{u, v} n).right
        ((e x).1 : OnePoint (liftedEuclidean.{v} m))
        ((e x).2 : OnePoint (liftedEuclidean.{v} n))).symm)

private theorem orthogonalSphere_zero_coe (x : liftedEuclidean.{v} 0) :
    orthogonalSphereZeroIso.{u, v}.hom.right
        (x : OnePoint (liftedEuclidean.{v} 0)) =
      (coprod.inr : CGWH.point.{u, v} ⟶
        CGWH.point.{u, v} ⨿ CGWH.point.{u, v})
          (sphereZeroCarrierHomeomorph.{u, v} x) := by
  let e := sphereZeroCarrierHomeomorph.{u, v}
  let _ : CompactSpace (CGWH.point.{u, v} : Type v) := by
    change CompactSpace PUnit
    infer_instance
  let _ : T2Space (CGWH.point.{u, v} : Type v) := by
    change T2Space PUnit
    infer_instance
  let F := onePointHomeomorphOfHomeomorph.{u, v} e
  let B := addBasepointIsoOnePointOfCompact CGWH.point.{u, v}
  let free := (coprod.inr : CGWH.point.{u, v} ⟶
    CGWH.point.{u, v} ⨿ CGWH.point.{u, v}) (e x)
  have hB : B.hom.right free =
      ((e x : CGWH.point.{u, v}) : OnePoint (CGWH.point.{u, v} : Type v)) :=
    PointedCGWH.compactFreePointIso_coe CGWH.point (e x)
  have hInv : B.inv.right
      ((e x : CGWH.point.{u, v}) : OnePoint (CGWH.point.{u, v} : Type v)) =
      free := by
    have hCancel := ConcreteCategory.congr_hom
      (congrArg Under.Hom.right B.hom_inv_id) free
    simp only [Under.comp_right, Under.id_right] at hCancel
    calc
      _ = B.inv.right (B.hom.right free) := congrArg B.inv.right hB.symm
      _ = _ := hCancel
  unfold orthogonalSphereZeroIso
  change B.inv.right (F.hom.right
      (x : OnePoint (liftedEuclidean.{v} 0))) = free
  have imageOfHomeomorph
      {X Y : Type v} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
      [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
      (e : X ≃ₜ Y) (x : X) :
      (onePointHomeomorphOfHomeomorph.{u, v} e).hom.right
        (x : OnePoint X) = (e x : OnePoint Y) := by
    let f : C(X, Y) := ⟨e, e.continuous⟩
    have hf : Tendsto f (coclosedCompact X) (coclosedCompact Y) :=
      e.map_coclosedCompact.le
    have hData : (onePointHomeomorphOfHomeomorph.{u, v} e).hom =
        onePointMapOfProper.{u, v} f hf := rfl
    exact (congrArg (fun q => q.right (x : OnePoint X)) hData).trans
      (onePointMapOfProper_coe.{u, v} f hf x)
  have hImage : F.hom.right (x : OnePoint (liftedEuclidean.{v} 0)) =
      (e x : OnePoint (CGWH.point.{u, v} : Type v)) := imageOfHomeomorph e x
  rw [hImage]
  exact hInv

/-- The tensor comparison sends a finite vector to its two coordinate blocks in the
native smash presentation. -/
theorem orthogonalSphereTensorIso_apply_coe
    (m n : OrthogonalIndex) (x : ULift.{v, 0} (EuclideanSpace ℝ (Fin (m + n)))) :
    let e := orthogonalSphereSplitHomeomorph.{v} m n
    let A := orthogonalSphere.{u, v} m
    let B := orthogonalSphere.{u, v} n
    (orthogonalSphereTensorIso.{u, v} m n).hom.right
        (x : OnePoint (ULift.{v, 0} (EuclideanSpace ℝ (Fin (m + n))))) =
      (CategoryTheory.Pointed.smashPresentation
        CGWH.point CGWH.point_isTerminal A B).2.1.inl
        (Classical.choose
          ((CGWH.prodComparisonToTop_bijective A.right B.right).2
            (((e x).1 : OnePoint (ULift.{v, 0} (EuclideanSpace ℝ (Fin m)))),
              ((e x).2 : OnePoint (ULift.{v, 0} (EuclideanSpace ℝ (Fin n))))))) :=
  orthogonalSphereTensorIso_coe m n x

/-- A finite degree-zero vector maps to the nonbasepoint summand of the native smash unit. -/
theorem orthogonalSphereZeroIso_apply_coe
    (x : ULift.{v, 0} (EuclideanSpace ℝ (Fin 0))) :
    orthogonalSphereZeroIso.{u, v}.hom.right
        (x : OnePoint (ULift.{v, 0} (EuclideanSpace ℝ (Fin 0)))) =
      (coprod.inr : CGWH.point.{u, v} ⟶
        CGWH.point.{u, v} ⨿ CGWH.point.{u, v}) PUnit.unit := by
  have h := orthogonalSphere_zero_coe.{u, v} x
  have hx : sphereZeroCarrierHomeomorph.{u, v} x = (PUnit.unit : CGWH.point.{u, v}) := by
    change (_ : PUnit) = PUnit.unit
    exact Subsingleton.elim _ _
  exact h.trans (congrArg (coprod.inr : CGWH.point.{u, v} ⟶
    CGWH.point.{u, v} ⨿ CGWH.point.{u, v}) hx)

theorem orthogonalSphereTensorIso_leftUnit (n : OrthogonalIndex) :
    let e : ULift.{v, 0} (EuclideanSpace ℝ (Fin (0 + n))) ≃ₜ
        ULift.{v, 0} (EuclideanSpace ℝ (Fin n)) :=
      (Homeomorph.ulift
        (X := EuclideanSpace ℝ (Fin (0 + n)))).trans
        ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
          (finCongr (Nat.zero_add n))).toHomeomorph.trans
            (Homeomorph.ulift
              (X := EuclideanSpace ℝ (Fin n))).symm)
    let r := onePointHomeomorphOfHomeomorph.{u, v} e
    r.hom = (orthogonalSphereTensorIso.{u, v} 0 n).hom ≫
      (orthogonalSphereZeroIso.{u, v}.hom ⊗ₘ
        𝟙 (orthogonalSphere.{u, v} n)) ≫
      (λ_ (orthogonalSphere.{u, v} n)).hom := by
  dsimp only
  let E0 := liftedEuclidean.{v} 0
  let E := liftedEuclidean.{v} n
  let f := liftedFinAddHomeomorph.{v} 0 n
  let r := liftedCoordinateHomeomorph.{v} (finCongr (Nat.zero_add n))
  let R := onePointHomeomorphOfHomeomorph.{u, v} r
  let D := orthogonalSphereTensorIso.{u, v} 0 n
  let Z := orthogonalSphereZeroIso.{u, v}
  let S0 := onePointOf.{u, v} E0
  let T := onePointOf.{u, v} E
  let _ : BraidedCategory CGWH.{u, v} :=
    BraidedCategory.ofCartesianMonoidalCategory
  let _ : SymmetricCategory CGWH.{u, v} := inferInstance
  apply Under.UnderMorphism.ext
  apply ConcreteCategory.hom_ext
  intro z
  induction z using OnePoint.rec with
  | infty =>
      let t : CGWH.point.{u, v} := by
        change PUnit
        exact PUnit.unit
      have hl := ConcreteCategory.congr_hom (Under.w R.hom) t
      have hr := ConcreteCategory.congr_hom
        (Under.w (D.hom ≫ (Z.hom ⊗ₘ 𝟙 T) ≫ (λ_ T).hom)) t
      exact hl.trans hr.symm
  | coe x =>
      have hRaw : r x = (f x).2 := by
        apply ULift.ext
        apply WithLp.ofLp_injective
        funext i
        dsimp [r, f, liftedCoordinateHomeomorph,
          liftedFinAddHomeomorph, EuclideanSpace.finAddEquivProd,
          EuclideanSpace.sumEquivProd]
        simp only [PiLp.sumPiLpEquivProdLpPiLp_apply_ofLp,
          WithLp.prodContinuousLinearEquiv_apply]
        simp only [LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply,
          Equiv.symm_symm, finSumFinEquiv_apply_right, Fin.natAdd_zero]
        change x.down.ofLp ((finCongr (Nat.zero_add n)).symm i) =
          x.down.ofLp (Fin.cast (Nat.zero_add n).symm i)
        apply congrArg x.down.ofLp
        apply Fin.ext
        rfl
      let x0 : E0 := (f x).1
      let y : E := (f x).2
      let yPoint : T.right := show T.right from (y : OnePoint E)
      let free : (𝟙_ PointedCGWH.{u, v}).right :=
        (coprod.inr : CGWH.point.{u, v} ⟶
          CGWH.point.{u, v} ⨿ CGWH.point.{u, v})
            (sphereZeroCarrierHomeomorph.{u, v} x0)
      let freeTop : (CGWH.cgwhToTop.obj
          (𝟙_ PointedCGWH.{u, v}).right : Type v) := free
      let yTop : (CGWH.cgwhToTop.obj T.right : Type v) := yPoint
      have hzero : Z.hom.right (x0 : OnePoint E0) = free :=
        orthogonalSphere_zero_coe.{u, v} x0
      let c := Classical.choose
        ((CGWH.prodComparisonToTop_bijective S0.right T.right).2
          ((x0 : OnePoint E0), yPoint))
      let c' := Classical.choose
        ((CGWH.prodComparisonToTop_bijective
          (𝟙_ PointedCGWH.{u, v}).right T.right).2
            (freeTop, yTop))
      let q : S0.right ⊗ T.right ⟶ (S0 ⊗ T).right :=
        (CategoryTheory.Pointed.smashPresentation
          CGWH.point CGWH.point_isTerminal S0 T).2.1.inl
      let q' : (𝟙_ PointedCGWH.{u, v}).right ⊗ T.right ⟶
          ((𝟙_ PointedCGWH.{u, v}) ⊗ T).right :=
        (CategoryTheory.Pointed.smashPresentation
          CGWH.point CGWH.point_isTerminal
          (𝟙_ PointedCGWH.{u, v}) T).2.1.inl
      have hDelta := orthogonalSphereTensorIso_coe.{u, v} 0 n x
      change D.hom.right (x : OnePoint (liftedEuclidean.{v} (0 + n))) =
        q c at hDelta
      have hnat := ConcreteCategory.congr_hom
        (CategoryTheory.Pointed.smashQuotient_naturality
          CGWH.point CGWH.point_isTerminal Z.hom (𝟙 T)) c
      change (Z.hom ⊗ₘ 𝟙 T).right (q c) =
        q' ((Z.hom.right ⊗ₘ 𝟙 T.right) c) at hnat
      have hc : (Z.hom.right ⊗ₘ 𝟙 T.right) c = c' := by
        have hMap := nativeProductMap_choose
          (A := S0.right) (B := T.right)
          (A' := (𝟙_ PointedCGWH.{u, v}).right) (B' := T.right)
          Z.hom.right (𝟙 T.right)
          (show S0.right from (x0 : OnePoint E0)) yPoint
        change (Z.hom.right ⊗ₘ 𝟙 T.right) c =
          Classical.choose ((CGWH.prodComparisonToTop_bijective
            (𝟙_ PointedCGWH.{u, v}).right T.right).2
            (Z.hom.right (show S0.right from (x0 : OnePoint E0)),
              (𝟙 T.right) yPoint)) at hMap
        have hId : (𝟙 T.right) yPoint = yPoint := rfl
        exact hMap.trans (by rw [hzero, hId])
      let P := CGWH.point.{u, v}
      let hP := CGWH.point_isTerminal.{u, v}
      let pIso := hP.uniqueUpToIso
        CartesianMonoidalCategory.isTerminalTensorUnit
      let freeMap : P ⟶ (𝟙_ PointedCGWH.{u, v}).right := coprod.inr
      let w0 := (λ_ T.right).inv yPoint
      let w1 := (pIso.inv ▷ T.right) w0
      let cStruct := (freeMap ▷ T.right) w1
      let cStruct' : (CGWH.cgwhToTop.obj
          ((𝟙_ PointedCGWH.{u, v}).right ⨯ T.right) : Type v) :=
        cStruct
      have hcStruct' : cStruct' = c' := by
        apply (CGWH.prodComparisonToTop_bijective
          (𝟙_ PointedCGWH.{u, v}).right T.right).1
        have hchoose : CGWH.prodComparisonToTop
            (𝟙_ PointedCGWH.{u, v}).right T.right c' =
            (freeTop, yTop) :=
          Classical.choose_spec
            ((CGWH.prodComparisonToTop_bijective
              (𝟙_ PointedCGWH.{u, v}).right T.right).2
                (freeTop, yTop))
        rw [hchoose]
        apply Prod.ext
        · have hfst := ConcreteCategory.congr_hom
            (CGWH.prodComparisonToTop_fst
              (𝟙_ PointedCGWH.{u, v}).right T.right) cStruct'
          rw [ConcreteCategory.comp_apply] at hfst
          change (ConcreteCategory.hom TopCat.prodFst
            (CGWH.prodComparisonToTop
              (𝟙_ PointedCGWH.{u, v}).right T.right cStruct')) = freeTop
          rw [hfst]
          change CartesianMonoidalCategory.fst
            (𝟙_ PointedCGWH.{u, v}).right T.right
              ((freeMap ⊗ₘ 𝟙 T.right) w1) = free
          have h1 := ConcreteCategory.congr_hom
            (CartesianMonoidalCategory.tensorHom_fst freeMap (𝟙 T.right))
              ((pIso.inv ⊗ₘ 𝟙 T.right) ((λ_ T.right).inv yPoint))
          have h0 := ConcreteCategory.congr_hom
            (CartesianMonoidalCategory.tensorHom_fst pIso.inv (𝟙 T.right))
              ((λ_ T.right).inv yPoint)
          have hu := ConcreteCategory.congr_hom
            (CartesianMonoidalCategory.leftUnitor_inv_fst T.right) yPoint
          simp only [ConcreteCategory.comp_apply] at h1 h0
          simp only [ConcreteCategory.comp_apply] at hu
          dsimp only [w1, w0]
          change CartesianMonoidalCategory.fst
            (𝟙_ PointedCGWH.{u, v}).right T.right
              ((freeMap ⊗ₘ 𝟙 T.right)
                ((pIso.inv ⊗ₘ 𝟙 T.right)
                  ((λ_ T.right).inv yPoint))) = free
          rw [h1]
          rw [h0]
          rw [hu]
          change (coprod.inr : P ⟶ P ⨿ P) _ = free
          congr 1
        · have hsnd := ConcreteCategory.congr_hom
            (CGWH.prodComparisonToTop_snd
              (𝟙_ PointedCGWH.{u, v}).right T.right) cStruct'
          rw [ConcreteCategory.comp_apply] at hsnd
          change (ConcreteCategory.hom TopCat.prodSnd
            (CGWH.prodComparisonToTop
              (𝟙_ PointedCGWH.{u, v}).right T.right cStruct')) = yTop
          rw [hsnd]
          change CartesianMonoidalCategory.snd
            (𝟙_ PointedCGWH.{u, v}).right T.right
              ((freeMap ⊗ₘ 𝟙 T.right) w1) = yPoint
          have h1 := ConcreteCategory.congr_hom
            (CartesianMonoidalCategory.tensorHom_snd freeMap (𝟙 T.right))
              ((pIso.inv ⊗ₘ 𝟙 T.right) ((λ_ T.right).inv yPoint))
          have h0 := ConcreteCategory.congr_hom
            (CartesianMonoidalCategory.tensorHom_snd pIso.inv (𝟙 T.right))
              ((λ_ T.right).inv yPoint)
          have hu := ConcreteCategory.congr_hom
            (CartesianMonoidalCategory.leftUnitor_inv_snd T.right) yPoint
          simp only [ConcreteCategory.comp_apply, Category.comp_id] at h1 h0 hu
          dsimp only [w1, w0]
          change CartesianMonoidalCategory.snd
            (𝟙_ PointedCGWH.{u, v}).right T.right
              ((freeMap ⊗ₘ 𝟙 T.right)
                ((pIso.inv ⊗ₘ 𝟙 T.right)
                  ((λ_ T.right).inv yPoint))) = yPoint
          rw [h1]
          rw [h0]
          rw [hu]
          rfl
      have hcStruct : cStruct = c' := hcStruct'
      have hFree := ConcreteCategory.congr_hom
        (CategoryTheory.Pointed.smashLeftUnitor_inv_free P hP T) yPoint
      have hFreeAt : (λ_ T).inv.right yPoint = q' cStruct := hFree
      have hq : q' c' = (λ_ T).inv.right yPoint := by
        rw [← hcStruct]
        exact hFreeAt.symm
      have hCancel := ConcreteCategory.congr_hom
        (congrArg Under.Hom.right (λ_ T).inv_hom_id) yPoint
      simp only [Under.comp_right, ConcreteCategory.comp_apply,
        Under.id_right, ConcreteCategory.id_apply] at hCancel
      change R.hom.right (x : OnePoint (liftedEuclidean.{v} (0 + n))) =
        (λ_ T).hom.right
          ((Z.hom ⊗ₘ 𝟙 T).right (D.hom.right
            (x : OnePoint (liftedEuclidean.{v} (0 + n)))))
      let fR : C(liftedEuclidean.{v} (0 + n), E) := ⟨r, r.continuous⟩
      have hfR : Tendsto fR (coclosedCompact (liftedEuclidean.{v} (0 + n)))
          (coclosedCompact E) := r.map_coclosedCompact.le
      have hImage : R.hom.right (x : OnePoint (liftedEuclidean.{v} (0 + n))) =
          (r x : OnePoint E) :=
        onePointMapOfProper_coe.{u, v} fR hfR x
      rw [hImage, hDelta, hnat, hc, hq, hCancel]
      exact congrArg ((↑) : E → OnePoint E) hRaw

theorem orthogonalSphereTensorIso_rightUnit (n : OrthogonalIndex) :
    let e : ULift.{v, 0} (EuclideanSpace ℝ (Fin (n + 0))) ≃ₜ
        ULift.{v, 0} (EuclideanSpace ℝ (Fin n)) :=
      (Homeomorph.ulift
        (X := EuclideanSpace ℝ (Fin (n + 0)))).trans
        ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
          (finCongr (Nat.add_zero n))).toHomeomorph.trans
            (Homeomorph.ulift
              (X := EuclideanSpace ℝ (Fin n))).symm)
    let r := onePointHomeomorphOfHomeomorph.{u, v} e
    r.hom = (orthogonalSphereTensorIso.{u, v} n 0).hom ≫
      (𝟙 (orthogonalSphere.{u, v} n) ⊗ₘ
        orthogonalSphereZeroIso.{u, v}.hom) ≫
      (ρ_ (orthogonalSphere.{u, v} n)).hom := by
  dsimp only
  let E := liftedEuclidean.{v} n
  let rRight := liftedCoordinateHomeomorph.{v} (finCongr (Nat.add_zero n))
  let rSwap := liftedCoordinateHomeomorph.{v}
    (finAddFlip : Fin (n + 0) ≃ Fin (0 + n))
  let rLeft := liftedCoordinateHomeomorph.{v} (finCongr (Nat.zero_add n))
  have hRaw : rRight = rSwap.trans rLeft := by
    apply Homeomorph.ext
    intro z
    apply ULift.ext
    apply WithLp.ofLp_injective
    funext i
    dsimp [rRight, rSwap, rLeft, liftedCoordinateHomeomorph]
    simp only [finCongr_refl, Homeomorph.apply_symm_apply]
    change z.down.ofLp ((finCongr (Nat.add_zero n)).symm i) =
      z.down.ofLp ((finAddFlip : Fin (n + 0) ≃ Fin (0 + n)).symm
        ((finCongr (Nat.zero_add n)).symm i))
    apply congrArg z.down.ofLp
    apply (finAddFlip : Fin (n + 0) ≃ Fin (0 + n)).injective
    rw [Equiv.apply_symm_apply]
    rw [show (finCongr (Nat.add_zero n)).symm i = Fin.castAdd 0 i by
      apply Fin.ext
      rfl]
    rw [finAddFlip_apply_castAdd]
    apply Fin.ext
    simp only [finCongr_symm_apply_coe, Fin.val_natAdd]
    omega
  let RRight := onePointHomeomorphOfHomeomorph.{u, v} rRight
  let RSwap := onePointHomeomorphOfHomeomorph.{u, v} rSwap
  let RLeft := onePointHomeomorphOfHomeomorph.{u, v} rLeft
  have imageOfHomeomorph
      {X Y : Type v} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
      [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
      (e : X ≃ₜ Y) (x : X) :
      (onePointHomeomorphOfHomeomorph.{u, v} e).hom.right
        (x : OnePoint X) = (e x : OnePoint Y) := by
    let f : C(X, Y) := ⟨e, e.continuous⟩
    have hf : Tendsto f (coclosedCompact X) (coclosedCompact Y) :=
      e.map_coclosedCompact.le
    have hData : (onePointHomeomorphOfHomeomorph.{u, v} e).hom =
        onePointMapOfProper.{u, v} f hf := rfl
    exact (congrArg (fun q => q.right (x : OnePoint X)) hData).trans
      (onePointMapOfProper_coe.{u, v} f hf x)
  have hPoint : RRight.hom = RSwap.hom ≫ RLeft.hom := by
    apply Under.UnderMorphism.ext
    apply ConcreteCategory.hom_ext
    intro z
    induction z using OnePoint.rec with
    | infty =>
        let t : CGWH.point.{u, v} := by
          change PUnit
          exact PUnit.unit
        have hl := ConcreteCategory.congr_hom (Under.w RRight.hom) t
        have hr := ConcreteCategory.congr_hom
          (Under.w (RSwap.hom ≫ RLeft.hom)) t
        exact hl.trans hr.symm
    | coe x =>
        change RRight.hom.right (x : OnePoint (liftedEuclidean.{v} (n + 0))) =
          RLeft.hom.right (RSwap.hom.right
            (x : OnePoint (liftedEuclidean.{v} (n + 0))))
        rw [imageOfHomeomorph rRight x, imageOfHomeomorph rSwap x,
          imageOfHomeomorph rLeft (rSwap x)]
        exact congrArg ((↑) : E → OnePoint E)
          (congrArg (fun h ↦ h x) hRaw)
  let S := orthogonalSphere.{u, v} n
  let Z := orthogonalSphereZeroIso.{u, v}
  let Dn0 := orthogonalSphereTensorIso.{u, v} n 0
  let D0n := orthogonalSphereTensorIso.{u, v} 0 n
  have hSwap := orthogonalSphereTensorIso_blockSwap.{u, v} n 0
  have hLeft := orthogonalSphereTensorIso_leftUnit.{u, v} n
  change RSwap.hom ≫ D0n.hom =
    Dn0.hom ≫ (β_ S (orthogonalSphere.{u, v} 0)).hom at hSwap
  change RLeft.hom = D0n.hom ≫ (Z.hom ⊗ₘ 𝟙 S) ≫
    (λ_ S).hom at hLeft
  change RRight.hom = Dn0.hom ≫ (𝟙 S ⊗ₘ Z.hom) ≫ (ρ_ S).hom
  have hStep : RRight.hom =
      (RSwap.hom ≫ D0n.hom) ≫ (Z.hom ⊗ₘ 𝟙 S) ≫ (λ_ S).hom := by
    exact hPoint.trans (congrArg (fun q => RSwap.hom ≫ q) hLeft)
  have hSwapStep :
      (RSwap.hom ≫ D0n.hom) ≫ (Z.hom ⊗ₘ 𝟙 S) ≫ (λ_ S).hom =
      (Dn0.hom ≫ (β_ S (orthogonalSphere.{u, v} 0)).hom) ≫
        (Z.hom ⊗ₘ 𝟙 S) ≫ (λ_ S).hom :=
    congrArg (fun q => q ≫ (Z.hom ⊗ₘ 𝟙 S) ≫ (λ_ S).hom) hSwap
  refine hStep.trans (hSwapStep.trans ?_)
  simp only [Category.assoc]
  rw [← BraidedCategory.braiding_naturality_assoc]
  exact congrArg (fun f ↦ Dn0.hom ≫ (𝟙 S ⊗ₘ Z.hom) ≫ f)
    (CategoryTheory.braiding_leftUnitor S)

private theorem action_identity (n : OrthogonalIndex) :
    (λ_ (orthogonalSphere.{u, v} n)).inv ≫
        (@eId PointedCGWH.{u, v} _ _ OrthogonalIndex
          (OrthogonalIndex.enrichedCategory.{u, v}) n ⊗ₘ
          𝟙 (orthogonalSphere.{u, v} n)) ≫
      orthogonalSphereAction.{u, v} n n =
    𝟙 (orthogonalSphere.{u, v} n) := by
  let _ : EnrichedCategory PointedCGWH.{u, v} OrthogonalIndex :=
    OrthogonalIndex.enrichedCategory.{u, v}
  have hIdentity : @eId PointedCGWH.{u, v} _ _ OrthogonalIndex
      (OrthogonalIndex.enrichedCategory.{u, v}) n =
    OrthogonalIndex.matrixPoint.{u, v} (OrthogonalMatrixHom.id n) :=
      OrthogonalIndex.enrichedCategory_id.{u, v} n
  rw [hIdentity]
  let _ : BraidedCategory CGWH.{u, v} :=
    BraidedCategory.ofCartesianMonoidalCategory
  let _ : SymmetricCategory CGWH.{u, v} := inferInstance
  apply Under.UnderMorphism.ext
  apply ConcreteCategory.hom_ext
  intro z
  induction z using OnePoint.rec with
  | infty =>
      let t : CGWH.point.{u, v} := by
        change PUnit
        exact PUnit.unit
      have hl := ConcreteCategory.congr_hom
        (Under.w ((λ_ (orthogonalSphere.{u, v} n)).inv ≫
          (OrthogonalIndex.matrixPoint.{u, v}
            (OrthogonalMatrixHom.id n) ⊗ₘ
              𝟙 (orthogonalSphere.{u, v} n)) ≫
          orthogonalSphereAction.{u, v} n n)) t
      have hr := ConcreteCategory.congr_hom
        (Under.w (𝟙 (orthogonalSphere.{u, v} n))) t
      exact hl.trans hr.symm
  | coe x =>
      rcases x with ⟨x⟩
      let P := CGWH.point.{u, v}
      let hP := CGWH.point_isTerminal.{u, v}
      let H := OrthogonalIndex.hom.{u, v} n n
      let S := orthogonalSphere.{u, v} n
      let a := OrthogonalIndex.matrixPoint.{u, v}
        (OrthogonalMatrixHom.id n)
      let t : (𝟙_ PointedCGWH.{u, v}).right :=
        (coprod.inr : P ⟶ P ⨿ P) PUnit.unit
      let pA : H.right := a.right t
      let y : S.right :=
        ((ULift.up x : liftedEuclidean.{v} n) :
          OnePoint (liftedEuclidean.{v} n))
      let cI := Classical.choose
        ((CGWH.prodComparisonToTop_bijective
          (𝟙_ PointedCGWH.{u, v}).right S.right).2 (t, y))
      let c := Classical.choose
        ((CGWH.prodComparisonToTop_bijective H.right S.right).2 (pA, y))
      let qI : (𝟙_ PointedCGWH.{u, v}).right ⊗ S.right ⟶
          ((𝟙_ PointedCGWH.{u, v}) ⊗ S).right :=
        (CategoryTheory.Pointed.smashPresentation P hP
          (𝟙_ PointedCGWH.{u, v}) S).2.1.inl
      let q : H.right ⊗ S.right ⟶ (H ⊗ S).right :=
        (CategoryTheory.Pointed.smashPresentation P hP H S).2.1.inl
      let pIso := hP.uniqueUpToIso
        CartesianMonoidalCategory.isTerminalTensorUnit
      let freeMap : P ⟶ (𝟙_ PointedCGWH.{u, v}).right := coprod.inr
      let w0 := (λ_ S.right).inv y
      let w1 := (pIso.inv ▷ S.right) w0
      let cStruct := (freeMap ▷ S.right) w1
      let cStruct' : (CGWH.cgwhToTop.obj
          ((𝟙_ PointedCGWH.{u, v}).right ⨯ S.right) : Type v) :=
        cStruct
      have hcStruct' : cStruct' = cI := by
        apply (CGWH.prodComparisonToTop_bijective
          (𝟙_ PointedCGWH.{u, v}).right S.right).1
        have hchoose : CGWH.prodComparisonToTop
            (𝟙_ PointedCGWH.{u, v}).right S.right cI = (t, y) :=
          Classical.choose_spec
            ((CGWH.prodComparisonToTop_bijective
              (𝟙_ PointedCGWH.{u, v}).right S.right).2 (t, y))
        rw [hchoose]
        apply Prod.ext
        · have hfst := ConcreteCategory.congr_hom
            (CGWH.prodComparisonToTop_fst
              (𝟙_ PointedCGWH.{u, v}).right S.right) cStruct'
          rw [ConcreteCategory.comp_apply] at hfst
          change (ConcreteCategory.hom TopCat.prodFst
            (CGWH.prodComparisonToTop
              (𝟙_ PointedCGWH.{u, v}).right S.right cStruct')) = t
          rw [hfst]
          change CartesianMonoidalCategory.fst
            (𝟙_ PointedCGWH.{u, v}).right S.right
              ((freeMap ⊗ₘ 𝟙 S.right) w1) = t
          have h1 := ConcreteCategory.congr_hom
            (CartesianMonoidalCategory.tensorHom_fst freeMap (𝟙 S.right))
              ((pIso.inv ⊗ₘ 𝟙 S.right) ((λ_ S.right).inv y))
          have h0 := ConcreteCategory.congr_hom
            (CartesianMonoidalCategory.tensorHom_fst pIso.inv (𝟙 S.right))
              ((λ_ S.right).inv y)
          have hu := ConcreteCategory.congr_hom
            (CartesianMonoidalCategory.leftUnitor_inv_fst S.right) y
          simp only [ConcreteCategory.comp_apply] at h1 h0 hu
          dsimp only [w1, w0]
          change CartesianMonoidalCategory.fst
            (𝟙_ PointedCGWH.{u, v}).right S.right
              ((freeMap ⊗ₘ 𝟙 S.right)
                ((pIso.inv ⊗ₘ 𝟙 S.right) ((λ_ S.right).inv y))) = t
          rw [h1, h0, hu]
          rfl
        · have hsnd := ConcreteCategory.congr_hom
            (CGWH.prodComparisonToTop_snd
              (𝟙_ PointedCGWH.{u, v}).right S.right) cStruct'
          rw [ConcreteCategory.comp_apply] at hsnd
          change (ConcreteCategory.hom TopCat.prodSnd
            (CGWH.prodComparisonToTop
              (𝟙_ PointedCGWH.{u, v}).right S.right cStruct')) = y
          rw [hsnd]
          change CartesianMonoidalCategory.snd
            (𝟙_ PointedCGWH.{u, v}).right S.right
              ((freeMap ⊗ₘ 𝟙 S.right) w1) = y
          have h1 := ConcreteCategory.congr_hom
            (CartesianMonoidalCategory.tensorHom_snd freeMap (𝟙 S.right))
              ((pIso.inv ⊗ₘ 𝟙 S.right) ((λ_ S.right).inv y))
          have h0 := ConcreteCategory.congr_hom
            (CartesianMonoidalCategory.tensorHom_snd pIso.inv (𝟙 S.right))
              ((λ_ S.right).inv y)
          have hu := ConcreteCategory.congr_hom
            (CartesianMonoidalCategory.leftUnitor_inv_snd S.right) y
          simp only [ConcreteCategory.comp_apply, Category.comp_id] at h1 h0 hu
          dsimp only [w1, w0]
          change CartesianMonoidalCategory.snd
            (𝟙_ PointedCGWH.{u, v}).right S.right
              ((freeMap ⊗ₘ 𝟙 S.right)
                ((pIso.inv ⊗ₘ 𝟙 S.right) ((λ_ S.right).inv y))) = y
          rw [h1, h0, hu]
          rfl
      have hcStruct : cStruct = cI := hcStruct'
      have hFree := ConcreteCategory.congr_hom
        (CategoryTheory.Pointed.smashLeftUnitor_inv_free P hP S) y
      have hFreeAt : (λ_ S).inv.right y = qI cStruct := hFree
      have hqI : qI cI = (λ_ S).inv.right y := by
        rw [← hcStruct]
        exact hFreeAt.symm
      have hnat := ConcreteCategory.congr_hom
        (CategoryTheory.Pointed.smashQuotient_naturality P hP a (𝟙 S)) cI
      change (a ⊗ₘ 𝟙 S).right (qI cI) =
        q ((a.right ⊗ₘ 𝟙 S.right) cI) at hnat
      have hc : (a.right ⊗ₘ 𝟙 S.right) cI = c := by
        have hMap := nativeProductMap_choose
          (A := (𝟙_ PointedCGWH.{u, v}).right) (B := S.right)
          (A' := H.right) (B' := S.right) a.right (𝟙 S.right) t y
        change (a.right ⊗ₘ 𝟙 S.right) cI =
          Classical.choose ((CGWH.prodComparisonToTop_bijective H.right S.right).2
            (a.right t, (𝟙 S.right) y)) at hMap
        exact hMap.trans (by rfl)
      have hInput :
          ((λ_ S).inv ≫ (a ⊗ₘ 𝟙 S)).right y = q c := by
        simp only [Under.comp_right, ConcreteCategory.comp_apply]
        rw [← hqI, hnat, hc]
      simp only [Under.comp_right, Under.id_right]
      change (orthogonalSphereAction.{u, v} n n).right
        (((λ_ S).inv ≫ (a ⊗ₘ 𝟙 S)).right y) = y
      rw [hInput]
      have hAction := orthogonalSphereAction_coe.{u, v}
        (OrthogonalMatrixHom.id n) x
      change (orthogonalSphereAction.{u, v} n n).right (q c) =
        ((ULift.up ((EuclideanSpace.equiv (Fin n) ℝ).symm
          ((OrthogonalMatrixHom.id n).1 *ᵥ x.ofLp)) :
            liftedEuclidean.{v} n) : OnePoint (liftedEuclidean.{v} n))
        at hAction
      rw [hAction]
      change ((ULift.up ((EuclideanSpace.equiv (Fin n) ℝ).symm
          ((1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ x.ofLp)) :
            liftedEuclidean.{v} n) : OnePoint (liftedEuclidean.{v} n)) =
        ((ULift.up x : liftedEuclidean.{v} n) :
          OnePoint (liftedEuclidean.{v} n))
      simp

private theorem action_composition
    (m n p : OrthogonalIndex) :
    ((@eComp PointedCGWH.{u, v} _ _ OrthogonalIndex
          (OrthogonalIndex.enrichedCategory.{u, v}) m n p) ⊗ₘ
        𝟙 (orthogonalSphere.{u, v} m)) ≫
      orthogonalSphereAction.{u, v} m p =
    (α_ (OrthogonalIndex.hom.{u, v} m n)
      (OrthogonalIndex.hom.{u, v} n p)
      (orthogonalSphere.{u, v} m)).hom ≫
      (𝟙 (OrthogonalIndex.hom.{u, v} m n) ⊗ₘ
        (β_ (OrthogonalIndex.hom.{u, v} n p)
          (orthogonalSphere.{u, v} m)).hom) ≫
      (α_ (OrthogonalIndex.hom.{u, v} m n)
        (orthogonalSphere.{u, v} m)
        (OrthogonalIndex.hom.{u, v} n p)).inv ≫
      (orthogonalSphereAction.{u, v} m n ⊗ₘ
        𝟙 (OrthogonalIndex.hom.{u, v} n p)) ≫
      (β_ (orthogonalSphere.{u, v} n)
        (OrthogonalIndex.hom.{u, v} n p)).hom ≫
      orthogonalSphereAction.{u, v} n p := by
  let _ : EnrichedCategory PointedCGWH.{u, v} OrthogonalIndex :=
    OrthogonalIndex.enrichedCategory.{u, v}
  let _ : BraidedCategory CGWH.{u, v} :=
    BraidedCategory.ofCartesianMonoidalCategory
  let _ : SymmetricCategory CGWH.{u, v} := inferInstance
  let Hmn := OrthogonalIndex.hom.{u, v} m n
  let Hnp := OrthogonalIndex.hom.{u, v} n p
  let Hmp := OrthogonalIndex.hom.{u, v} m p
  let Sm := orthogonalSphere.{u, v} m
  let Sn := orthogonalSphere.{u, v} n
  let q (X Y : PointedCGWH.{u, v}) :
      X.right ⊗ Y.right ⟶ (X ⊗ Y).right :=
    (CategoryTheory.Pointed.smashPresentation
      CGWH.point CGWH.point_isTerminal X Y).2.1.inl
  have pointTensor_free {X Y : PointedCGWH.{u, v}}
      (f : 𝟙_ PointedCGWH.{u, v} ⟶ X)
      (g : 𝟙_ PointedCGWH.{u, v} ⟶ Y) :
      let t : (𝟙_ PointedCGWH.{u, v}).right :=
        (coprod.inr : CGWH.point.{u, v} ⟶
          CGWH.point.{u, v} ⨿ CGWH.point.{u, v}) PUnit.unit
      let c := Classical.choose
        ((CGWH.prodComparisonToTop_bijective X.right Y.right).2
          (f.right t, g.right t))
      ((λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫ (f ⊗ₘ g)).right t =
        q X Y c := by
    dsimp only
    let P := CGWH.point.{u, v}
    let hP := CGWH.point_isTerminal.{u, v}
    let I := 𝟙_ PointedCGWH.{u, v}
    let unitPoint : P := by
      change PUnit.{v + 1}
      exact PUnit.unit
    let t : I.right :=
      (coprod.inr : P ⟶ P ⨿ P) unitPoint
    let cI := Classical.choose
      ((CGWH.prodComparisonToTop_bijective I.right I.right).2 (t, t))
    let c := Classical.choose
      ((CGWH.prodComparisonToTop_bijective X.right Y.right).2
        (f.right t, g.right t))
    let qI : I.right ⊗ I.right ⟶ (I ⊗ I).right :=
      (CategoryTheory.Pointed.smashPresentation P hP I I).2.1.inl
    let pIso := hP.uniqueUpToIso
      CartesianMonoidalCategory.isTerminalTensorUnit
    let freeMap : P ⟶ I.right := coprod.inr
    let w0 := (λ_ I.right).inv t
    let w1 := (pIso.inv ▷ I.right) w0
    let cStruct := (freeMap ▷ I.right) w1
    let cStruct' : (CGWH.cgwhToTop.obj (I.right ⨯ I.right) : Type v) :=
      cStruct
    have hcStruct' : cStruct' = cI := by
      apply (CGWH.prodComparisonToTop_bijective I.right I.right).1
      have hchoose : CGWH.prodComparisonToTop I.right I.right cI =
          (t, t) :=
        Classical.choose_spec
          ((CGWH.prodComparisonToTop_bijective I.right I.right).2 (t, t))
      rw [hchoose]
      apply Prod.ext
      · have hfst := ConcreteCategory.congr_hom
          (CGWH.prodComparisonToTop_fst I.right I.right) cStruct'
        rw [ConcreteCategory.comp_apply] at hfst
        change (ConcreteCategory.hom TopCat.prodFst
          (CGWH.prodComparisonToTop I.right I.right cStruct')) = t
        rw [hfst]
        change CartesianMonoidalCategory.fst I.right I.right
            ((freeMap ⊗ₘ 𝟙 I.right) w1) = t
        have h1 := ConcreteCategory.congr_hom
          (CartesianMonoidalCategory.tensorHom_fst freeMap (𝟙 I.right))
            ((pIso.inv ⊗ₘ 𝟙 I.right) ((λ_ I.right).inv t))
        have h0 := ConcreteCategory.congr_hom
          (CartesianMonoidalCategory.tensorHom_fst pIso.inv (𝟙 I.right))
            ((λ_ I.right).inv t)
        have hu := ConcreteCategory.congr_hom
          (CartesianMonoidalCategory.leftUnitor_inv_fst I.right) t
        simp only [ConcreteCategory.comp_apply] at h1 h0 hu
        dsimp only [w1, w0]
        change CartesianMonoidalCategory.fst I.right I.right
            ((freeMap ⊗ₘ 𝟙 I.right)
              ((pIso.inv ⊗ₘ 𝟙 I.right) ((λ_ I.right).inv t))) = t
        rw [h1, h0, hu]
        rfl
      · have hsnd := ConcreteCategory.congr_hom
          (CGWH.prodComparisonToTop_snd I.right I.right) cStruct'
        rw [ConcreteCategory.comp_apply] at hsnd
        change (ConcreteCategory.hom TopCat.prodSnd
          (CGWH.prodComparisonToTop I.right I.right cStruct')) = t
        rw [hsnd]
        change CartesianMonoidalCategory.snd I.right I.right
            ((freeMap ⊗ₘ 𝟙 I.right) w1) = t
        have h1 := ConcreteCategory.congr_hom
          (CartesianMonoidalCategory.tensorHom_snd freeMap (𝟙 I.right))
            ((pIso.inv ⊗ₘ 𝟙 I.right) ((λ_ I.right).inv t))
        have h0 := ConcreteCategory.congr_hom
          (CartesianMonoidalCategory.tensorHom_snd pIso.inv (𝟙 I.right))
            ((λ_ I.right).inv t)
        have hu := ConcreteCategory.congr_hom
          (CartesianMonoidalCategory.leftUnitor_inv_snd I.right) t
        simp only [ConcreteCategory.comp_apply, Category.comp_id] at h1 h0 hu
        dsimp only [w1, w0]
        change CartesianMonoidalCategory.snd I.right I.right
            ((freeMap ⊗ₘ 𝟙 I.right)
              ((pIso.inv ⊗ₘ 𝟙 I.right) ((λ_ I.right).inv t))) = t
        rw [h1, h0, hu]
        rfl
    have hcStruct : cStruct = cI := hcStruct'
    have hFree := ConcreteCategory.congr_hom
      (CategoryTheory.Pointed.smashLeftUnitor_inv_free P hP I) t
    have hFreeAt : (λ_ I).inv.right t = qI cStruct := hFree
    have hqI : qI cI = (λ_ I).inv.right t := by
      rw [← hcStruct]
      exact hFreeAt.symm
    have hnat := ConcreteCategory.congr_hom
      (CategoryTheory.Pointed.smashQuotient_naturality P hP f g) cI
    change (f ⊗ₘ g).right (qI cI) =
      q X Y ((f.right ⊗ₘ g.right) cI) at hnat
    have hc : (f.right ⊗ₘ g.right) cI = c := by
      exact nativeProductMap_choose f.right g.right t t
    change (f ⊗ₘ g).right ((λ_ I).inv.right t) = _
    exact (congrArg (fun x => (f ⊗ₘ g).right x) hqI.symm).trans
      (hnat.trans (congrArg (q X Y) hc))
  have epi_right_of_isPushout_of_splitEpi
      {A B X Y : CGWH.{u, v}} {t : A ⟶ B} {l : A ⟶ X}
      {r : B ⟶ Y} {b : X ⟶ Y}
      (h : IsPushout t l r b) (s : X ⟶ A)
      (hs : s ≫ l = 𝟙 X) : Epi r := by
    constructor
    intro Z f g hr
    apply h.hom_ext
    · exact hr
    · calc
        b ≫ f = (𝟙 X) ≫ b ≫ f := by simp
        _ = (s ≫ l) ≫ b ≫ f := by rw [hs]
        _ = s ≫ (l ≫ b) ≫ f := by simp only [Category.assoc]
        _ = s ≫ (t ≫ r) ≫ f := by rw [h.w]
        _ = s ≫ t ≫ (r ≫ f) := by simp only [Category.assoc]
        _ = s ≫ t ≫ (r ≫ g) := by rw [hr]
        _ = s ≫ (t ≫ r) ≫ g := by simp only [Category.assoc]
        _ = s ≫ (l ≫ b) ≫ g := by rw [h.w]
        _ = (s ≫ l) ≫ b ≫ g := by simp only [Category.assoc]
        _ = b ≫ g := by rw [hs]; simp
  have map_isPushout_of_preserves
      {A B X Y : CGWH.{u, v}} {t : A ⟶ B} {l : A ⟶ X}
      {r : B ⟶ Y} {b : X ⟶ Y}
      (F : CGWH.{u, v} ⥤ CGWH.{u, v})
      [PreservesColimit (span t l) F]
      (h : IsPushout t l r b) :
      IsPushout (F.map t) (F.map l) (F.map r) (F.map b) :=
    IsPushout.of_isColimit_cocone
      (PreservesColimit.preserves h.isColimit).some
  have map_epi_right_of_isPushout_of_splitEpi
      {A B X Y : CGWH.{u, v}} {t : A ⟶ B} {l : A ⟶ X}
      {r : B ⟶ Y} {b : X ⟶ Y}
      (F : CGWH.{u, v} ⥤ CGWH.{u, v})
      [PreservesColimit (span t l) F]
      (h : IsPushout t l r b) (s : X ⟶ A)
      (hs : s ≫ l = 𝟙 X) : Epi (F.map r) := by
    apply epi_right_of_isPushout_of_splitEpi
      (map_isPushout_of_preserves F h) (F.map s)
    rw [← F.map_comp, hs, F.map_id]
  have q_epi (X Y : PointedCGWH.{u, v}) : Epi (q X Y) := by
    let W := ((CategoryTheory.Pointed.wedge CGWH.point).obj X).obj Y
    let c : W.right ⟶ CGWH.point.{u, v} :=
      CGWH.point_isTerminal.from W.right
    have hs : W.hom ≫ c = 𝟙 CGWH.point.{u, v} :=
      CGWH.point_isTerminal.hom_ext _ _
    exact epi_right_of_isPushout_of_splitEpi
      (IsPushout.of_isColimit_cocone
        (CategoryTheory.Pointed.smashPresentation
          CGWH.point CGWH.point_isTerminal X Y).2.2)
      W.hom hs
  have q_whisker_epi (X Y : PointedCGWH.{u, v})
      (T : CGWH.{u, v}) : Epi (q X Y ▷ T) := by
    let W := ((CategoryTheory.Pointed.wedge CGWH.point).obj X).obj Y
    let c : W.right ⟶ CGWH.point.{u, v} :=
      CGWH.point_isTerminal.from W.right
    have hs : W.hom ≫ c = 𝟙 CGWH.point.{u, v} :=
      CGWH.point_isTerminal.hom_ext _ _
    exact map_epi_right_of_isPushout_of_splitEpi (tensorRight T)
      (IsPushout.of_isColimit_cocone
        (CategoryTheory.Pointed.smashPresentation
          CGWH.point CGWH.point_isTerminal X Y).2.2)
      W.hom hs
  let _ : Epi (q Hmn Hnp ▷ Sm.right) :=
    q_whisker_epi Hmn Hnp Sm.right
  let _ : Epi (q (Hmn ⊗ Hnp) Sm) :=
    q_epi (Hmn ⊗ Hnp) Sm
  apply Under.UnderMorphism.ext
  apply (cancel_epi ((q Hmn Hnp ▷ Sm.right) ≫
    q (Hmn ⊗ Hnp) Sm)).1
  let nativeComp : Hmn ⊗ Hnp ⟶ Hmp :=
    @eComp PointedCGWH.{u, v} _ _ OrthogonalIndex
      (OrthogonalIndex.enrichedCategory.{u, v}) m n p
  let leftMap : (Hmn ⊗ Hnp) ⊗ Sm ⟶ orthogonalSphere.{u, v} p :=
    (nativeComp ⊗ₘ 𝟙 Sm) ≫ orthogonalSphereAction.{u, v} m p
  let rightMap : (Hmn ⊗ Hnp) ⊗ Sm ⟶ orthogonalSphere.{u, v} p :=
    (α_ Hmn Hnp Sm).hom ≫
      (𝟙 Hmn ⊗ₘ (β_ Hnp Sm).hom) ≫
      (α_ Hmn Sm Hnp).inv ≫
      (orthogonalSphereAction.{u, v} m n ⊗ₘ 𝟙 Hnp) ≫
      (β_ Sn Hnp).hom ≫ orthogonalSphereAction.{u, v} n p
  change ((q Hmn Hnp ▷ Sm.right) ≫ q (Hmn ⊗ Hnp) Sm) ≫ leftMap.right =
    ((q Hmn Hnp ▷ Sm.right) ≫ q (Hmn ⊗ Hnp) Sm) ≫ rightMap.right
  change (q Hmn Hnp ▷ Sm.right) ≫ q (Hmn ⊗ Hnp) Sm ≫
      (nativeComp ⊗ₘ 𝟙 Sm).right ≫ (orthogonalSphereAction.{u, v} m p).right =
    (q Hmn Hnp ▷ Sm.right) ≫ q (Hmn ⊗ Hnp) Sm ≫
      (α_ Hmn Hnp Sm).hom.right ≫
      (𝟙 Hmn ⊗ₘ (β_ Hnp Sm).hom).right ≫
      (α_ Hmn Sm Hnp).inv.right ≫
      (orthogonalSphereAction.{u, v} m n ⊗ₘ 𝟙 Hnp).right ≫
      (β_ Sn Hnp).hom.right ≫ (orthogonalSphereAction.{u, v} n p).right
  have hQuot : q (Hmn ⊗ Hnp) Sm ≫
      (nativeComp ⊗ₘ 𝟙 Sm).right =
    (nativeComp.right ⊗ₘ 𝟙 Sm.right) ≫ q Hmp Sm :=
    CategoryTheory.Pointed.smashQuotient_naturality
      CGWH.point.{u, v} CGWH.point_isTerminal nativeComp (𝟙 Sm)
  slice_lhs 2 3 => rw [hQuot]
  have hAssoc :=
    CategoryTheory.Pointed.smashAssociator_hom_quotient
      CGWH.point.{u, v} CGWH.point_isTerminal Hmn Hnp Sm
  change ((q Hmn Hnp ▷ Sm.right) ≫ q (Hmn ⊗ Hnp) Sm) ≫
      (α_ (OrthogonalIndex.hom.{u, v} m n)
        (OrthogonalIndex.hom.{u, v} n p)
        (orthogonalSphere.{u, v} m)).hom.right =
    (α_ Hmn.right Hnp.right Sm.right).hom ≫
      (Hmn.right ◁ q Hnp Sm) ≫ q Hmn (Hnp ⊗ Sm) at hAssoc
  slice_rhs 1 3 =>
    rw [← Category.assoc, hAssoc]
  simp only [Category.assoc]
  have hQuotBraid : q Hmn (Hnp ⊗ Sm) ≫
      (𝟙 Hmn ⊗ₘ (β_ Hnp Sm).hom).right =
    (𝟙 Hmn.right ⊗ₘ (β_ Hnp Sm).hom.right) ≫ q Hmn (Sm ⊗ Hnp) :=
    CategoryTheory.Pointed.smashQuotient_naturality
      CGWH.point.{u, v} CGWH.point_isTerminal (𝟙 Hmn) (β_ Hnp Sm).hom
  slice_rhs 3 4 => rw [hQuotBraid]
  have hTensorBraid₁ :
      𝟙 (Hmn.right) ⊗ₘ
          (β_ (OrthogonalIndex.hom.{u, v} n p)
            (orthogonalSphere.{u, v} m)).hom.right =
        Hmn.right ◁
          (β_ (OrthogonalIndex.hom.{u, v} n p)
            (orthogonalSphere.{u, v} m)).hom.right := by
    change (𝟙 Hmn.right) ⊗ₘ (β_ Hnp Sm).hom.right =
      Hmn.right ◁ (β_ Hnp Sm).hom.right
    exact MonoidalCategory.id_tensorHom _ _
  rw [hTensorBraid₁]
  have hBraid₁ := smashQuotient_braiding_hom Hnp Sm
  change q Hnp Sm ≫
      (β_ (OrthogonalIndex.hom.{u, v} n p)
        (orthogonalSphere.{u, v} m)).hom.right =
    CartesianMonoidalCategory.lift
        (CartesianMonoidalCategory.snd Hnp.right Sm.right)
        (CartesianMonoidalCategory.fst Hnp.right Sm.right) ≫
      q Sm Hnp at hBraid₁
  slice_rhs 2 3 =>
    rw [← MonoidalCategory.whiskerLeft_comp, hBraid₁,
      MonoidalCategory.whiskerLeft_comp]
  simp only [Category.assoc]
  have hAssocInv :=
    CategoryTheory.Pointed.smashAssociator_inv_quotient
      CGWH.point.{u, v} CGWH.point_isTerminal Hmn Sm Hnp
  change ((Hmn.right ◁ q Sm Hnp) ≫ q Hmn (Sm ⊗ Hnp)) ≫
      (α_ (OrthogonalIndex.hom.{u, v} m n)
        (orthogonalSphere.{u, v} m)
        (OrthogonalIndex.hom.{u, v} n p)).inv.right =
    (α_ Hmn.right Sm.right Hnp.right).inv ≫
      (q Hmn Sm ▷ Hnp.right) ≫ q (Hmn ⊗ Sm) Hnp at hAssocInv
  slice_rhs 3 5 =>
    rw [← Category.assoc, hAssocInv]
  simp only [Category.assoc]
  have hQuotAct : q (Hmn ⊗ Sm) Hnp ≫
      (orthogonalSphereAction.{u, v} m n ⊗ₘ 𝟙 Hnp).right =
    ((orthogonalSphereAction.{u, v} m n).right ⊗ₘ 𝟙 Hnp.right) ≫ q Sn Hnp :=
    CategoryTheory.Pointed.smashQuotient_naturality
      CGWH.point.{u, v} CGWH.point_isTerminal
      (orthogonalSphereAction.{u, v} m n) (𝟙 Hnp)
  slice_rhs 5 6 => rw [hQuotAct]
  have hBraid₂ := smashQuotient_braiding_hom Sn Hnp
  change q Sn Hnp ≫
      (β_ (orthogonalSphere.{u, v} n)
        (OrthogonalIndex.hom.{u, v} n p)).hom.right =
    CartesianMonoidalCategory.lift
        (CartesianMonoidalCategory.snd Sn.right Hnp.right)
        (CartesianMonoidalCategory.fst Sn.right Hnp.right) ≫
      q Hnp Sn at hBraid₂
  slice_rhs 6 7 =>
    rw [hBraid₂]
  apply ConcreteCategory.hom_ext
  intro z
  let AB : CGWH.{u, v} := Hmn.right ⊗ Hnp.right
  let zAB : AB := CartesianMonoidalCategory.fst AB Sm.right z
  let x : Sm.right := CartesianMonoidalCategory.snd AB Sm.right z
  let a : Hmn.right :=
    CartesianMonoidalCategory.fst Hmn.right Hnp.right zAB
  let b : Hnp.right :=
    CartesianMonoidalCategory.snd Hmn.right Hnp.right zAB
  let cAB : (Hmn.right ⊗ Hnp.right : CGWH.{u, v}) := Classical.choose
    ((CGWH.prodComparisonToTop_bijective Hmn.right Hnp.right).2 (a, b))
  have hzAB : zAB = cAB := by
    apply (CGWH.prodComparisonToTop_bijective Hmn.right Hnp.right).1
    have hcAB : CGWH.prodComparisonToTop Hmn.right Hnp.right cAB =
        (a, b) :=
      Classical.choose_spec
        ((CGWH.prodComparisonToTop_bijective Hmn.right Hnp.right).2 (a, b))
    rw [hcAB]
    apply Prod.ext
    · have hf := ConcreteCategory.congr_hom
        (CGWH.prodComparisonToTop_fst Hmn.right Hnp.right) zAB
      change (CGWH.prodComparisonToTop Hmn.right Hnp.right zAB).1 =
        CartesianMonoidalCategory.fst Hmn.right Hnp.right zAB at hf
      exact hf
    · have hs := ConcreteCategory.congr_hom
        (CGWH.prodComparisonToTop_snd Hmn.right Hnp.right) zAB
      change (CGWH.prodComparisonToTop Hmn.right Hnp.right zAB).2 =
        CartesianMonoidalCategory.snd Hmn.right Hnp.right zAB at hs
      exact hs
  let cOuter : (AB ⊗ Sm.right : CGWH.{u, v}) := Classical.choose
    ((CGWH.prodComparisonToTop_bijective AB Sm.right).2 (cAB, x))
  have hz : z = cOuter := by
    apply (CGWH.prodComparisonToTop_bijective AB Sm.right).1
    have hcOuter : CGWH.prodComparisonToTop AB Sm.right cOuter =
        (cAB, x) :=
      Classical.choose_spec
        ((CGWH.prodComparisonToTop_bijective AB Sm.right).2 (cAB, x))
    rw [hcOuter]
    apply Prod.ext
    · have hf := ConcreteCategory.congr_hom
        (CGWH.prodComparisonToTop_fst AB Sm.right) z
      change (CGWH.prodComparisonToTop AB Sm.right z).1 =
        CartesianMonoidalCategory.fst AB Sm.right z at hf
      exact hf.trans hzAB
    · have hs := ConcreteCategory.congr_hom
        (CGWH.prodComparisonToTop_snd AB Sm.right) z
      change (CGWH.prodComparisonToTop AB Sm.right z).2 =
        CartesianMonoidalCategory.snd AB Sm.right z at hs
      exact hs
  let unitPoint : CGWH.point.{u, v} := by
    change PUnit.{v + 1}
    exact PUnit.unit
  let t : (𝟙_ PointedCGWH.{u, v}).right :=
    (coprod.inr : CGWH.point.{u, v} ⟶
      CGWH.point.{u, v} ⨿ CGWH.point.{u, v}) unitPoint
  have preservesBase {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
      f.right (X.hom unitPoint) = Y.hom unitPoint := by
    have h := ConcreteCategory.congr_hom (Under.w f) unitPoint
    change f.right (X.hom unitPoint) = Y.hom unitPoint at h
    exact h
  have zero_free (X : PointedCGWH.{u, v}) :
      (0 : 𝟙_ PointedCGWH.{u, v} ⟶ X).right t =
        X.hom PUnit.unit := by
    let pointZero : PointedCGWH.{u, v} :=
      Under.mk (𝟙 CGWH.point.{u, v})
    have pointZeroIsZero : IsZero pointZero :=
      { unique_to := fun T ↦
          ⟨{ default := Under.mkIdInitial.to T
             uniq := fun g ↦ Under.mkIdInitial.hom_ext g _ }⟩
        unique_from := fun T ↦
          ⟨{ default := Under.homMk
                (CGWH.point_isTerminal.from T.right)
                (CGWH.point_isTerminal.hom_ext _ _)
             uniq := fun g ↦ Under.UnderMorphism.ext
               (CGWH.point_isTerminal.hom_ext g.right _) }⟩ }
    let zeroPointedIso : (0 : PointedCGWH.{u, v}) ≅ pointZero :=
      (isZero_zero PointedCGWH.{u, v}).iso pointZeroIsZero
    let zeroRightIso :
        (0 : PointedCGWH.{u, v}).right ≅ CGWH.point.{u, v} :=
      { hom := zeroPointedIso.hom.right
        inv := zeroPointedIso.inv.right
        hom_inv_id := congrArg (fun g ↦ g.right)
          zeroPointedIso.hom_inv_id
        inv_hom_id := congrArg (fun g ↦ g.right)
          zeroPointedIso.inv_hom_id }
    have zeroRightIsTerminal : IsTerminal
        ((0 : PointedCGWH.{u, v}).right) :=
      IsTerminal.ofIso CGWH.point_isTerminal zeroRightIso.symm
    let freeGenerator : CGWH.point.{u, v} ⟶
        (𝟙_ PointedCGWH.{u, v}).right := coprod.inr
    have hzero : freeGenerator ≫
          (0 : 𝟙_ PointedCGWH.{u, v} ⟶ X).right = X.hom := by
      change freeGenerator ≫
          ((default : 𝟙_ PointedCGWH.{u, v} ⟶
            (0 : PointedCGWH.{u, v})).right ≫
          (default : (0 : PointedCGWH.{u, v}) ⟶ X).right) = _
      rw [← Category.assoc]
      have hfirst : freeGenerator ≫
          (default : 𝟙_ PointedCGWH.{u, v} ⟶
            (0 : PointedCGWH.{u, v})).right =
          (0 : PointedCGWH.{u, v}).hom :=
        zeroRightIsTerminal.hom_ext _ _
      rw [hfirst]
      exact Under.w (default : (0 : PointedCGWH.{u, v}) ⟶ X)
    have h := ConcreteCategory.congr_hom hzero unitPoint
    change (0 : 𝟙_ PointedCGWH.{u, v} ⟶ X).right t = X.hom unitPoint at h
    exact h
  let pointMap (X : PointedCGWH.{u, v}) (x : X.right) :
      𝟙_ PointedCGWH.{u, v} ⟶ X :=
    Under.homMk
      (coprod.desc X.hom ((CGWH.pointHomEquiv X.right).symm x))
      (by
        have hunit : (𝟙_ PointedCGWH.{u, v}).hom =
            (coprod.inl : CGWH.point.{u, v} ⟶
              CGWH.point.{u, v} ⨿ CGWH.point.{u, v}) := by
          change ((Under.costar CGWH.point.{u, v}).obj CGWH.point.{u, v}).hom = _
          exact (Under.costar_obj_hom CGWH.point CGWH.point).trans (coprod.inl_desc _ _)
        exact (congrArg (fun h => h ≫
          coprod.desc X.hom ((CGWH.pointHomEquiv X.right).symm x)) hunit).trans
            (coprod.inl_desc _ _))
  have pointMap_free (X : PointedCGWH.{u, v}) (x : X.right) :
      (pointMap X x).right t = x := by
    let f : CGWH.point.{u, v} ⟶ X.right := (CGWH.pointHomEquiv X.right).symm x
    have hDesc : (coprod.inr : CGWH.point.{u, v} ⟶
        CGWH.point.{u, v} ⨿ CGWH.point.{u, v}) ≫ coprod.desc X.hom f = f :=
      coprod.inr_desc _ _
    have h := ConcreteCategory.congr_hom hDesc unitPoint
    change (pointMap X x).right t = f unitPoint at h
    exact h.trans (CGWH.pointHomEquiv_symm_apply_apply X.right x unitPoint)
  have q_left_base (X Y : PointedCGWH.{u, v}) (y : Y.right) :
      let c := Classical.choose
        ((CGWH.prodComparisonToTop_bijective X.right Y.right).2
          (X.hom PUnit.unit, y))
      q X Y c = (X ⊗ Y).hom PUnit.unit := by
    dsimp only
    let py := pointMap Y y
    let c₀ := Classical.choose
      ((CGWH.prodComparisonToTop_bijective X.right Y.right).2
        ((0 : 𝟙_ PointedCGWH.{u, v} ⟶ X).right t, py.right t))
    let c := Classical.choose
      ((CGWH.prodComparisonToTop_bijective X.right Y.right).2
        (X.hom PUnit.unit, y))
    have hc : c₀ = c := by
      dsimp only [c₀, c]
      rw [zero_free X, pointMap_free]
    have hp := pointTensor_free
      (0 : 𝟙_ PointedCGWH.{u, v} ⟶ X) py
    change ((λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫
        ((0 : 𝟙_ PointedCGWH.{u, v} ⟶ X) ⊗ₘ py)).right t =
      q X Y c₀ at hp
    have hz :
        (λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫
            ((0 : 𝟙_ PointedCGWH.{u, v} ⟶ X) ⊗ₘ py) =
          (0 : 𝟙_ PointedCGWH.{u, v} ⟶ X ⊗ Y) := by
      have ht :
          ((0 : 𝟙_ PointedCGWH.{u, v} ⟶ X) ⊗ₘ py) = 0 := by
        let _ : (tensorRight
            (𝟙_ PointedCGWH.{u, v})).PreservesZeroMorphisms :=
          inferInstance
        rw [MonoidalCategory.tensorHom_def]
        change (tensorRight (𝟙_ PointedCGWH.{u, v})).map 0 ≫ _ = 0
        rw [Functor.map_zero, zero_comp]
      rw [ht, comp_zero]
    have hze := ConcreteCategory.congr_hom
      (congrArg Under.Hom.right hz) t
    calc
      q X Y c = q X Y c₀ := congrArg (q X Y) hc.symm
      _ = ((λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫
          ((0 : 𝟙_ PointedCGWH.{u, v} ⟶ X) ⊗ₘ py)).right t :=
        hp.symm
      _ = (0 : 𝟙_ PointedCGWH.{u, v} ⟶ X ⊗ Y).right t := hze
      _ = (X ⊗ Y).hom PUnit.unit := zero_free (X ⊗ Y)
  have q_right_base (X Y : PointedCGWH.{u, v}) (x : X.right) :
      let c := Classical.choose
        ((CGWH.prodComparisonToTop_bijective X.right Y.right).2
          (x, Y.hom PUnit.unit))
      q X Y c = (X ⊗ Y).hom PUnit.unit := by
    dsimp only
    let px := pointMap X x
    let c₀ := Classical.choose
      ((CGWH.prodComparisonToTop_bijective X.right Y.right).2
        (px.right t, (0 : 𝟙_ PointedCGWH.{u, v} ⟶ Y).right t))
    let c := Classical.choose
      ((CGWH.prodComparisonToTop_bijective X.right Y.right).2
        (x, Y.hom PUnit.unit))
    have hc : c₀ = c := by
      dsimp only [c₀, c]
      rw [pointMap_free, zero_free Y]
    have hp := pointTensor_free px
      (0 : 𝟙_ PointedCGWH.{u, v} ⟶ Y)
    change ((λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫
        (px ⊗ₘ (0 : 𝟙_ PointedCGWH.{u, v} ⟶ Y))).right t =
      q X Y c₀ at hp
    have hz :
        (λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫
            (px ⊗ₘ (0 : 𝟙_ PointedCGWH.{u, v} ⟶ Y)) =
          (0 : 𝟙_ PointedCGWH.{u, v} ⟶ X ⊗ Y) := by
      have ht :
          (px ⊗ₘ (0 : 𝟙_ PointedCGWH.{u, v} ⟶ Y)) = 0 := by
        let _ : (tensorLeft
            (𝟙_ PointedCGWH.{u, v})).PreservesZeroMorphisms :=
          inferInstance
        rw [MonoidalCategory.tensorHom_def']
        change (tensorLeft (𝟙_ PointedCGWH.{u, v})).map 0 ≫ _ = 0
        rw [Functor.map_zero, zero_comp]
      rw [ht, comp_zero]
    have hze := ConcreteCategory.congr_hom
      (congrArg Under.Hom.right hz) t
    calc
      q X Y c = q X Y c₀ := congrArg (q X Y) hc.symm
      _ = ((λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫
          (px ⊗ₘ (0 : 𝟙_ PointedCGWH.{u, v} ⟶ Y))).right t :=
        hp.symm
      _ = (0 : 𝟙_ PointedCGWH.{u, v} ⟶ X ⊗ Y).right t := hze
      _ = (X ⊗ Y).hom PUnit.unit := zero_free (X ⊗ Y)
  have isoHom_injective {X Y : PointedCGWH.{u, v}} (e : X ≅ Y) :
      Function.Injective (ConcreteCategory.hom e.hom.right) := by
    intro x₁ x₂ h
    have h' := congrArg (ConcreteCategory.hom e.inv.right) h
    have h₁ := ConcreteCategory.congr_hom
      (congrArg Under.Hom.right e.hom_inv_id) x₁
    have h₂ := ConcreteCategory.congr_hom
      (congrArg Under.Hom.right e.hom_inv_id) x₂
    simp only [Under.comp_right, ConcreteCategory.comp_apply,
      Under.id_right, ConcreteCategory.id_apply] at h₁ h₂
    exact h₁.symm.trans (h'.trans h₂)
  have homPoint_cases (i j : OrthogonalIndex)
      (y : (OrthogonalIndex.hom.{u, v} i j).right) :
      y = (OrthogonalIndex.hom.{u, v} i j).hom PUnit.unit ∨
        ∃ A : OrthogonalMatrixHom i j,
          y = (OrthogonalIndex.matrixPoint.{u, v} A).right t := by
    let _ : CompactSpace (liftedMatrix.{v} i j) := inferInstance
    let _ : LocallyCompactSpace (liftedMatrix.{v} i j) := inferInstance
    let I := homToOnePointIso.{u, v} i j
    generalize hy : I.hom.right y = z'
    induction z' using OnePoint.rec with
    | infty =>
        left
        apply isoHom_injective I
        rw [hy]
        have hbase : I.hom.right
            ((OrthogonalIndex.hom.{u, v} i j).hom PUnit.unit) =
              OnePoint.infty := by
          have h := ConcreteCategory.congr_hom (Under.w I.hom) unitPoint
          change I.hom.right ((OrthogonalIndex.hom.{u, v} i j).hom unitPoint) =
            (onePointOf.{u, v} (liftedMatrix.{v} i j)).hom unitPoint at h
          exact h
        exact hbase.symm
    | coe y' =>
        rcases y' with ⟨A⟩
        right
        refine ⟨A, ?_⟩
        apply isoHom_injective I
        rw [hy]
        exact (homToOnePointIso_matrixPoint.{u, v} A).symm
  have hcAB_fst :
      CartesianMonoidalCategory.fst Hmn.right Hnp.right cAB = a := by
    have h := ConcreteCategory.congr_hom
      (CGWH.prodComparisonToTop_fst Hmn.right Hnp.right) cAB
    change (CGWH.prodComparisonToTop Hmn.right Hnp.right cAB).1 =
      CartesianMonoidalCategory.fst Hmn.right Hnp.right cAB at h
    have hc : CGWH.prodComparisonToTop Hmn.right Hnp.right cAB = (a, b) :=
      Classical.choose_spec
        ((CGWH.prodComparisonToTop_bijective Hmn.right Hnp.right).2 (a, b))
    exact h.symm.trans (congrArg Prod.fst hc)
  have hcAB_snd :
      CartesianMonoidalCategory.snd Hmn.right Hnp.right cAB = b := by
    have h := ConcreteCategory.congr_hom
      (CGWH.prodComparisonToTop_snd Hmn.right Hnp.right) cAB
    change (CGWH.prodComparisonToTop Hmn.right Hnp.right cAB).2 =
      CartesianMonoidalCategory.snd Hmn.right Hnp.right cAB at h
    have hc : CGWH.prodComparisonToTop Hmn.right Hnp.right cAB = (a, b) :=
      Classical.choose_spec
        ((CGWH.prodComparisonToTop_bijective Hmn.right Hnp.right).2 (a, b))
    exact h.symm.trans (congrArg Prod.snd hc)
  have hcOuter_fst :
      CartesianMonoidalCategory.fst AB Sm.right cOuter = cAB := by
    have h := ConcreteCategory.congr_hom
      (CGWH.prodComparisonToTop_fst AB Sm.right) cOuter
    change (CGWH.prodComparisonToTop AB Sm.right cOuter).1 =
      CartesianMonoidalCategory.fst AB Sm.right cOuter at h
    have hc : CGWH.prodComparisonToTop AB Sm.right cOuter = (cAB, x) :=
      Classical.choose_spec
        ((CGWH.prodComparisonToTop_bijective AB Sm.right).2 (cAB, x))
    exact h.symm.trans (congrArg Prod.fst hc)
  have hcOuter_snd :
      CartesianMonoidalCategory.snd AB Sm.right cOuter = x := by
    have h := ConcreteCategory.congr_hom
      (CGWH.prodComparisonToTop_snd AB Sm.right) cOuter
    change (CGWH.prodComparisonToTop AB Sm.right cOuter).2 =
      CartesianMonoidalCategory.snd AB Sm.right cOuter at h
    have hc : CGWH.prodComparisonToTop AB Sm.right cOuter = (cAB, x) :=
      Classical.choose_spec
        ((CGWH.prodComparisonToTop_bijective AB Sm.right).2 (cAB, x))
    exact h.symm.trans (congrArg Prod.snd hc)
  let swap : Hnp.right ⊗ Sm.right ⟶ Sm.right ⊗ Hnp.right :=
    CartesianMonoidalCategory.lift
      (CartesianMonoidalCategory.snd Hnp.right Sm.right)
      (CartesianMonoidalCategory.fst Hnp.right Sm.right)
  let w₁ : (Hmn.right ⊗ (Hnp.right ⊗ Sm.right) : CGWH.{u, v}) :=
    (α_ Hmn.right Hnp.right Sm.right).hom cOuter
  let w₂ : (Hmn.right ⊗ (Sm.right ⊗ Hnp.right) : CGWH.{u, v}) :=
    (Hmn.right ◁ swap) w₁
  let w₃ : ((Hmn.right ⊗ Sm.right) ⊗ Hnp.right : CGWH.{u, v}) :=
    (α_ Hmn.right Sm.right Hnp.right).inv w₂
  have hw₁a :
      CartesianMonoidalCategory.fst Hmn.right
        (Hnp.right ⊗ Sm.right) w₁ = a := by
    have h := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.associator_hom_fst
        Hmn.right Hnp.right Sm.right) cOuter
    change CartesianMonoidalCategory.fst Hmn.right (Hnp.right ⊗ Sm.right) w₁ =
      CartesianMonoidalCategory.fst Hmn.right Hnp.right
        (CartesianMonoidalCategory.fst AB Sm.right cOuter) at h
    rw [h, hcOuter_fst, hcAB_fst]
  have hw₁b :
      CartesianMonoidalCategory.fst Hnp.right Sm.right
        (CartesianMonoidalCategory.snd Hmn.right
          (Hnp.right ⊗ Sm.right) w₁) = b := by
    have h := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.associator_hom_snd_fst
        Hmn.right Hnp.right Sm.right) cOuter
    change CartesianMonoidalCategory.fst Hnp.right Sm.right
        (CartesianMonoidalCategory.snd Hmn.right (Hnp.right ⊗ Sm.right) w₁) =
      CartesianMonoidalCategory.snd Hmn.right Hnp.right
        (CartesianMonoidalCategory.fst AB Sm.right cOuter) at h
    rw [h, hcOuter_fst, hcAB_snd]
  have hw₁x :
      CartesianMonoidalCategory.snd Hnp.right Sm.right
        (CartesianMonoidalCategory.snd Hmn.right
          (Hnp.right ⊗ Sm.right) w₁) = x := by
    have h := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.associator_hom_snd_snd
        Hmn.right Hnp.right Sm.right) cOuter
    change CartesianMonoidalCategory.snd Hnp.right Sm.right
        (CartesianMonoidalCategory.snd Hmn.right (Hnp.right ⊗ Sm.right) w₁) =
      CartesianMonoidalCategory.snd AB Sm.right cOuter at h
    rw [h, hcOuter_snd]
  have hw₂a :
      CartesianMonoidalCategory.fst Hmn.right
        (Sm.right ⊗ Hnp.right) w₂ = a := by
    have h := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.whiskerLeft_fst Hmn.right swap) w₁
    simp only [ConcreteCategory.comp_apply] at h
    rw [h, hw₁a]
  have hw₂x :
      CartesianMonoidalCategory.fst Sm.right Hnp.right
        (CartesianMonoidalCategory.snd Hmn.right
          (Sm.right ⊗ Hnp.right) w₂) = x := by
    have hmap :
        (Hmn.right ◁ swap) ≫
            CartesianMonoidalCategory.snd Hmn.right
              (Sm.right ⊗ Hnp.right) ≫
            CartesianMonoidalCategory.fst Sm.right Hnp.right =
          CartesianMonoidalCategory.snd Hmn.right
              (Hnp.right ⊗ Sm.right) ≫
            CartesianMonoidalCategory.snd Hnp.right Sm.right := by
      rw [← Category.assoc,
        CartesianMonoidalCategory.whiskerLeft_snd]
      simp only [Category.assoc]
      rw [show swap ≫
          CartesianMonoidalCategory.fst Sm.right Hnp.right =
            CartesianMonoidalCategory.snd Hnp.right Sm.right by
        dsimp only [swap]
        exact CartesianMonoidalCategory.lift_fst _ _]
    have h := ConcreteCategory.congr_hom hmap w₁
    simp only [ConcreteCategory.comp_apply] at h
    rw [h, hw₁x]
  have hw₂b :
      CartesianMonoidalCategory.snd Sm.right Hnp.right
        (CartesianMonoidalCategory.snd Hmn.right
          (Sm.right ⊗ Hnp.right) w₂) = b := by
    have hmap :
        (Hmn.right ◁ swap) ≫
            CartesianMonoidalCategory.snd Hmn.right
              (Sm.right ⊗ Hnp.right) ≫
            CartesianMonoidalCategory.snd Sm.right Hnp.right =
          CartesianMonoidalCategory.snd Hmn.right
              (Hnp.right ⊗ Sm.right) ≫
            CartesianMonoidalCategory.fst Hnp.right Sm.right := by
      rw [← Category.assoc,
        CartesianMonoidalCategory.whiskerLeft_snd]
      simp only [Category.assoc]
      rw [show swap ≫
          CartesianMonoidalCategory.snd Sm.right Hnp.right =
            CartesianMonoidalCategory.fst Hnp.right Sm.right by
        dsimp only [swap]
        exact CartesianMonoidalCategory.lift_snd _ _]
    have h := ConcreteCategory.congr_hom hmap w₁
    simp only [ConcreteCategory.comp_apply] at h
    rw [h, hw₁b]
  let wAX : (Hmn.right ⊗ Sm.right : CGWH.{u, v}) :=
    CartesianMonoidalCategory.fst
      (Hmn.right ⊗ Sm.right) Hnp.right w₃
  have hwAX_fst :
      CartesianMonoidalCategory.fst Hmn.right Sm.right wAX = a := by
    have h := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.associator_inv_fst_fst
        Hmn.right Sm.right Hnp.right) w₂
    simp only [ConcreteCategory.comp_apply] at h
    rw [h, hw₂a]
  have hwAX_snd :
      CartesianMonoidalCategory.snd Hmn.right Sm.right wAX = x := by
    have h := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.associator_inv_fst_snd
        Hmn.right Sm.right Hnp.right) w₂
    simp only [ConcreteCategory.comp_apply] at h
    rw [h, hw₂x]
  have hw₃_snd :
      CartesianMonoidalCategory.snd
        (Hmn.right ⊗ Sm.right) Hnp.right w₃ = b := by
    have h := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.associator_inv_snd
        Hmn.right Sm.right Hnp.right) w₂
    simp only [ConcreteCategory.comp_apply] at h
    rw [h, hw₂b]
  let cAX : (Hmn.right ⊗ Sm.right : CGWH.{u, v}) := Classical.choose
    ((CGWH.prodComparisonToTop_bijective Hmn.right Sm.right).2 (a, x))
  have hcAX_spec :
      CGWH.prodComparisonToTop Hmn.right Sm.right cAX = (a, x) :=
    Classical.choose_spec
      ((CGWH.prodComparisonToTop_bijective Hmn.right Sm.right).2 (a, x))
  have hwAX : wAX = cAX := by
    apply (CGWH.prodComparisonToTop_bijective Hmn.right Sm.right).1
    have hc : CGWH.prodComparisonToTop Hmn.right Sm.right cAX = (a, x) :=
      Classical.choose_spec
        ((CGWH.prodComparisonToTop_bijective Hmn.right Sm.right).2 (a, x))
    rw [hc]
    apply Prod.ext
    · have h := ConcreteCategory.congr_hom
        (CGWH.prodComparisonToTop_fst Hmn.right Sm.right) wAX
      change (CGWH.prodComparisonToTop Hmn.right Sm.right wAX).1 =
        CartesianMonoidalCategory.fst Hmn.right Sm.right wAX at h
      exact h.trans hwAX_fst
    · have h := ConcreteCategory.congr_hom
        (CGWH.prodComparisonToTop_snd Hmn.right Sm.right) wAX
      change (CGWH.prodComparisonToTop Hmn.right Sm.right wAX).2 =
        CartesianMonoidalCategory.snd Hmn.right Sm.right wAX at h
      exact h.trans hwAX_snd
  let cAXB : ((Hmn.right ⊗ Sm.right) ⊗ Hnp.right : CGWH.{u, v}) := Classical.choose
    ((CGWH.prodComparisonToTop_bijective
      (Hmn.right ⊗ Sm.right) Hnp.right).2 (cAX, b))
  have hw₃ : w₃ = cAXB := by
    apply (CGWH.prodComparisonToTop_bijective
      (Hmn.right ⊗ Sm.right) Hnp.right).1
    have hc : CGWH.prodComparisonToTop
        (Hmn.right ⊗ Sm.right) Hnp.right cAXB = (cAX, b) :=
      Classical.choose_spec
        ((CGWH.prodComparisonToTop_bijective
          (Hmn.right ⊗ Sm.right) Hnp.right).2 (cAX, b))
    rw [hc]
    apply Prod.ext
    · have h := ConcreteCategory.congr_hom
        (CGWH.prodComparisonToTop_fst
          (Hmn.right ⊗ Sm.right) Hnp.right) w₃
      change (CGWH.prodComparisonToTop (Hmn.right ⊗ Sm.right) Hnp.right w₃).1 =
        CartesianMonoidalCategory.fst (Hmn.right ⊗ Sm.right) Hnp.right w₃ at h
      exact h.trans hwAX
    · have h := ConcreteCategory.congr_hom
        (CGWH.prodComparisonToTop_snd
          (Hmn.right ⊗ Sm.right) Hnp.right) w₃
      change (CGWH.prodComparisonToTop (Hmn.right ⊗ Sm.right) Hnp.right w₃).2 =
        CartesianMonoidalCategory.snd (Hmn.right ⊗ Sm.right) Hnp.right w₃ at h
      exact h.trans hw₃_snd
  let cQX : ((Hmn ⊗ Hnp).right ⊗ Sm.right : CGWH.{u, v}) := Classical.choose
    ((CGWH.prodComparisonToTop_bijective (Hmn ⊗ Hnp).right Sm.right).2
      (q Hmn Hnp cAB, x))
  have hQX : (q Hmn Hnp ▷ Sm.right) cOuter = cQX := by
    have hNative : (q Hmn Hnp ⊗ₘ 𝟙 Sm.right) cOuter = cQX :=
      nativeProductMap_choose (q Hmn Hnp) (𝟙 Sm.right) cAB x
    have hTensor : q Hmn Hnp ⊗ₘ 𝟙 Sm.right = q Hmn Hnp ▷ Sm.right :=
      MonoidalCategory.tensorHom_id (q Hmn Hnp) Sm.right
    exact (congrArg (fun f ↦ f cOuter) hTensor).symm.trans hNative
  let ec := @eComp PointedCGWH.{u, v} _ _ OrthogonalIndex
    (OrthogonalIndex.enrichedCategory.{u, v}) m n p
  let compAB : Hmp.right := ec.right (q Hmn Hnp cAB)
  let cCompX : (Hmp.right ⊗ Sm.right : CGWH.{u, v}) := Classical.choose
    ((CGWH.prodComparisonToTop_bijective Hmp.right Sm.right).2 (compAB, x))
  have hcCompX_spec :
      CGWH.prodComparisonToTop Hmp.right Sm.right cCompX = (compAB, x) :=
    Classical.choose_spec
      ((CGWH.prodComparisonToTop_bijective Hmp.right Sm.right).2 (compAB, x))
  have hCompX : (ec.right ⊗ₘ 𝟙 Sm.right) cQX = cCompX := by
    exact nativeProductMap_choose ec.right (𝟙 Sm.right)
      (q Hmn Hnp cAB) x
  have hL :
      (q Hmn Hnp ▷ Sm.right ≫ (ec.right ⊗ₘ 𝟙 Sm.right) ≫
          q Hmp Sm ≫ (orthogonalSphereAction.{u, v} m p).right) cOuter =
        (orthogonalSphereAction.{u, v} m p).right (q Hmp Sm cCompX) := by
    change (orthogonalSphereAction.{u, v} m p).right
        (q Hmp Sm ((ec.right ⊗ₘ 𝟙 Sm.right)
          ((q Hmn Hnp ▷ Sm.right) cOuter))) =
      (orthogonalSphereAction.{u, v} m p).right (q Hmp Sm cCompX)
    rw [hQX]
    exact congrArg
      (fun d ↦ (orthogonalSphereAction.{u, v} m p).right
        (q Hmp Sm d)) hCompX
  let cQAB : ((Hmn ⊗ Sm).right ⊗ Hnp.right : CGWH.{u, v}) := Classical.choose
    ((CGWH.prodComparisonToTop_bijective
      (Hmn ⊗ Sm).right Hnp.right).2 (q Hmn Sm cAX, b))
  have hQAB : (q Hmn Sm ▷ Hnp.right) cAXB = cQAB := by
    have hNative : (q Hmn Sm ⊗ₘ 𝟙 Hnp.right) cAXB = cQAB :=
      nativeProductMap_choose (q Hmn Sm) (𝟙 Hnp.right) cAX b
    have hTensor : q Hmn Sm ⊗ₘ 𝟙 Hnp.right = q Hmn Sm ▷ Hnp.right :=
      MonoidalCategory.tensorHom_id (q Hmn Sm) Hnp.right
    exact (congrArg (fun f ↦ f cAXB) hTensor).symm.trans hNative
  let y : Sn.right :=
    (orthogonalSphereAction.{u, v} m n).right (q Hmn Sm cAX)
  let cYB : (Sn.right ⊗ Hnp.right : CGWH.{u, v}) := Classical.choose
    ((CGWH.prodComparisonToTop_bijective Sn.right Hnp.right).2 (y, b))
  have hYB :
      ((orthogonalSphereAction.{u, v} m n).right ⊗ₘ 𝟙 Hnp.right) cQAB =
        cYB := by
    exact nativeProductMap_choose
      (orthogonalSphereAction.{u, v} m n).right (𝟙 Hnp.right)
        (q Hmn Sm cAX) b
  let swap₂ : Sn.right ⊗ Hnp.right ⟶ Hnp.right ⊗ Sn.right :=
    CartesianMonoidalCategory.lift
      (CartesianMonoidalCategory.snd Sn.right Hnp.right)
      (CartesianMonoidalCategory.fst Sn.right Hnp.right)
  let cBY : (Hnp.right ⊗ Sn.right : CGWH.{u, v}) := Classical.choose
    ((CGWH.prodComparisonToTop_bijective Hnp.right Sn.right).2 (b, y))
  have hcBY_spec :
      CGWH.prodComparisonToTop Hnp.right Sn.right cBY = (b, y) :=
    Classical.choose_spec
      ((CGWH.prodComparisonToTop_bijective Hnp.right Sn.right).2 (b, y))
  have hcYB_fst :
      CartesianMonoidalCategory.fst Sn.right Hnp.right cYB = y := by
    have h := ConcreteCategory.congr_hom
      (CGWH.prodComparisonToTop_fst Sn.right Hnp.right) cYB
    change (CGWH.prodComparisonToTop Sn.right Hnp.right cYB).1 =
      CartesianMonoidalCategory.fst Sn.right Hnp.right cYB at h
    have hc : CGWH.prodComparisonToTop Sn.right Hnp.right cYB = (y, b) :=
      Classical.choose_spec
        ((CGWH.prodComparisonToTop_bijective Sn.right Hnp.right).2 (y, b))
    exact h.symm.trans (congrArg Prod.fst hc)
  have hcYB_snd :
      CartesianMonoidalCategory.snd Sn.right Hnp.right cYB = b := by
    have h := ConcreteCategory.congr_hom
      (CGWH.prodComparisonToTop_snd Sn.right Hnp.right) cYB
    change (CGWH.prodComparisonToTop Sn.right Hnp.right cYB).2 =
      CartesianMonoidalCategory.snd Sn.right Hnp.right cYB at h
    have hc : CGWH.prodComparisonToTop Sn.right Hnp.right cYB = (y, b) :=
      Classical.choose_spec
        ((CGWH.prodComparisonToTop_bijective Sn.right Hnp.right).2 (y, b))
    exact h.symm.trans (congrArg Prod.snd hc)
  have hSwap₂ : swap₂ cYB = cBY := by
    apply (CGWH.prodComparisonToTop_bijective Hnp.right Sn.right).1
    have hc : CGWH.prodComparisonToTop Hnp.right Sn.right cBY = (b, y) :=
      Classical.choose_spec
        ((CGWH.prodComparisonToTop_bijective Hnp.right Sn.right).2 (b, y))
    have hPair : CGWH.prodComparisonToTop Hnp.right Sn.right (swap₂ cYB) =
        (b, y) := by
      apply Prod.ext
      · have h := ConcreteCategory.congr_hom
          (CGWH.prodComparisonToTop_fst Hnp.right Sn.right) (swap₂ cYB)
        change (CGWH.prodComparisonToTop Hnp.right Sn.right (swap₂ cYB)).1 =
          CartesianMonoidalCategory.fst Hnp.right Sn.right (swap₂ cYB) at h
        have hm : swap₂ ≫ CartesianMonoidalCategory.fst Hnp.right Sn.right =
            CartesianMonoidalCategory.snd Sn.right Hnp.right := by
          dsimp only [swap₂]
          exact CartesianMonoidalCategory.lift_fst _ _
        have he := ConcreteCategory.congr_hom hm cYB
        change CartesianMonoidalCategory.fst Hnp.right Sn.right (swap₂ cYB) =
          CartesianMonoidalCategory.snd Sn.right Hnp.right cYB at he
        exact h.trans (he.trans hcYB_snd)
      · have h := ConcreteCategory.congr_hom
          (CGWH.prodComparisonToTop_snd Hnp.right Sn.right) (swap₂ cYB)
        change (CGWH.prodComparisonToTop Hnp.right Sn.right (swap₂ cYB)).2 =
          CartesianMonoidalCategory.snd Hnp.right Sn.right (swap₂ cYB) at h
        have hm : swap₂ ≫ CartesianMonoidalCategory.snd Hnp.right Sn.right =
            CartesianMonoidalCategory.fst Sn.right Hnp.right := by
          dsimp only [swap₂]
          exact CartesianMonoidalCategory.lift_snd _ _
        have he := ConcreteCategory.congr_hom hm cYB
        change CartesianMonoidalCategory.snd Hnp.right Sn.right (swap₂ cYB) =
          CartesianMonoidalCategory.fst Sn.right Hnp.right cYB at he
        exact h.trans (he.trans hcYB_fst)
    exact hPair.trans hc.symm
  have hR :
      ((α_ Hmn.right Hnp.right Sm.right).hom ≫
          (Hmn.right ◁ swap) ≫
          (α_ Hmn.right Sm.right Hnp.right).inv ≫
          (q Hmn Sm ▷ Hnp.right) ≫
          ((orthogonalSphereAction.{u, v} m n).right ⊗ₘ
            𝟙 Hnp.right) ≫ swap₂ ≫ q Hnp Sn ≫
          (orthogonalSphereAction.{u, v} n p).right) cOuter =
        (orthogonalSphereAction.{u, v} n p).right (q Hnp Sn cBY) := by
    change (orthogonalSphereAction.{u, v} n p).right
      (q Hnp Sn (swap₂
        (((orthogonalSphereAction.{u, v} m n).right ⊗ₘ 𝟙 Hnp.right)
          ((q Hmn Sm ▷ Hnp.right) w₃)))) =
      (orthogonalSphereAction.{u, v} n p).right (q Hnp Sn cBY)
    rw [hw₃, hQAB, hYB, hSwap₂]
  have comp_value
      (f : 𝟙_ PointedCGWH.{u, v} ⟶ Hmn)
      (g : 𝟙_ PointedCGWH.{u, v} ⟶ Hnp)
      (h : 𝟙_ PointedCGWH.{u, v} ⟶ Hmp)
      (hcomp : (λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫
          (f ⊗ₘ g) ≫ ec = h) :
      let c := Classical.choose
        ((CGWH.prodComparisonToTop_bijective Hmn.right Hnp.right).2
          (f.right t, g.right t))
      ec.right (q Hmn Hnp c) = h.right t := by
    dsimp only
    have hp := pointTensor_free f g
    have hc := ConcreteCategory.congr_hom
      (congrArg Under.Hom.right hcomp) t
    simp only [Under.comp_right, ConcreteCategory.comp_apply] at hc
    exact (congrArg ec.right hp).symm.trans hc
  rw [hz]
  rcases homPoint_cases m n a with ha | ⟨A, ha⟩
  · have hqAB : q Hmn Hnp cAB =
        (Hmn ⊗ Hnp).hom PUnit.unit := by
      dsimp only [cAB]
      rw [ha]
      exact q_left_base Hmn Hnp b
    have hcompAB : compAB = Hmp.hom PUnit.unit := by
      dsimp only [compAB]
      rw [hqAB]
      exact preservesBase ec
    have hqComp : q Hmp Sm cCompX =
        (Hmp ⊗ Sm).hom PUnit.unit := by
      dsimp only [cCompX]
      rw [hcompAB]
      exact q_left_base Hmp Sm x
    have hleft :
        (orthogonalSphereAction.{u, v} m p).right (q Hmp Sm cCompX) =
          (orthogonalSphere.{u, v} p).hom PUnit.unit := by
      rw [hqComp]
      exact preservesBase (orthogonalSphereAction.{u, v} m p)
    have hqAX : q Hmn Sm cAX = (Hmn ⊗ Sm).hom PUnit.unit := by
      dsimp only [cAX]
      rw [ha]
      exact q_left_base Hmn Sm x
    have hybase : y = Sn.hom PUnit.unit := by
      dsimp only [y]
      rw [hqAX]
      exact preservesBase (orthogonalSphereAction.{u, v} m n)
    have hqBY : q Hnp Sn cBY = (Hnp ⊗ Sn).hom PUnit.unit := by
      dsimp only [cBY]
      rw [hybase]
      exact q_right_base Hnp Sn b
    have hright :
        (orthogonalSphereAction.{u, v} n p).right (q Hnp Sn cBY) =
          (orthogonalSphere.{u, v} p).hom PUnit.unit := by
      rw [hqBY]
      exact preservesBase (orthogonalSphereAction.{u, v} n p)
    change
      (q Hmn Hnp ▷ Sm.right ≫ (ec.right ⊗ₘ 𝟙 Sm.right) ≫
        q Hmp Sm ≫ (orthogonalSphereAction.{u, v} m p).right) cOuter =
      ((α_ Hmn.right Hnp.right Sm.right).hom ≫
        (Hmn.right ◁ swap) ≫
        (α_ Hmn.right Sm.right Hnp.right).inv ≫
        (q Hmn Sm ▷ Hnp.right) ≫
        ((orthogonalSphereAction.{u, v} m n).right ⊗ₘ 𝟙 Hnp.right) ≫
        swap₂ ≫ q Hnp Sn ≫
        (orthogonalSphereAction.{u, v} n p).right) cOuter
    rw [hL, hR]
    exact hleft.trans hright.symm
  · rcases homPoint_cases n p b with hb | ⟨B, hb⟩
    · have hqAB : q Hmn Hnp cAB =
          (Hmn ⊗ Hnp).hom PUnit.unit := by
        dsimp only [cAB]
        rw [hb]
        exact q_right_base Hmn Hnp a
      have hcompAB : compAB = Hmp.hom PUnit.unit := by
        dsimp only [compAB]
        rw [hqAB]
        exact preservesBase ec
      have hqComp : q Hmp Sm cCompX =
          (Hmp ⊗ Sm).hom PUnit.unit := by
        dsimp only [cCompX]
        rw [hcompAB]
        exact q_left_base Hmp Sm x
      have hleft :
          (orthogonalSphereAction.{u, v} m p).right (q Hmp Sm cCompX) =
            (orthogonalSphere.{u, v} p).hom PUnit.unit := by
        rw [hqComp]
        exact preservesBase (orthogonalSphereAction.{u, v} m p)
      have hqBY : q Hnp Sn cBY = (Hnp ⊗ Sn).hom PUnit.unit := by
        dsimp only [cBY]
        rw [hb]
        exact q_left_base Hnp Sn y
      have hright :
          (orthogonalSphereAction.{u, v} n p).right (q Hnp Sn cBY) =
            (orthogonalSphere.{u, v} p).hom PUnit.unit := by
        rw [hqBY]
        exact preservesBase (orthogonalSphereAction.{u, v} n p)
      change
        (q Hmn Hnp ▷ Sm.right ≫ (ec.right ⊗ₘ 𝟙 Sm.right) ≫
          q Hmp Sm ≫ (orthogonalSphereAction.{u, v} m p).right) cOuter =
        ((α_ Hmn.right Hnp.right Sm.right).hom ≫
          (Hmn.right ◁ swap) ≫
          (α_ Hmn.right Sm.right Hnp.right).inv ≫
          (q Hmn Sm ▷ Hnp.right) ≫
          ((orthogonalSphereAction.{u, v} m n).right ⊗ₘ 𝟙 Hnp.right) ≫
          swap₂ ≫ q Hnp Sn ≫
          (orthogonalSphereAction.{u, v} n p).right) cOuter
      rw [hL, hR]
      exact hleft.trans hright.symm
    · let BA := OrthogonalMatrixHom.comp A B
      let pA : Hmn.right :=
        (OrthogonalIndex.matrixPoint.{u, v} A).right t
      let pB : Hnp.right :=
        (OrthogonalIndex.matrixPoint.{u, v} B).right t
      let pBA : Hmp.right :=
        (OrthogonalIndex.matrixPoint.{u, v} BA).right t
      have hcompAB : compAB = pBA := by
        have hc := comp_value
          (OrthogonalIndex.matrixPoint.{u, v} A)
          (OrthogonalIndex.matrixPoint.{u, v} B)
          (OrthogonalIndex.matrixPoint.{u, v} BA)
          (OrthogonalIndex.enrichedCategory_comp.{u, v} A B).1
        dsimp only [compAB, cAB]
        rw [ha, hb]
        exact hc
      generalize hx : x = x₀
      induction x₀ using OnePoint.rec with
      | infty =>
          let cCompInf : (Hmp.right ⊗ Sm.right : CGWH.{u, v}) := Classical.choose
            ((CGWH.prodComparisonToTop_bijective Hmp.right Sm.right).2
              (pBA, OnePoint.infty))
          have hcCompInf : cCompX = cCompInf := by
            apply (CGWH.prodComparisonToTop_bijective Hmp.right Sm.right).1
            have hSource : CGWH.prodComparisonToTop Hmp.right Sm.right cCompX =
                (compAB, x) := hcCompX_spec
            have hPair : (compAB, x) = (pBA, (OnePoint.infty : Sm.right)) := Prod.ext hcompAB hx
            have hTarget : CGWH.prodComparisonToTop Hmp.right Sm.right cCompInf =
                (pBA, (OnePoint.infty : Sm.right)) :=
              Classical.choose_spec
                ((CGWH.prodComparisonToTop_bijective Hmp.right Sm.right).2
                  (pBA, (OnePoint.infty : Sm.right)))
            exact hSource.trans (hPair.trans hTarget.symm)
          have hleft₀ :=
            orthogonalSphereAction_infty.{u, v} m p pBA
          change (orthogonalSphereAction.{u, v} m p).right
              (q Hmp Sm cCompInf) = OnePoint.infty at hleft₀
          have hleft :
              (orthogonalSphereAction.{u, v} m p).right
                  (q Hmp Sm cCompX) = OnePoint.infty := by
            rw [hcCompInf]
            exact hleft₀
          let cAInf : (Hmn.right ⊗ Sm.right : CGWH.{u, v}) := Classical.choose
            ((CGWH.prodComparisonToTop_bijective Hmn.right Sm.right).2
              (pA, OnePoint.infty))
          have hcAInf : cAX = cAInf := by
            apply (CGWH.prodComparisonToTop_bijective Hmn.right Sm.right).1
            have hSource : CGWH.prodComparisonToTop Hmn.right Sm.right cAX =
                (a, x) := hcAX_spec
            have hPair : (a, x) = (pA, (OnePoint.infty : Sm.right)) := Prod.ext ha hx
            have hTarget : CGWH.prodComparisonToTop Hmn.right Sm.right cAInf =
                (pA, (OnePoint.infty : Sm.right)) :=
              Classical.choose_spec
                ((CGWH.prodComparisonToTop_bijective Hmn.right Sm.right).2
                  (pA, (OnePoint.infty : Sm.right)))
            exact hSource.trans (hPair.trans hTarget.symm)
          have hy₀ := orthogonalSphereAction_infty.{u, v} m n pA
          change (orthogonalSphereAction.{u, v} m n).right
              (q Hmn Sm cAInf) = OnePoint.infty at hy₀
          have hyInf : y = OnePoint.infty := by
            dsimp only [y]
            rw [hcAInf]
            exact hy₀
          let cBInf : (Hnp.right ⊗ Sn.right : CGWH.{u, v}) := Classical.choose
            ((CGWH.prodComparisonToTop_bijective Hnp.right Sn.right).2
              (pB, OnePoint.infty))
          have hcBInf : cBY = cBInf := by
            apply (CGWH.prodComparisonToTop_bijective Hnp.right Sn.right).1
            have hSource : CGWH.prodComparisonToTop Hnp.right Sn.right cBY =
                (b, y) := hcBY_spec
            have hPair : (b, y) = (pB, (OnePoint.infty : Sn.right)) := Prod.ext hb hyInf
            have hTarget : CGWH.prodComparisonToTop Hnp.right Sn.right cBInf =
                (pB, (OnePoint.infty : Sn.right)) :=
              Classical.choose_spec
                ((CGWH.prodComparisonToTop_bijective Hnp.right Sn.right).2
                  (pB, (OnePoint.infty : Sn.right)))
            exact hSource.trans (hPair.trans hTarget.symm)
          have hright₀ :=
            orthogonalSphereAction_infty.{u, v} n p pB
          change (orthogonalSphereAction.{u, v} n p).right
              (q Hnp Sn cBInf) = OnePoint.infty at hright₀
          have hright :
              (orthogonalSphereAction.{u, v} n p).right
                  (q Hnp Sn cBY) = OnePoint.infty := by
            rw [hcBInf]
            exact hright₀
          change
            (q Hmn Hnp ▷ Sm.right ≫ (ec.right ⊗ₘ 𝟙 Sm.right) ≫
              q Hmp Sm ≫
              (orthogonalSphereAction.{u, v} m p).right) cOuter =
            ((α_ Hmn.right Hnp.right Sm.right).hom ≫
              (Hmn.right ◁ swap) ≫
              (α_ Hmn.right Sm.right Hnp.right).inv ≫
              (q Hmn Sm ▷ Hnp.right) ≫
              ((orthogonalSphereAction.{u, v} m n).right ⊗ₘ
                𝟙 Hnp.right) ≫
              swap₂ ≫ q Hnp Sn ≫
              (orthogonalSphereAction.{u, v} n p).right) cOuter
          rw [hL, hR]
          exact hleft.trans hright.symm
      | coe x' =>
          rcases x' with ⟨x'⟩
          let xPoint : Sm.right :=
            ((ULift.up x' : liftedEuclidean.{v} m) :
              OnePoint (liftedEuclidean.{v} m))
          let Ax : EuclideanSpace ℝ (Fin n) :=
            (EuclideanSpace.equiv (Fin n) ℝ).symm (A.1 *ᵥ x'.ofLp)
          let yPoint : Sn.right :=
            ((ULift.up Ax : liftedEuclidean.{v} n) :
              OnePoint (liftedEuclidean.{v} n))
          let cCompFin : (Hmp.right ⊗ Sm.right : CGWH.{u, v}) := Classical.choose
            ((CGWH.prodComparisonToTop_bijective Hmp.right Sm.right).2
              (pBA, xPoint))
          have hcCompFin : cCompX = cCompFin := by
            apply (CGWH.prodComparisonToTop_bijective Hmp.right Sm.right).1
            have hSource : CGWH.prodComparisonToTop Hmp.right Sm.right cCompX =
                (compAB, x) := hcCompX_spec
            have hPair : (compAB, x) = (pBA, xPoint) := Prod.ext hcompAB hx
            have hTarget : CGWH.prodComparisonToTop Hmp.right Sm.right cCompFin =
                (pBA, xPoint) :=
              Classical.choose_spec
                ((CGWH.prodComparisonToTop_bijective Hmp.right Sm.right).2
                  (pBA, xPoint))
            exact hSource.trans (hPair.trans hTarget.symm)
          have hleft₀ :=
            orthogonalSphereAction_coe.{u, v} BA x'
          change (orthogonalSphereAction.{u, v} m p).right
              (q Hmp Sm cCompFin) =
            ((ULift.up ((EuclideanSpace.equiv (Fin p) ℝ).symm
              (BA.1 *ᵥ x'.ofLp)) : liftedEuclidean.{v} p) :
                OnePoint (liftedEuclidean.{v} p)) at hleft₀
          have hleft :
              (orthogonalSphereAction.{u, v} m p).right
                  (q Hmp Sm cCompX) =
                ((ULift.up ((EuclideanSpace.equiv (Fin p) ℝ).symm
                  (BA.1 *ᵥ x'.ofLp)) : liftedEuclidean.{v} p) :
                    OnePoint (liftedEuclidean.{v} p)) := by
            rw [hcCompFin]
            exact hleft₀
          let cAFin : (Hmn.right ⊗ Sm.right : CGWH.{u, v}) := Classical.choose
            ((CGWH.prodComparisonToTop_bijective Hmn.right Sm.right).2
              (pA, xPoint))
          have hcAFin : cAX = cAFin := by
            apply (CGWH.prodComparisonToTop_bijective Hmn.right Sm.right).1
            have hSource : CGWH.prodComparisonToTop Hmn.right Sm.right cAX =
                (a, x) := hcAX_spec
            have hPair : (a, x) = (pA, xPoint) := Prod.ext ha hx
            have hTarget : CGWH.prodComparisonToTop Hmn.right Sm.right cAFin =
                (pA, xPoint) :=
              Classical.choose_spec
                ((CGWH.prodComparisonToTop_bijective Hmn.right Sm.right).2
                  (pA, xPoint))
            exact hSource.trans (hPair.trans hTarget.symm)
          have hy₀ := orthogonalSphereAction_coe.{u, v} A x'
          change (orthogonalSphereAction.{u, v} m n).right
              (q Hmn Sm cAFin) = yPoint at hy₀
          have hyFin : y = yPoint := by
            dsimp only [y]
            rw [hcAFin]
            exact hy₀
          let cBFin : (Hnp.right ⊗ Sn.right : CGWH.{u, v}) := Classical.choose
            ((CGWH.prodComparisonToTop_bijective Hnp.right Sn.right).2
              (pB, yPoint))
          have hcBFin : cBY = cBFin := by
            apply (CGWH.prodComparisonToTop_bijective Hnp.right Sn.right).1
            have hSource : CGWH.prodComparisonToTop Hnp.right Sn.right cBY =
                (b, y) := hcBY_spec
            have hPair : (b, y) = (pB, yPoint) := Prod.ext hb hyFin
            have hTarget : CGWH.prodComparisonToTop Hnp.right Sn.right cBFin =
                (pB, yPoint) :=
              Classical.choose_spec
                ((CGWH.prodComparisonToTop_bijective Hnp.right Sn.right).2
                  (pB, yPoint))
            exact hSource.trans (hPair.trans hTarget.symm)
          have hright₀ := orthogonalSphereAction_coe.{u, v} B Ax
          change (orthogonalSphereAction.{u, v} n p).right
              (q Hnp Sn cBFin) =
            ((ULift.up ((EuclideanSpace.equiv (Fin p) ℝ).symm
              (B.1 *ᵥ Ax.ofLp)) : liftedEuclidean.{v} p) :
                OnePoint (liftedEuclidean.{v} p)) at hright₀
          have hright :
              (orthogonalSphereAction.{u, v} n p).right
                  (q Hnp Sn cBY) =
                ((ULift.up ((EuclideanSpace.equiv (Fin p) ℝ).symm
                  (B.1 *ᵥ Ax.ofLp)) : liftedEuclidean.{v} p) :
                    OnePoint (liftedEuclidean.{v} p)) := by
            rw [hcBFin]
            exact hright₀
          have hmatrix :
              (EuclideanSpace.equiv (Fin p) ℝ).symm
                  (BA.1 *ᵥ x'.ofLp) =
                (EuclideanSpace.equiv (Fin p) ℝ).symm
                  (B.1 *ᵥ Ax.ofLp) := by
            apply congrArg (EuclideanSpace.equiv (Fin p) ℝ).symm
            dsimp only [BA, Ax, OrthogonalMatrixHom.comp]
            change (B.1 * A.1) *ᵥ x'.ofLp =
              B.1 *ᵥ (A.1 *ᵥ x'.ofLp)
            exact (Matrix.mulVec_mulVec x'.ofLp B.1 A.1).symm
          change
            (q Hmn Hnp ▷ Sm.right ≫ (ec.right ⊗ₘ 𝟙 Sm.right) ≫
              q Hmp Sm ≫
              (orthogonalSphereAction.{u, v} m p).right) cOuter =
            ((α_ Hmn.right Hnp.right Sm.right).hom ≫
              (Hmn.right ◁ swap) ≫
              (α_ Hmn.right Sm.right Hnp.right).inv ≫
              (q Hmn Sm ▷ Hnp.right) ≫
              ((orthogonalSphereAction.{u, v} m n).right ⊗ₘ
                𝟙 Hnp.right) ≫
              swap₂ ≫ q Hnp Sn ≫
              (orthogonalSphereAction.{u, v} n p).right) cOuter
          rw [hL, hR, hleft, hright]
          exact congrArg
            (fun z : EuclideanSpace ℝ (Fin p) ↦
              ((ULift.up z : liftedEuclidean.{v} p) :
                OnePoint (liftedEuclidean.{v} p))) hmatrix

private theorem action_blockSum
    (m n p q : OrthogonalIndex) :
    (OrthogonalIndex.tensorMap.{u, v} m n p q ⊗ₘ
        (orthogonalSphereTensorIso.{u, v} m p).inv) ≫
      orthogonalSphereAction.{u, v} (m + p) (n + q) ≫
      (orthogonalSphereTensorIso.{u, v} n q).hom =
    MonoidalCategory.tensorμ
        (OrthogonalIndex.hom.{u, v} m n)
        (OrthogonalIndex.hom.{u, v} p q)
        (orthogonalSphere.{u, v} m)
        (orthogonalSphere.{u, v} p) ≫
      (orthogonalSphereAction.{u, v} m n ⊗ₘ
        orthogonalSphereAction.{u, v} p q) := by
  let _ : BraidedCategory CGWH.{u, v} :=
    BraidedCategory.ofCartesianMonoidalCategory
  let _ : SymmetricCategory CGWH.{u, v} := inferInstance
  let H₁ := OrthogonalIndex.hom.{u, v} m n
  let H₂ := OrthogonalIndex.hom.{u, v} p q
  let S₁ := orthogonalSphere.{u, v} m
  let S₂ := orthogonalSphere.{u, v} p
  let Hsum := OrthogonalIndex.hom.{u, v} (m + p) (n + q)
  let Ssum := orthogonalSphere.{u, v} (m + p)
  let T₁ := orthogonalSphere.{u, v} n
  let T₂ := orthogonalSphere.{u, v} q
  let qSmash (X Y : PointedCGWH.{u, v}) :
      X.right ⊗ Y.right ⟶ (X ⊗ Y).right :=
    (CategoryTheory.Pointed.smashPresentation
      CGWH.point CGWH.point_isTerminal X Y).2.1.inl
  have hμ :
      (qSmash H₁ H₂ ⊗ₘ qSmash S₁ S₂) ≫
          qSmash (H₁ ⊗ H₂) (S₁ ⊗ S₂) ≫
          (MonoidalCategory.tensorμ H₁ H₂ S₁ S₂).right =
        MonoidalCategory.tensorμ H₁.right H₂.right S₁.right S₂.right ≫
          (qSmash H₁ S₁ ⊗ₘ qSmash H₂ S₂) ≫
          qSmash (H₁ ⊗ S₁) (H₂ ⊗ S₂) := by
    unfold MonoidalCategory.tensorμ
    simp only [Under.comp_right, Category.assoc]
    slice_lhs 1 1 =>
      rw [MonoidalCategory.tensorHom_def']
    simp only [Category.assoc]
    have hAssoc₁ :=
      CategoryTheory.Pointed.smashAssociator_hom_quotient
        CGWH.point.{u, v} CGWH.point_isTerminal H₁ H₂ (S₁ ⊗ S₂)
    change ((qSmash H₁ H₂ ▷ (S₁ ⊗ S₂).right) ≫
        qSmash (H₁ ⊗ H₂) (S₁ ⊗ S₂)) ≫
        (α_ H₁ H₂ (S₁ ⊗ S₂)).hom.right =
      (α_ H₁.right H₂.right (S₁ ⊗ S₂).right).hom ≫
        (H₁.right ◁ qSmash H₂ (S₁ ⊗ S₂)) ≫
        qSmash H₁ (H₂ ⊗ (S₁ ⊗ S₂)) at hAssoc₁
    slice_lhs 2 4 =>
      rw [← Category.assoc, hAssoc₁]
    have hNatAssoc₁ :
        ((H₁.right ⊗ H₂.right) ◁ qSmash S₁ S₂) ≫
            (α_ H₁.right H₂.right (S₁ ⊗ S₂).right).hom =
          (α_ H₁.right H₂.right
            (S₁.right ⊗ S₂.right)).hom ≫
            (H₁.right ◁ (H₂.right ◁ qSmash S₁ S₂)) := by
      simpa only [MonoidalCategory.tensorHom_id,
        MonoidalCategory.id_tensorHom,
        MonoidalCategory.id_whiskerRight] using
        (MonoidalCategory.associator_naturality
          (𝟙 H₁.right) (𝟙 H₂.right) (qSmash S₁ S₂))
    slice_lhs 1 2 =>
      rw [hNatAssoc₁]
    simp only [Category.assoc]
    have hPointTensorAssocInv :
        (H₁ ◁ (α_ H₂ S₁ S₂).inv).right =
          (𝟙 H₁ ⊗ₘ (α_ H₂ S₁ S₂).inv).right := by
      rw [MonoidalCategory.id_tensorHom]
    rw [hPointTensorAssocInv]
    have hQuotAssoc : qSmash H₁ (H₂ ⊗ (S₁ ⊗ S₂)) ≫
        (𝟙 H₁ ⊗ₘ (α_ H₂ S₁ S₂).inv).right =
      (𝟙 H₁.right ⊗ₘ (α_ H₂ S₁ S₂).inv.right) ≫
        qSmash H₁ ((H₂ ⊗ S₁) ⊗ S₂) :=
      CategoryTheory.Pointed.smashQuotient_naturality
        CGWH.point.{u, v} CGWH.point_isTerminal (𝟙 H₁) (α_ H₂ S₁ S₂).inv
    slice_lhs 4 5 => rw [hQuotAssoc]
    have hTensorAssocInv :
        (𝟙 H₁.right) ⊗ₘ (α_ H₂ S₁ S₂).inv.right =
          H₁.right ◁ (α_ H₂ S₁ S₂).inv.right := by
      exact MonoidalCategory.id_tensorHom _ _
    rw [hTensorAssocInv]
    have hAssocInv₂ :=
      CategoryTheory.Pointed.smashAssociator_inv_quotient
        CGWH.point.{u, v} CGWH.point_isTerminal H₂ S₁ S₂
    change ((H₂.right ◁ qSmash S₁ S₂) ≫
        qSmash H₂ (S₁ ⊗ S₂)) ≫
        (α_ H₂ S₁ S₂).inv.right =
      (α_ H₂.right S₁.right S₂.right).inv ≫
        (qSmash H₂ S₁ ▷ S₂.right) ≫
        qSmash (H₂ ⊗ S₁) S₂ at hAssocInv₂
    have hAssocInv₂' :
        (H₂.right ◁ qSmash S₁ S₂) ≫
            qSmash H₂ (S₁ ⊗ S₂) ≫
            (α_ H₂ S₁ S₂).inv.right =
          (α_ H₂.right S₁.right S₂.right).inv ≫
            (qSmash H₂ S₁ ▷ S₂.right) ≫
            qSmash (H₂ ⊗ S₁) S₂ := by
      rw [← Category.assoc, hAssocInv₂]
    slice_lhs 2 4 =>
      rw [← MonoidalCategory.whiskerLeft_comp,
        ← MonoidalCategory.whiskerLeft_comp, hAssocInv₂',
        MonoidalCategory.whiskerLeft_comp,
        MonoidalCategory.whiskerLeft_comp]
    simp only [Category.assoc]
    let k : ((H₂ ⊗ S₁) ⊗ S₂) ⟶ ((S₁ ⊗ H₂) ⊗ S₂) :=
      (β_ H₂ S₁).hom ▷ S₂
    have hPointTensorK :
        (H₁ ◁ k).right = (𝟙 H₁ ⊗ₘ k).right := by
      rw [MonoidalCategory.id_tensorHom]
    dsimp only [k] at hPointTensorK
    rw [hPointTensorK]
    have hQuotK : qSmash H₁ ((H₂ ⊗ S₁) ⊗ S₂) ≫
        (𝟙 H₁ ⊗ₘ k).right =
      (𝟙 H₁.right ⊗ₘ k.right) ≫ qSmash H₁ ((S₁ ⊗ H₂) ⊗ S₂) :=
      CategoryTheory.Pointed.smashQuotient_naturality
        CGWH.point.{u, v} CGWH.point_isTerminal (𝟙 H₁) k
    slice_lhs 5 6 => rw [hQuotK]
    have hTensorK :
        (𝟙 H₁.right) ⊗ₘ k.right = H₁.right ◁ k.right := by
      exact MonoidalCategory.id_tensorHom _ _
    rw [hTensorK]
    have hInnerNat :=
      CategoryTheory.Pointed.smashQuotient_naturality
        CGWH.point.{u, v} CGWH.point_isTerminal
        (β_ H₂ S₁).hom (𝟙 S₂)
    simp only [Under.id_right] at hInnerNat
    have hkRight :
        ((β_ H₂ S₁).hom ⊗ₘ 𝟙 S₂).right = k.right :=
      congrArg Under.Hom.right
        (MonoidalCategory.tensorHom_id (β_ H₂ S₁).hom S₂)
    rw [hkRight] at hInnerNat
    change qSmash (H₂ ⊗ S₁) S₂ ≫ k.right =
      ((β_ H₂ S₁).hom.right ⊗ₘ 𝟙 S₂.right) ≫
        qSmash (S₁ ⊗ H₂) S₂ at hInnerNat
    have hBraid := smashQuotient_braiding_hom H₂ S₁
    change qSmash H₂ S₁ ≫ (β_ H₂ S₁).hom.right =
      CartesianMonoidalCategory.lift
          (CartesianMonoidalCategory.snd H₂.right S₁.right)
          (CartesianMonoidalCategory.fst H₂.right S₁.right) ≫
        qSmash S₁ H₂ at hBraid
    let swapRaw : H₂.right ⊗ S₁.right ⟶ S₁.right ⊗ H₂.right :=
      CartesianMonoidalCategory.lift
        (CartesianMonoidalCategory.snd H₂.right S₁.right)
        (CartesianMonoidalCategory.fst H₂.right S₁.right)
    have hInnerBraid :
        (qSmash H₂ S₁ ▷ S₂.right) ≫
            qSmash (H₂ ⊗ S₁) S₂ ≫ k.right =
          (swapRaw ▷ S₂.right) ≫
            (qSmash S₁ H₂ ▷ S₂.right) ≫
            qSmash (S₁ ⊗ H₂) S₂ := by
      rw [hInnerNat]
      rw [MonoidalCategory.tensorHom_id]
      rw [← Category.assoc, ← MonoidalCategory.comp_whiskerRight, hBraid,
        MonoidalCategory.comp_whiskerRight]
      dsimp only [swapRaw]
      rw [Category.assoc]
    slice_lhs 3 5 =>
      rw [← MonoidalCategory.whiskerLeft_comp,
        ← MonoidalCategory.whiskerLeft_comp, hInnerBraid,
        MonoidalCategory.whiskerLeft_comp,
        MonoidalCategory.whiskerLeft_comp]
    simp only [Category.assoc]
    have hPointTensorAssocHom :
        (H₁ ◁ (α_ S₁ H₂ S₂).hom).right =
          (𝟙 H₁ ⊗ₘ (α_ S₁ H₂ S₂).hom).right := by
      rw [MonoidalCategory.id_tensorHom]
    rw [hPointTensorAssocHom]
    have hQuotAssocHom : qSmash H₁ ((S₁ ⊗ H₂) ⊗ S₂) ≫
        (𝟙 H₁ ⊗ₘ (α_ S₁ H₂ S₂).hom).right =
      (𝟙 H₁.right ⊗ₘ (α_ S₁ H₂ S₂).hom.right) ≫ qSmash H₁ (S₁ ⊗ (H₂ ⊗ S₂)) :=
      CategoryTheory.Pointed.smashQuotient_naturality
        CGWH.point.{u, v} CGWH.point_isTerminal (𝟙 H₁) (α_ S₁ H₂ S₂).hom
    slice_lhs 6 7 => rw [hQuotAssocHom]
    have hTensorAssocHom :
        (𝟙 H₁.right) ⊗ₘ (α_ S₁ H₂ S₂).hom.right =
          H₁.right ◁ (α_ S₁ H₂ S₂).hom.right := by
      exact MonoidalCategory.id_tensorHom _ _
    rw [hTensorAssocHom]
    have hAssocHom₃ :=
      CategoryTheory.Pointed.smashAssociator_hom_quotient
        CGWH.point.{u, v} CGWH.point_isTerminal S₁ H₂ S₂
    change ((qSmash S₁ H₂ ▷ S₂.right) ≫
        qSmash (S₁ ⊗ H₂) S₂) ≫
        (α_ S₁ H₂ S₂).hom.right =
      (α_ S₁.right H₂.right S₂.right).hom ≫
        (S₁.right ◁ qSmash H₂ S₂) ≫
        qSmash S₁ (H₂ ⊗ S₂) at hAssocHom₃
    have hAssocHom₃' :
        (qSmash S₁ H₂ ▷ S₂.right) ≫
            qSmash (S₁ ⊗ H₂) S₂ ≫
            (α_ S₁ H₂ S₂).hom.right =
          (α_ S₁.right H₂.right S₂.right).hom ≫
            (S₁.right ◁ qSmash H₂ S₂) ≫
            qSmash S₁ (H₂ ⊗ S₂) := by
      rw [← Category.assoc, hAssocHom₃]
    slice_lhs 4 6 =>
      rw [← MonoidalCategory.whiskerLeft_comp,
        ← MonoidalCategory.whiskerLeft_comp, hAssocHom₃',
        MonoidalCategory.whiskerLeft_comp,
        MonoidalCategory.whiskerLeft_comp]
    simp only [Category.assoc]
    have hAssocInv₄ :=
      CategoryTheory.Pointed.smashAssociator_inv_quotient
        CGWH.point.{u, v} CGWH.point_isTerminal H₁ S₁ (H₂ ⊗ S₂)
    change ((H₁.right ◁ qSmash S₁ (H₂ ⊗ S₂)) ≫
        qSmash H₁ (S₁ ⊗ (H₂ ⊗ S₂))) ≫
        (α_ H₁ S₁ (H₂ ⊗ S₂)).inv.right =
      (α_ H₁.right S₁.right (H₂ ⊗ S₂).right).inv ≫
        (qSmash H₁ S₁ ▷ (H₂ ⊗ S₂).right) ≫
        qSmash (H₁ ⊗ S₁) (H₂ ⊗ S₂) at hAssocInv₄
    slice_lhs 6 8 =>
      rw [← Category.assoc, hAssocInv₄]
    have hNatAssocInv₄ :
        (H₁.right ◁ (S₁.right ◁ qSmash H₂ S₂)) ≫
            (α_ H₁.right S₁.right (H₂ ⊗ S₂).right).inv =
          (α_ H₁.right S₁.right
            (H₂.right ⊗ S₂.right)).inv ≫
            ((H₁.right ⊗ S₁.right) ◁ qSmash H₂ S₂) := by
      simpa only [MonoidalCategory.tensorHom_id,
        MonoidalCategory.id_tensorHom,
        MonoidalCategory.id_whiskerRight] using
        (MonoidalCategory.associator_inv_naturality
          (𝟙 H₁.right) (𝟙 S₁.right) (qSmash H₂ S₂))
    slice_lhs 5 6 =>
      rw [hNatAssocInv₄]
    simp only [Category.assoc]
    slice_lhs 6 7 =>
      rw [← MonoidalCategory.tensorHom_def']
    have hswap :
        swapRaw = (β_ H₂.right S₁.right).hom := by
      rfl
    rw [hswap]
  have epi_right_of_isPushout_of_splitEpi
      {A B X Y : CGWH.{u, v}} {t : A ⟶ B} {l : A ⟶ X}
      {r : B ⟶ Y} {b : X ⟶ Y}
      (h : IsPushout t l r b) (s : X ⟶ A)
      (hs : s ≫ l = 𝟙 X) : Epi r := by
    constructor
    intro Z f g hr
    apply h.hom_ext
    · exact hr
    · calc
        b ≫ f = (𝟙 X) ≫ b ≫ f := by simp
        _ = (s ≫ l) ≫ b ≫ f := by rw [hs]
        _ = s ≫ (l ≫ b) ≫ f := by simp only [Category.assoc]
        _ = s ≫ (t ≫ r) ≫ f := by rw [h.w]
        _ = s ≫ t ≫ (r ≫ f) := by simp only [Category.assoc]
        _ = s ≫ t ≫ (r ≫ g) := by rw [hr]
        _ = s ≫ (t ≫ r) ≫ g := by simp only [Category.assoc]
        _ = s ≫ (l ≫ b) ≫ g := by rw [h.w]
        _ = (s ≫ l) ≫ b ≫ g := by simp only [Category.assoc]
        _ = b ≫ g := by rw [hs]; simp
  have map_isPushout_of_preserves
      {A B X Y : CGWH.{u, v}} {t : A ⟶ B} {l : A ⟶ X}
      {r : B ⟶ Y} {b : X ⟶ Y}
      (F : CGWH.{u, v} ⥤ CGWH.{u, v})
      [PreservesColimit (span t l) F]
      (h : IsPushout t l r b) :
      IsPushout (F.map t) (F.map l) (F.map r) (F.map b) :=
    IsPushout.of_isColimit_cocone
      (PreservesColimit.preserves h.isColimit).some
  have map_epi_right_of_isPushout_of_splitEpi
      {A B X Y : CGWH.{u, v}} {t : A ⟶ B} {l : A ⟶ X}
      {r : B ⟶ Y} {b : X ⟶ Y}
      (F : CGWH.{u, v} ⥤ CGWH.{u, v})
      [PreservesColimit (span t l) F]
      (h : IsPushout t l r b) (s : X ⟶ A)
      (hs : s ≫ l = 𝟙 X) : Epi (F.map r) := by
    apply epi_right_of_isPushout_of_splitEpi
      (map_isPushout_of_preserves F h) (F.map s)
    rw [← F.map_comp, hs, F.map_id]
  have q_epi (X Y : PointedCGWH.{u, v}) :
      Epi (qSmash X Y) := by
    let W := ((CategoryTheory.Pointed.wedge CGWH.point).obj X).obj Y
    let c : W.right ⟶ CGWH.point.{u, v} :=
      CGWH.point_isTerminal.from W.right
    have hs : W.hom ≫ c = 𝟙 CGWH.point.{u, v} :=
      CGWH.point_isTerminal.hom_ext _ _
    exact epi_right_of_isPushout_of_splitEpi
      (IsPushout.of_isColimit_cocone
        (CategoryTheory.Pointed.smashPresentation
          CGWH.point CGWH.point_isTerminal X Y).2.2)
      W.hom hs
  have q_whisker_right_epi (X Y : PointedCGWH.{u, v})
      (T : CGWH.{u, v}) : Epi (qSmash X Y ▷ T) := by
    let W := ((CategoryTheory.Pointed.wedge CGWH.point).obj X).obj Y
    let c : W.right ⟶ CGWH.point.{u, v} :=
      CGWH.point_isTerminal.from W.right
    have hs : W.hom ≫ c = 𝟙 CGWH.point.{u, v} :=
      CGWH.point_isTerminal.hom_ext _ _
    exact map_epi_right_of_isPushout_of_splitEpi (tensorRight T)
      (IsPushout.of_isColimit_cocone
        (CategoryTheory.Pointed.smashPresentation
          CGWH.point CGWH.point_isTerminal X Y).2.2)
      W.hom hs
  have q_whisker_left_epi (T : CGWH.{u, v})
      (X Y : PointedCGWH.{u, v}) : Epi (T ◁ qSmash X Y) := by
    let W := ((CategoryTheory.Pointed.wedge CGWH.point).obj X).obj Y
    let c : W.right ⟶ CGWH.point.{u, v} :=
      CGWH.point_isTerminal.from W.right
    have hs : W.hom ≫ c = 𝟙 CGWH.point.{u, v} :=
      CGWH.point_isTerminal.hom_ext _ _
    exact map_epi_right_of_isPushout_of_splitEpi (tensorLeft T)
      (IsPushout.of_isColimit_cocone
        (CategoryTheory.Pointed.smashPresentation
          CGWH.point CGWH.point_isTerminal X Y).2.2)
      W.hom hs
  let _ : Epi ((H₁.right ⊗ H₂.right) ◁ qSmash S₁ S₂) :=
    q_whisker_left_epi (H₁.right ⊗ H₂.right) S₁ S₂
  let _ : Epi (qSmash H₁ H₂ ▷ (S₁ ⊗ S₂).right) :=
    q_whisker_right_epi H₁ H₂ (S₁ ⊗ S₂).right
  have qTensor_epi :
      Epi (qSmash H₁ H₂ ⊗ₘ qSmash S₁ S₂) := by
    rw [MonoidalCategory.tensorHom_def']
    infer_instance
  let _ : Epi (qSmash H₁ H₂ ⊗ₘ qSmash S₁ S₂) := qTensor_epi
  let _ : Epi (qSmash (H₁ ⊗ H₂) (S₁ ⊗ S₂)) :=
    q_epi (H₁ ⊗ H₂) (S₁ ⊗ S₂)
  apply Under.UnderMorphism.ext
  apply (cancel_epi ((qSmash H₁ H₂ ⊗ₘ qSmash S₁ S₂) ≫
    qSmash (H₁ ⊗ H₂) (S₁ ⊗ S₂))).1
  simp only [Under.comp_right, Category.assoc]
  have hQuotTensor : qSmash (H₁ ⊗ H₂) (S₁ ⊗ S₂) ≫
      (OrthogonalIndex.tensorMap.{u, v} m n p q ⊗ₘ
        (orthogonalSphereTensorIso.{u, v} m p).inv).right =
    ((OrthogonalIndex.tensorMap.{u, v} m n p q).right ⊗ₘ
        (orthogonalSphereTensorIso.{u, v} m p).inv.right) ≫
      qSmash Hsum Ssum :=
    CategoryTheory.Pointed.smashQuotient_naturality
      CGWH.point.{u, v} CGWH.point_isTerminal
      (OrthogonalIndex.tensorMap.{u, v} m n p q)
      (orthogonalSphereTensorIso.{u, v} m p).inv
  slice_lhs 2 3 => rw [hQuotTensor]
  have hμ' :
      ((qSmash H₁ H₂ ⊗ₘ qSmash S₁ S₂) ≫
          qSmash (H₁ ⊗ H₂) (S₁ ⊗ S₂)) ≫
          (MonoidalCategory.tensorμ
            (OrthogonalIndex.hom.{u, v} m n)
            (OrthogonalIndex.hom.{u, v} p q)
            (orthogonalSphere.{u, v} m)
            (orthogonalSphere.{u, v} p)).right =
        MonoidalCategory.tensorμ H₁.right H₂.right S₁.right S₂.right ≫
          (qSmash H₁ S₁ ⊗ₘ qSmash H₂ S₂) ≫
          qSmash (H₁ ⊗ S₁) (H₂ ⊗ S₂) := by
    rw [Category.assoc]
    exact hμ
  slice_rhs 1 3 =>
    rw [← Category.assoc, hμ']
  simp only [Category.assoc]
  have hQuotActions : qSmash (H₁ ⊗ S₁) (H₂ ⊗ S₂) ≫
      (orthogonalSphereAction.{u, v} m n ⊗ₘ
        orthogonalSphereAction.{u, v} p q).right =
    ((orthogonalSphereAction.{u, v} m n).right ⊗ₘ
        (orthogonalSphereAction.{u, v} p q).right) ≫ qSmash T₁ T₂ :=
    CategoryTheory.Pointed.smashQuotient_naturality
      CGWH.point.{u, v} CGWH.point_isTerminal
      (orthogonalSphereAction.{u, v} m n) (orthogonalSphereAction.{u, v} p q)
  slice_rhs 3 4 => rw [hQuotActions]
  apply ConcreteCategory.hom_ext
  intro z
  let RH : CGWH.{u, v} := H₁.right ⊗ H₂.right
  let RS : CGWH.{u, v} := S₁.right ⊗ S₂.right
  let zH : RH := CartesianMonoidalCategory.fst RH RS z
  let zS : RS := CartesianMonoidalCategory.snd RH RS z
  let a : H₁.right :=
    CartesianMonoidalCategory.fst H₁.right H₂.right zH
  let b : H₂.right :=
    CartesianMonoidalCategory.snd H₁.right H₂.right zH
  let x : S₁.right :=
    CartesianMonoidalCategory.fst S₁.right S₂.right zS
  let y : S₂.right :=
    CartesianMonoidalCategory.snd S₁.right S₂.right zS
  let cH : (H₁.right ⊗ H₂.right : CGWH.{u, v}) := Classical.choose
    ((CGWH.prodComparisonToTop_bijective H₁.right H₂.right).2 (a, b))
  let cS : (S₁.right ⊗ S₂.right : CGWH.{u, v}) := Classical.choose
    ((CGWH.prodComparisonToTop_bijective S₁.right S₂.right).2 (x, y))
  have hcH : CGWH.prodComparisonToTop H₁.right H₂.right cH = (a, b) :=
    Classical.choose_spec
      ((CGWH.prodComparisonToTop_bijective H₁.right H₂.right).2 (a, b))
  have hcS : CGWH.prodComparisonToTop S₁.right S₂.right cS = (x, y) :=
    Classical.choose_spec
      ((CGWH.prodComparisonToTop_bijective S₁.right S₂.right).2 (x, y))
  have hcH_fst :
      CartesianMonoidalCategory.fst H₁.right H₂.right cH = a := by
    have h := ConcreteCategory.congr_hom
      (CGWH.prodComparisonToTop_fst H₁.right H₂.right) cH
    change (CGWH.prodComparisonToTop H₁.right H₂.right cH).1 =
      CartesianMonoidalCategory.fst H₁.right H₂.right cH at h
    exact h.symm.trans (congrArg Prod.fst hcH)
  have hcH_snd :
      CartesianMonoidalCategory.snd H₁.right H₂.right cH = b := by
    have h := ConcreteCategory.congr_hom
      (CGWH.prodComparisonToTop_snd H₁.right H₂.right) cH
    change (CGWH.prodComparisonToTop H₁.right H₂.right cH).2 =
      CartesianMonoidalCategory.snd H₁.right H₂.right cH at h
    exact h.symm.trans (congrArg Prod.snd hcH)
  have hcS_fst :
      CartesianMonoidalCategory.fst S₁.right S₂.right cS = x := by
    have h := ConcreteCategory.congr_hom
      (CGWH.prodComparisonToTop_fst S₁.right S₂.right) cS
    change (CGWH.prodComparisonToTop S₁.right S₂.right cS).1 =
      CartesianMonoidalCategory.fst S₁.right S₂.right cS at h
    exact h.symm.trans (congrArg Prod.fst hcS)
  have hcS_snd :
      CartesianMonoidalCategory.snd S₁.right S₂.right cS = y := by
    have h := ConcreteCategory.congr_hom
      (CGWH.prodComparisonToTop_snd S₁.right S₂.right) cS
    change (CGWH.prodComparisonToTop S₁.right S₂.right cS).2 =
      CartesianMonoidalCategory.snd S₁.right S₂.right cS at h
    exact h.symm.trans (congrArg Prod.snd hcS)
  let cOuter : (RH ⊗ RS : CGWH.{u, v}) := Classical.choose
    ((CGWH.prodComparisonToTop_bijective RH RS).2 (cH, cS))
  have hzH : zH = cH := by
    apply (CGWH.prodComparisonToTop_bijective H₁.right H₂.right).1
    have hp : CGWH.prodComparisonToTop H₁.right H₂.right zH = (a, b) := by
      apply Prod.ext
      · have h := ConcreteCategory.congr_hom
          (CGWH.prodComparisonToTop_fst H₁.right H₂.right) zH
        change (CGWH.prodComparisonToTop H₁.right H₂.right zH).1 =
          CartesianMonoidalCategory.fst H₁.right H₂.right zH at h
        exact h
      · have h := ConcreteCategory.congr_hom
          (CGWH.prodComparisonToTop_snd H₁.right H₂.right) zH
        change (CGWH.prodComparisonToTop H₁.right H₂.right zH).2 =
          CartesianMonoidalCategory.snd H₁.right H₂.right zH at h
        exact h
    exact hp.trans hcH.symm
  have hzS : zS = cS := by
    apply (CGWH.prodComparisonToTop_bijective S₁.right S₂.right).1
    have hp : CGWH.prodComparisonToTop S₁.right S₂.right zS = (x, y) := by
      apply Prod.ext
      · have h := ConcreteCategory.congr_hom
          (CGWH.prodComparisonToTop_fst S₁.right S₂.right) zS
        change (CGWH.prodComparisonToTop S₁.right S₂.right zS).1 =
          CartesianMonoidalCategory.fst S₁.right S₂.right zS at h
        exact h
      · have h := ConcreteCategory.congr_hom
          (CGWH.prodComparisonToTop_snd S₁.right S₂.right) zS
        change (CGWH.prodComparisonToTop S₁.right S₂.right zS).2 =
          CartesianMonoidalCategory.snd S₁.right S₂.right zS at h
        exact h
    exact hp.trans hcS.symm
  have hz : z = cOuter := by
    apply (CGWH.prodComparisonToTop_bijective RH RS).1
    have hc : CGWH.prodComparisonToTop RH RS cOuter = (cH, cS) :=
      Classical.choose_spec
        ((CGWH.prodComparisonToTop_bijective RH RS).2 (cH, cS))
    rw [hc]
    apply Prod.ext
    · have h := ConcreteCategory.congr_hom
        (CGWH.prodComparisonToTop_fst RH RS) z
      change (CGWH.prodComparisonToTop RH RS z).1 =
        CartesianMonoidalCategory.fst RH RS z at h
      exact h.trans hzH
    · have h := ConcreteCategory.congr_hom
        (CGWH.prodComparisonToTop_snd RH RS) z
      change (CGWH.prodComparisonToTop RH RS z).2 =
        CartesianMonoidalCategory.snd RH RS z at h
      exact h.trans hzS
  let cAX : (H₁.right ⊗ S₁.right : CGWH.{u, v}) := Classical.choose
    ((CGWH.prodComparisonToTop_bijective H₁.right S₁.right).2 (a, x))
  let cBY : (H₂.right ⊗ S₂.right : CGWH.{u, v}) := Classical.choose
    ((CGWH.prodComparisonToTop_bijective H₂.right S₂.right).2 (b, y))
  let cPairs : ((H₁.right ⊗ S₁.right) ⊗ (H₂.right ⊗ S₂.right) : CGWH.{u, v}) :=
    Classical.choose
      ((CGWH.prodComparisonToTop_bijective
        (H₁.right ⊗ S₁.right) (H₂.right ⊗ S₂.right)).2 (cAX, cBY))
  have hμPoint :
      MonoidalCategory.tensorμ H₁.right H₂.right S₁.right S₂.right cOuter =
        cPairs := by
    apply (CGWH.prodComparisonToTop_bijective
      (H₁.right ⊗ S₁.right) (H₂.right ⊗ S₂.right)).1
    have hcPairs : CGWH.prodComparisonToTop
        (H₁.right ⊗ S₁.right) (H₂.right ⊗ S₂.right) cPairs =
          (cAX, cBY) :=
      Classical.choose_spec
        ((CGWH.prodComparisonToTop_bijective
          (H₁.right ⊗ S₁.right) (H₂.right ⊗ S₂.right)).2
            (cAX, cBY))
    rw [hcPairs]
    apply Prod.ext
    · have hfst := ConcreteCategory.congr_hom
        (CGWH.prodComparisonToTop_fst
          (H₁.right ⊗ S₁.right) (H₂.right ⊗ S₂.right))
        (MonoidalCategory.tensorμ H₁.right H₂.right
          S₁.right S₂.right cOuter)
      change (CGWH.prodComparisonToTop
          (H₁.right ⊗ S₁.right) (H₂.right ⊗ S₂.right)
          (MonoidalCategory.tensorμ H₁.right H₂.right S₁.right S₂.right cOuter)).1 =
        CartesianMonoidalCategory.fst (H₁.right ⊗ S₁.right) (H₂.right ⊗ S₂.right)
          (MonoidalCategory.tensorμ H₁.right H₂.right S₁.right S₂.right cOuter) at hfst
      have hμfst :
          CartesianMonoidalCategory.fst (H₁.right ⊗ S₁.right) (H₂.right ⊗ S₂.right)
              (MonoidalCategory.tensorμ H₁.right H₂.right S₁.right S₂.right cOuter) =
            ((CartesianMonoidalCategory.fst H₁.right H₂.right) ⊗ₘ
              (CartesianMonoidalCategory.fst S₁.right S₂.right)) cOuter := by
        have h := ConcreteCategory.congr_hom
          (CartesianMonoidalCategory.tensorμ_fst
            H₁.right H₂.right S₁.right S₂.right) cOuter
        change CartesianMonoidalCategory.fst
            (H₁.right ⊗ S₁.right) (H₂.right ⊗ S₂.right)
            (MonoidalCategory.tensorμ H₁.right H₂.right S₁.right S₂.right cOuter) =
          ((CartesianMonoidalCategory.fst H₁.right H₂.right) ⊗ₘ
            (CartesianMonoidalCategory.fst S₁.right S₂.right)) cOuter at h
        exact h
      have hmap :
          ((CartesianMonoidalCategory.fst H₁.right H₂.right) ⊗ₘ
            (CartesianMonoidalCategory.fst S₁.right S₂.right)) cOuter = cAX := by
        change
          ((CartesianMonoidalCategory.fst H₁.right H₂.right) ⊗ₘ
            (CartesianMonoidalCategory.fst S₁.right S₂.right))
              (Classical.choose
                ((CGWH.prodComparisonToTop_bijective RH RS).2 (cH, cS))) =
            Classical.choose
              ((CGWH.prodComparisonToTop_bijective H₁.right S₁.right).2 (a, x))
        have hPair :
            (CartesianMonoidalCategory.fst H₁.right H₂.right cH,
              CartesianMonoidalCategory.fst S₁.right S₂.right cS) = (a, x) :=
          Prod.ext hcH_fst hcS_fst
        have hTarget := congrArg
          (fun z : H₁.right × S₁.right ↦ Classical.choose
            ((CGWH.prodComparisonToTop_bijective H₁.right S₁.right).2 z)) hPair
        exact (nativeProductMap_choose (A := RH) (B := RS)
          (A' := H₁.right) (B' := S₁.right)
          (CartesianMonoidalCategory.fst H₁.right H₂.right)
          (CartesianMonoidalCategory.fst S₁.right S₂.right) cH cS).trans hTarget
      exact hfst.trans (hμfst.trans hmap)
    · have hsnd := ConcreteCategory.congr_hom
        (CGWH.prodComparisonToTop_snd
          (H₁.right ⊗ S₁.right) (H₂.right ⊗ S₂.right))
        (MonoidalCategory.tensorμ H₁.right H₂.right
          S₁.right S₂.right cOuter)
      change (CGWH.prodComparisonToTop
          (H₁.right ⊗ S₁.right) (H₂.right ⊗ S₂.right)
          (MonoidalCategory.tensorμ H₁.right H₂.right S₁.right S₂.right cOuter)).2 =
        CartesianMonoidalCategory.snd (H₁.right ⊗ S₁.right) (H₂.right ⊗ S₂.right)
          (MonoidalCategory.tensorμ H₁.right H₂.right S₁.right S₂.right cOuter) at hsnd
      have hμsnd :
          CartesianMonoidalCategory.snd (H₁.right ⊗ S₁.right) (H₂.right ⊗ S₂.right)
              (MonoidalCategory.tensorμ H₁.right H₂.right S₁.right S₂.right cOuter) =
            ((CartesianMonoidalCategory.snd H₁.right H₂.right) ⊗ₘ
              (CartesianMonoidalCategory.snd S₁.right S₂.right)) cOuter := by
        have h := ConcreteCategory.congr_hom
          (CartesianMonoidalCategory.tensorμ_snd
            H₁.right H₂.right S₁.right S₂.right) cOuter
        change CartesianMonoidalCategory.snd
            (H₁.right ⊗ S₁.right) (H₂.right ⊗ S₂.right)
            (MonoidalCategory.tensorμ H₁.right H₂.right S₁.right S₂.right cOuter) =
          ((CartesianMonoidalCategory.snd H₁.right H₂.right) ⊗ₘ
            (CartesianMonoidalCategory.snd S₁.right S₂.right)) cOuter at h
        exact h
      have hmap :
          ((CartesianMonoidalCategory.snd H₁.right H₂.right) ⊗ₘ
            (CartesianMonoidalCategory.snd S₁.right S₂.right)) cOuter = cBY := by
        change
          ((CartesianMonoidalCategory.snd H₁.right H₂.right) ⊗ₘ
            (CartesianMonoidalCategory.snd S₁.right S₂.right))
              (Classical.choose
                ((CGWH.prodComparisonToTop_bijective RH RS).2 (cH, cS))) =
            Classical.choose
              ((CGWH.prodComparisonToTop_bijective H₂.right S₂.right).2 (b, y))
        have hPair :
            (CartesianMonoidalCategory.snd H₁.right H₂.right cH,
              CartesianMonoidalCategory.snd S₁.right S₂.right cS) = (b, y) :=
          Prod.ext hcH_snd hcS_snd
        have hTarget := congrArg
          (fun z : H₂.right × S₂.right ↦ Classical.choose
            ((CGWH.prodComparisonToTop_bijective H₂.right S₂.right).2 z)) hPair
        exact (nativeProductMap_choose (A := RH) (B := RS)
          (A' := H₂.right) (B' := S₂.right)
          (CartesianMonoidalCategory.snd H₁.right H₂.right)
          (CartesianMonoidalCategory.snd S₁.right S₂.right) cH cS).trans hTarget
      exact hsnd.trans (hμsnd.trans hmap)
  let cHS : ((H₁ ⊗ H₂).right ⊗ (S₁ ⊗ S₂).right : CGWH.{u, v}) :=
    Classical.choose
      ((CGWH.prodComparisonToTop_bijective
        (H₁ ⊗ H₂).right (S₁ ⊗ S₂).right).2
          (qSmash H₁ H₂ cH, qSmash S₁ S₂ cS))
  have hHS :
      (qSmash H₁ H₂ ⊗ₘ qSmash S₁ S₂) cOuter = cHS := by
    exact nativeProductMap_choose
      (qSmash H₁ H₂) (qSmash S₁ S₂) cH cS
  let tensorMap := OrthogonalIndex.tensorMap.{u, v} m n p q
  let deltaIn := orthogonalSphereTensorIso.{u, v} m p
  let deltaOut := orthogonalSphereTensorIso.{u, v} n q
  let param : Hsum.right := tensorMap.right (qSmash H₁ H₂ cH)
  let sphere : Ssum.right := deltaIn.inv.right (qSmash S₁ S₂ cS)
  let cParamSphere : (Hsum.right ⊗ Ssum.right : CGWH.{u, v}) := Classical.choose
    ((CGWH.prodComparisonToTop_bijective Hsum.right Ssum.right).2
      (param, sphere))
  have hParamSphere :
      (tensorMap.right ⊗ₘ deltaIn.inv.right) cHS = cParamSphere := by
    exact nativeProductMap_choose tensorMap.right deltaIn.inv.right
      (qSmash H₁ H₂ cH) (qSmash S₁ S₂ cS)
  let outSum : (orthogonalSphere.{u, v} (n + q)).right :=
    (orthogonalSphereAction.{u, v} (m + p) (n + q)).right
      (qSmash Hsum Ssum cParamSphere)
  let leftOut : (T₁ ⊗ T₂).right := deltaOut.hom.right outSum
  let action₁ : (T₁).right :=
    (orthogonalSphereAction.{u, v} m n).right (qSmash H₁ S₁ cAX)
  let action₂ : (T₂).right :=
    (orthogonalSphereAction.{u, v} p q).right (qSmash H₂ S₂ cBY)
  let cActions : (T₁.right ⊗ T₂.right : CGWH.{u, v}) := Classical.choose
    ((CGWH.prodComparisonToTop_bijective T₁.right T₂.right).2
      (action₁, action₂))
  let cPairSmashes : ((H₁ ⊗ S₁).right ⊗ (H₂ ⊗ S₂).right : CGWH.{u, v}) := Classical.choose
    ((CGWH.prodComparisonToTop_bijective
      (H₁ ⊗ S₁).right (H₂ ⊗ S₂).right).2
        (qSmash H₁ S₁ cAX, qSmash H₂ S₂ cBY))
  have hPairSmashes :
      (qSmash H₁ S₁ ⊗ₘ qSmash H₂ S₂) cPairs = cPairSmashes := by
    exact nativeProductMap_choose
      (qSmash H₁ S₁) (qSmash H₂ S₂) cAX cBY
  have hActions :
      ((orthogonalSphereAction.{u, v} m n).right ⊗ₘ
        (orthogonalSphereAction.{u, v} p q).right) cPairSmashes =
          cActions := by
    exact nativeProductMap_choose
      (orthogonalSphereAction.{u, v} m n).right
      (orthogonalSphereAction.{u, v} p q).right
      (qSmash H₁ S₁ cAX) (qSmash H₂ S₂ cBY)
  have pointTensor_free {X Y : PointedCGWH.{u, v}}
      (f : 𝟙_ PointedCGWH.{u, v} ⟶ X)
      (g : 𝟙_ PointedCGWH.{u, v} ⟶ Y) :
      let t : (𝟙_ PointedCGWH.{u, v}).right :=
        (coprod.inr : CGWH.point.{u, v} ⟶
          CGWH.point.{u, v} ⨿ CGWH.point.{u, v}) PUnit.unit
      let c := Classical.choose
        ((CGWH.prodComparisonToTop_bijective X.right Y.right).2
          (f.right t, g.right t))
      ((λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫ (f ⊗ₘ g)).right t =
        qSmash X Y c := by
    dsimp only
    let P := CGWH.point.{u, v}
    let hP := CGWH.point_isTerminal.{u, v}
    let I := 𝟙_ PointedCGWH.{u, v}
    let unitPoint : P := by
      change PUnit.{v + 1}
      exact PUnit.unit
    let t : I.right :=
      (coprod.inr : P ⟶ P ⨿ P) unitPoint
    let cI := Classical.choose
      ((CGWH.prodComparisonToTop_bijective I.right I.right).2 (t, t))
    let c := Classical.choose
      ((CGWH.prodComparisonToTop_bijective X.right Y.right).2
        (f.right t, g.right t))
    let qI : I.right ⊗ I.right ⟶ (I ⊗ I).right :=
      (CategoryTheory.Pointed.smashPresentation P hP I I).2.1.inl
    let pIso := hP.uniqueUpToIso
      CartesianMonoidalCategory.isTerminalTensorUnit
    let freeMap : P ⟶ I.right := coprod.inr
    let w0 := (λ_ I.right).inv t
    let w1 := (pIso.inv ▷ I.right) w0
    let cStruct := (freeMap ▷ I.right) w1
    let cStruct' : (CGWH.cgwhToTop.obj (I.right ⨯ I.right) : Type v) :=
      cStruct
    have hcStruct' : cStruct' = cI := by
      apply (CGWH.prodComparisonToTop_bijective I.right I.right).1
      have hchoose : CGWH.prodComparisonToTop I.right I.right cI =
          (t, t) :=
        Classical.choose_spec
          ((CGWH.prodComparisonToTop_bijective I.right I.right).2 (t, t))
      rw [hchoose]
      apply Prod.ext
      · have hfst := ConcreteCategory.congr_hom
          (CGWH.prodComparisonToTop_fst I.right I.right) cStruct'
        rw [ConcreteCategory.comp_apply] at hfst
        change (ConcreteCategory.hom TopCat.prodFst
          (CGWH.prodComparisonToTop I.right I.right cStruct')) = t
        rw [hfst]
        change CartesianMonoidalCategory.fst I.right I.right
            ((freeMap ⊗ₘ 𝟙 I.right) w1) = t
        have h1 := ConcreteCategory.congr_hom
          (CartesianMonoidalCategory.tensorHom_fst freeMap (𝟙 I.right))
            ((pIso.inv ⊗ₘ 𝟙 I.right) ((λ_ I.right).inv t))
        have h0 := ConcreteCategory.congr_hom
          (CartesianMonoidalCategory.tensorHom_fst pIso.inv (𝟙 I.right))
            ((λ_ I.right).inv t)
        have hu := ConcreteCategory.congr_hom
          (CartesianMonoidalCategory.leftUnitor_inv_fst I.right) t
        simp only [ConcreteCategory.comp_apply] at h1 h0 hu
        dsimp only [w1, w0]
        change CartesianMonoidalCategory.fst I.right I.right
            ((freeMap ⊗ₘ 𝟙 I.right)
              ((pIso.inv ⊗ₘ 𝟙 I.right) ((λ_ I.right).inv t))) = t
        rw [h1, h0, hu]
        rfl
      · have hsnd := ConcreteCategory.congr_hom
          (CGWH.prodComparisonToTop_snd I.right I.right) cStruct'
        rw [ConcreteCategory.comp_apply] at hsnd
        change (ConcreteCategory.hom TopCat.prodSnd
          (CGWH.prodComparisonToTop I.right I.right cStruct')) = t
        rw [hsnd]
        change CartesianMonoidalCategory.snd I.right I.right
            ((freeMap ⊗ₘ 𝟙 I.right) w1) = t
        have h1 := ConcreteCategory.congr_hom
          (CartesianMonoidalCategory.tensorHom_snd freeMap (𝟙 I.right))
            ((pIso.inv ⊗ₘ 𝟙 I.right) ((λ_ I.right).inv t))
        have h0 := ConcreteCategory.congr_hom
          (CartesianMonoidalCategory.tensorHom_snd pIso.inv (𝟙 I.right))
            ((λ_ I.right).inv t)
        have hu := ConcreteCategory.congr_hom
          (CartesianMonoidalCategory.leftUnitor_inv_snd I.right) t
        simp only [ConcreteCategory.comp_apply, Category.comp_id] at h1 h0 hu
        dsimp only [w1, w0]
        change CartesianMonoidalCategory.snd I.right I.right
            ((freeMap ⊗ₘ 𝟙 I.right)
              ((pIso.inv ⊗ₘ 𝟙 I.right) ((λ_ I.right).inv t))) = t
        rw [h1, h0, hu]
        rfl
    have hcStruct : cStruct = cI := hcStruct'
    have hFree := ConcreteCategory.congr_hom
      (CategoryTheory.Pointed.smashLeftUnitor_inv_free P hP I) t
    have hFreeAt : (λ_ I).inv.right t = qI cStruct := hFree
    have hqI : qI cI = (λ_ I).inv.right t := by
      rw [← hcStruct]
      exact hFreeAt.symm
    have hnat := ConcreteCategory.congr_hom
      (CategoryTheory.Pointed.smashQuotient_naturality P hP f g) cI
    change (f ⊗ₘ g).right (qI cI) =
      qSmash X Y ((f.right ⊗ₘ g.right) cI) at hnat
    have hc : (f.right ⊗ₘ g.right) cI = c := by
      exact nativeProductMap_choose f.right g.right t t
    change (f ⊗ₘ g).right ((λ_ I).inv.right t) = _
    exact (congrArg (fun x => (f ⊗ₘ g).right x) hqI.symm).trans
      (hnat.trans (congrArg (qSmash X Y) hc))
  let unitPoint : CGWH.point.{u, v} := by
    change PUnit.{v + 1}
    exact PUnit.unit
  let t : (𝟙_ PointedCGWH.{u, v}).right :=
    (coprod.inr : CGWH.point.{u, v} ⟶
      CGWH.point.{u, v} ⨿ CGWH.point.{u, v}) unitPoint
  have preservesBase {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
      f.right (X.hom unitPoint) = Y.hom unitPoint := by
    have h := ConcreteCategory.congr_hom (Under.w f) unitPoint
    change f.right (X.hom unitPoint) = Y.hom unitPoint at h
    exact h
  have zero_free (X : PointedCGWH.{u, v}) :
      (0 : 𝟙_ PointedCGWH.{u, v} ⟶ X).right t =
        X.hom PUnit.unit := by
    let pointZero : PointedCGWH.{u, v} :=
      Under.mk (𝟙 CGWH.point.{u, v})
    have pointZeroIsZero : IsZero pointZero :=
      { unique_to := fun T ↦
          ⟨{ default := Under.mkIdInitial.to T
             uniq := fun g ↦ Under.mkIdInitial.hom_ext g _ }⟩
        unique_from := fun T ↦
          ⟨{ default := Under.homMk
                (CGWH.point_isTerminal.from T.right)
                (CGWH.point_isTerminal.hom_ext _ _)
             uniq := fun g ↦ Under.UnderMorphism.ext
               (CGWH.point_isTerminal.hom_ext g.right _) }⟩ }
    let zeroPointedIso : (0 : PointedCGWH.{u, v}) ≅ pointZero :=
      (isZero_zero PointedCGWH.{u, v}).iso pointZeroIsZero
    let zeroRightIso :
        (0 : PointedCGWH.{u, v}).right ≅ CGWH.point.{u, v} :=
      { hom := zeroPointedIso.hom.right
        inv := zeroPointedIso.inv.right
        hom_inv_id := congrArg (fun g ↦ g.right)
          zeroPointedIso.hom_inv_id
        inv_hom_id := congrArg (fun g ↦ g.right)
          zeroPointedIso.inv_hom_id }
    have zeroRightIsTerminal : IsTerminal
        ((0 : PointedCGWH.{u, v}).right) :=
      IsTerminal.ofIso CGWH.point_isTerminal zeroRightIso.symm
    let freeGenerator : CGWH.point.{u, v} ⟶
        (𝟙_ PointedCGWH.{u, v}).right := coprod.inr
    have hzero : freeGenerator ≫
          (0 : 𝟙_ PointedCGWH.{u, v} ⟶ X).right = X.hom := by
      change freeGenerator ≫
          ((default : 𝟙_ PointedCGWH.{u, v} ⟶
            (0 : PointedCGWH.{u, v})).right ≫
          (default : (0 : PointedCGWH.{u, v}) ⟶ X).right) = _
      rw [← Category.assoc]
      have hfirst : freeGenerator ≫
          (default : 𝟙_ PointedCGWH.{u, v} ⟶
            (0 : PointedCGWH.{u, v})).right =
          (0 : PointedCGWH.{u, v}).hom :=
        zeroRightIsTerminal.hom_ext _ _
      rw [hfirst]
      exact Under.w (default : (0 : PointedCGWH.{u, v}) ⟶ X)
    have h := ConcreteCategory.congr_hom hzero unitPoint
    change (0 : 𝟙_ PointedCGWH.{u, v} ⟶ X).right t = X.hom unitPoint at h
    exact h
  let pointMap (X : PointedCGWH.{u, v}) (x : X.right) :
      𝟙_ PointedCGWH.{u, v} ⟶ X :=
    Under.homMk
      (coprod.desc X.hom ((CGWH.pointHomEquiv X.right).symm x))
      (by
        have hunit : (𝟙_ PointedCGWH.{u, v}).hom =
            (coprod.inl : CGWH.point.{u, v} ⟶
              CGWH.point.{u, v} ⨿ CGWH.point.{u, v}) := by
          change ((Under.costar CGWH.point.{u, v}).obj CGWH.point.{u, v}).hom = _
          exact (Under.costar_obj_hom CGWH.point CGWH.point).trans (coprod.inl_desc _ _)
        exact (congrArg (fun h => h ≫
          coprod.desc X.hom ((CGWH.pointHomEquiv X.right).symm x)) hunit).trans
            (coprod.inl_desc _ _))
  have pointMap_free (X : PointedCGWH.{u, v}) (x : X.right) :
      (pointMap X x).right t = x := by
    let f : CGWH.point.{u, v} ⟶ X.right := (CGWH.pointHomEquiv X.right).symm x
    have hDesc : (coprod.inr : CGWH.point.{u, v} ⟶
        CGWH.point.{u, v} ⨿ CGWH.point.{u, v}) ≫ coprod.desc X.hom f = f :=
      coprod.inr_desc _ _
    have h := ConcreteCategory.congr_hom hDesc unitPoint
    change (pointMap X x).right t = f unitPoint at h
    exact h.trans (CGWH.pointHomEquiv_symm_apply_apply X.right x unitPoint)
  have q_left_base (X Y : PointedCGWH.{u, v}) (y : Y.right) :
      let c := Classical.choose
        ((CGWH.prodComparisonToTop_bijective X.right Y.right).2
          (X.hom PUnit.unit, y))
      qSmash X Y c = (X ⊗ Y).hom PUnit.unit := by
    dsimp only
    let py := pointMap Y y
    let c₀ := Classical.choose
      ((CGWH.prodComparisonToTop_bijective X.right Y.right).2
        ((0 : 𝟙_ PointedCGWH.{u, v} ⟶ X).right t, py.right t))
    let c := Classical.choose
      ((CGWH.prodComparisonToTop_bijective X.right Y.right).2
        (X.hom PUnit.unit, y))
    have hc : c₀ = c := by
      dsimp only [c₀, c]
      rw [zero_free X, pointMap_free]
    have hp := pointTensor_free
      (0 : 𝟙_ PointedCGWH.{u, v} ⟶ X) py
    change ((λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫
        ((0 : 𝟙_ PointedCGWH.{u, v} ⟶ X) ⊗ₘ py)).right t =
      qSmash X Y c₀ at hp
    have hz :
        (λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫
            ((0 : 𝟙_ PointedCGWH.{u, v} ⟶ X) ⊗ₘ py) =
          (0 : 𝟙_ PointedCGWH.{u, v} ⟶ X ⊗ Y) := by
      have ht :
          ((0 : 𝟙_ PointedCGWH.{u, v} ⟶ X) ⊗ₘ py) = 0 := by
        let _ : (tensorRight
            (𝟙_ PointedCGWH.{u, v})).PreservesZeroMorphisms :=
          inferInstance
        rw [MonoidalCategory.tensorHom_def]
        change (tensorRight (𝟙_ PointedCGWH.{u, v})).map 0 ≫ _ = 0
        rw [Functor.map_zero, zero_comp]
      rw [ht, comp_zero]
    have hze := ConcreteCategory.congr_hom
      (congrArg Under.Hom.right hz) t
    calc
      qSmash X Y c = qSmash X Y c₀ := congrArg (qSmash X Y) hc.symm
      _ = ((λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫
          ((0 : 𝟙_ PointedCGWH.{u, v} ⟶ X) ⊗ₘ py)).right t :=
        hp.symm
      _ = (0 : 𝟙_ PointedCGWH.{u, v} ⟶ X ⊗ Y).right t := hze
      _ = (X ⊗ Y).hom PUnit.unit := zero_free (X ⊗ Y)
  have q_right_base (X Y : PointedCGWH.{u, v}) (x : X.right) :
      let c := Classical.choose
        ((CGWH.prodComparisonToTop_bijective X.right Y.right).2
          (x, Y.hom PUnit.unit))
      qSmash X Y c = (X ⊗ Y).hom PUnit.unit := by
    dsimp only
    let px := pointMap X x
    let c₀ := Classical.choose
      ((CGWH.prodComparisonToTop_bijective X.right Y.right).2
        (px.right t, (0 : 𝟙_ PointedCGWH.{u, v} ⟶ Y).right t))
    let c := Classical.choose
      ((CGWH.prodComparisonToTop_bijective X.right Y.right).2
        (x, Y.hom PUnit.unit))
    have hc : c₀ = c := by
      dsimp only [c₀, c]
      rw [pointMap_free, zero_free Y]
    have hp := pointTensor_free px
      (0 : 𝟙_ PointedCGWH.{u, v} ⟶ Y)
    change ((λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫
        (px ⊗ₘ (0 : 𝟙_ PointedCGWH.{u, v} ⟶ Y))).right t =
      qSmash X Y c₀ at hp
    have hz :
        (λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫
            (px ⊗ₘ (0 : 𝟙_ PointedCGWH.{u, v} ⟶ Y)) =
          (0 : 𝟙_ PointedCGWH.{u, v} ⟶ X ⊗ Y) := by
      have ht :
          (px ⊗ₘ (0 : 𝟙_ PointedCGWH.{u, v} ⟶ Y)) = 0 := by
        let _ : (tensorLeft
            (𝟙_ PointedCGWH.{u, v})).PreservesZeroMorphisms :=
          inferInstance
        rw [MonoidalCategory.tensorHom_def']
        change (tensorLeft (𝟙_ PointedCGWH.{u, v})).map 0 ≫ _ = 0
        rw [Functor.map_zero, zero_comp]
      rw [ht, comp_zero]
    have hze := ConcreteCategory.congr_hom
      (congrArg Under.Hom.right hz) t
    calc
      qSmash X Y c = qSmash X Y c₀ := congrArg (qSmash X Y) hc.symm
      _ = ((λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫
          (px ⊗ₘ (0 : 𝟙_ PointedCGWH.{u, v} ⟶ Y))).right t :=
        hp.symm
      _ = (0 : 𝟙_ PointedCGWH.{u, v} ⟶ X ⊗ Y).right t := hze
      _ = (X ⊗ Y).hom PUnit.unit := zero_free (X ⊗ Y)
  have isoHom_injective {X Y : PointedCGWH.{u, v}} (e : X ≅ Y) :
      Function.Injective (ConcreteCategory.hom e.hom.right) := by
    intro x₁ x₂ h
    have h' := congrArg (ConcreteCategory.hom e.inv.right) h
    have h₁ := ConcreteCategory.congr_hom
      (congrArg Under.Hom.right e.hom_inv_id) x₁
    have h₂ := ConcreteCategory.congr_hom
      (congrArg Under.Hom.right e.hom_inv_id) x₂
    simp only [Under.comp_right, ConcreteCategory.comp_apply,
      Under.id_right, ConcreteCategory.id_apply] at h₁ h₂
    exact h₁.symm.trans (h'.trans h₂)
  have homPoint_cases (i j : OrthogonalIndex)
      (y : (OrthogonalIndex.hom.{u, v} i j).right) :
      y = (OrthogonalIndex.hom.{u, v} i j).hom PUnit.unit ∨
        ∃ A : OrthogonalMatrixHom i j,
          y = (OrthogonalIndex.matrixPoint.{u, v} A).right t := by
    let _ : CompactSpace (liftedMatrix.{v} i j) := inferInstance
    let _ : LocallyCompactSpace (liftedMatrix.{v} i j) := inferInstance
    let I := homToOnePointIso.{u, v} i j
    generalize hy : I.hom.right y = z'
    induction z' using OnePoint.rec with
    | infty =>
        left
        apply isoHom_injective I
        rw [hy]
        have hbase : I.hom.right
            ((OrthogonalIndex.hom.{u, v} i j).hom PUnit.unit) =
              OnePoint.infty := by
          have h := ConcreteCategory.congr_hom (Under.w I.hom) unitPoint
          change I.hom.right ((OrthogonalIndex.hom.{u, v} i j).hom unitPoint) =
            (onePointOf.{u, v} (liftedMatrix.{v} i j)).hom unitPoint at h
          exact h
        exact hbase.symm
    | coe y' =>
        rcases y' with ⟨A⟩
        right
        refine ⟨A, ?_⟩
        apply isoHom_injective I
        rw [hy]
        exact (homToOnePointIso_matrixPoint.{u, v} A).symm
  rw [hz]
  change deltaOut.hom.right ((orthogonalSphereAction.{u, v} (m + p) (n + q)).right
      (qSmash Hsum Ssum ((tensorMap.right ⊗ₘ deltaIn.inv.right)
        ((qSmash H₁ H₂ ⊗ₘ qSmash S₁ S₂) cOuter)))) =
    qSmash T₁ T₂
      (((orthogonalSphereAction.{u, v} m n).right ⊗ₘ
          (orthogonalSphereAction.{u, v} p q).right)
        ((qSmash H₁ S₁ ⊗ₘ qSmash H₂ S₂)
          (MonoidalCategory.tensorμ H₁.right H₂.right S₁.right S₂.right cOuter)))
  rw [hHS, hParamSphere, hμPoint, hPairSmashes, hActions]
  change leftOut = qSmash T₁ T₂ cActions
  rcases homPoint_cases m n a with ha | ⟨A, ha⟩
  · have hqH : qSmash H₁ H₂ cH =
        (H₁ ⊗ H₂).hom PUnit.unit := by
      dsimp only [cH]
      rw [ha]
      exact q_left_base H₁ H₂ b
    have hparam : param = Hsum.hom PUnit.unit := by
      dsimp only [param]
      rw [hqH]
      exact preservesBase tensorMap
    have hqParam : qSmash Hsum Ssum cParamSphere =
        (Hsum ⊗ Ssum).hom PUnit.unit := by
      dsimp only [cParamSphere]
      rw [hparam]
      exact q_left_base Hsum Ssum sphere
    have hout : outSum =
        (orthogonalSphere.{u, v} (n + q)).hom PUnit.unit := by
      dsimp only [outSum]
      rw [hqParam]
      exact preservesBase (orthogonalSphereAction.{u, v} (m + p) (n + q))
    have hleft : leftOut = (T₁ ⊗ T₂).hom PUnit.unit := by
      dsimp only [leftOut]
      rw [hout]
      exact preservesBase deltaOut.hom
    have hqAX : qSmash H₁ S₁ cAX =
        (H₁ ⊗ S₁).hom PUnit.unit := by
      dsimp only [cAX]
      rw [ha]
      exact q_left_base H₁ S₁ x
    have haction₁ : action₁ = T₁.hom PUnit.unit := by
      dsimp only [action₁]
      rw [hqAX]
      exact preservesBase (orthogonalSphereAction.{u, v} m n)
    have hright : qSmash T₁ T₂ cActions =
        (T₁ ⊗ T₂).hom PUnit.unit := by
      dsimp only [cActions]
      rw [haction₁]
      exact q_left_base T₁ T₂ action₂
    exact hleft.trans hright.symm
  · rcases homPoint_cases p q b with hb | ⟨B, hb⟩
    · have hqH : qSmash H₁ H₂ cH =
          (H₁ ⊗ H₂).hom PUnit.unit := by
        dsimp only [cH]
        rw [hb]
        exact q_right_base H₁ H₂ a
      have hparam : param = Hsum.hom PUnit.unit := by
        dsimp only [param]
        rw [hqH]
        exact preservesBase tensorMap
      have hqParam : qSmash Hsum Ssum cParamSphere =
          (Hsum ⊗ Ssum).hom PUnit.unit := by
        dsimp only [cParamSphere]
        rw [hparam]
        exact q_left_base Hsum Ssum sphere
      have hout : outSum =
          (orthogonalSphere.{u, v} (n + q)).hom PUnit.unit := by
        dsimp only [outSum]
        rw [hqParam]
        exact preservesBase (orthogonalSphereAction.{u, v} (m + p) (n + q))
      have hleft : leftOut = (T₁ ⊗ T₂).hom PUnit.unit := by
        dsimp only [leftOut]
        rw [hout]
        exact preservesBase deltaOut.hom
      have hqBY : qSmash H₂ S₂ cBY =
          (H₂ ⊗ S₂).hom PUnit.unit := by
        dsimp only [cBY]
        rw [hb]
        exact q_left_base H₂ S₂ y
      have haction₂ : action₂ = T₂.hom PUnit.unit := by
        dsimp only [action₂]
        rw [hqBY]
        exact preservesBase (orthogonalSphereAction.{u, v} p q)
      have hright : qSmash T₁ T₂ cActions =
          (T₁ ⊗ T₂).hom PUnit.unit := by
        dsimp only [cActions]
        rw [haction₂]
        exact q_right_base T₁ T₂ action₁
      exact hleft.trans hright.symm
    · generalize hx : x = x₀
      induction x₀ using OnePoint.rec with
      | infty =>
          have hxBase : x = S₁.hom PUnit.unit := hx
          have hqS : qSmash S₁ S₂ cS =
              (S₁ ⊗ S₂).hom PUnit.unit := by
            dsimp only [cS]
            rw [hxBase]
            exact q_left_base S₁ S₂ y
          have hsphere : sphere = Ssum.hom PUnit.unit := by
            dsimp only [sphere]
            rw [hqS]
            exact preservesBase deltaIn.inv
          have hqParam : qSmash Hsum Ssum cParamSphere =
              (Hsum ⊗ Ssum).hom PUnit.unit := by
            dsimp only [cParamSphere]
            rw [hsphere]
            exact q_right_base Hsum Ssum param
          have hout : outSum =
              (orthogonalSphere.{u, v} (n + q)).hom PUnit.unit := by
            dsimp only [outSum]
            rw [hqParam]
            exact preservesBase (orthogonalSphereAction.{u, v} (m + p) (n + q))
          have hleft : leftOut = (T₁ ⊗ T₂).hom PUnit.unit := by
            dsimp only [leftOut]
            rw [hout]
            exact preservesBase deltaOut.hom
          have hqAX : qSmash H₁ S₁ cAX =
              (H₁ ⊗ S₁).hom PUnit.unit := by
            dsimp only [cAX]
            rw [hxBase]
            exact q_right_base H₁ S₁ a
          have haction₁ : action₁ = T₁.hom PUnit.unit := by
            dsimp only [action₁]
            rw [hqAX]
            exact preservesBase (orthogonalSphereAction.{u, v} m n)
          have hright : qSmash T₁ T₂ cActions =
              (T₁ ⊗ T₂).hom PUnit.unit := by
            dsimp only [cActions]
            rw [haction₁]
            exact q_left_base T₁ T₂ action₂
          exact hleft.trans hright.symm
      | coe x' =>
          generalize hy : y = y₀
          induction y₀ using OnePoint.rec with
          | infty =>
              have hyBase : y = S₂.hom PUnit.unit := hy
              have hqS : qSmash S₁ S₂ cS =
                  (S₁ ⊗ S₂).hom PUnit.unit := by
                dsimp only [cS]
                rw [hyBase]
                exact q_right_base S₁ S₂ x
              have hsphere : sphere = Ssum.hom PUnit.unit := by
                dsimp only [sphere]
                rw [hqS]
                exact preservesBase deltaIn.inv
              have hqParam : qSmash Hsum Ssum cParamSphere =
                  (Hsum ⊗ Ssum).hom PUnit.unit := by
                dsimp only [cParamSphere]
                rw [hsphere]
                exact q_right_base Hsum Ssum param
              have hout : outSum =
                  (orthogonalSphere.{u, v} (n + q)).hom PUnit.unit := by
                dsimp only [outSum]
                rw [hqParam]
                exact preservesBase (orthogonalSphereAction.{u, v} (m + p) (n + q))
              have hleft : leftOut = (T₁ ⊗ T₂).hom PUnit.unit := by
                dsimp only [leftOut]
                rw [hout]
                exact preservesBase deltaOut.hom
              have hqBY : qSmash H₂ S₂ cBY =
                  (H₂ ⊗ S₂).hom PUnit.unit := by
                dsimp only [cBY]
                rw [hyBase]
                exact q_right_base H₂ S₂ b
              have haction₂ : action₂ = T₂.hom PUnit.unit := by
                dsimp only [action₂]
                rw [hqBY]
                exact preservesBase (orthogonalSphereAction.{u, v} p q)
              have hright : qSmash T₁ T₂ cActions =
                  (T₁ ⊗ T₂).hom PUnit.unit := by
                dsimp only [cActions]
                rw [haction₂]
                exact q_right_base T₁ T₂ action₁
              exact hleft.trans hright.symm
          | coe y' =>
              rcases x' with ⟨x₀⟩
              rcases y' with ⟨y₀⟩
              let pA : H₁.right :=
                (OrthogonalIndex.matrixPoint.{u, v} A).right t
              let pB : H₂.right :=
                (OrthogonalIndex.matrixPoint.{u, v} B).right t
              let AB := OrthogonalMatrixHom.blockSum A B
              let pAB : Hsum.right :=
                (OrthogonalIndex.matrixPoint.{u, v} AB).right t
              have hparam : param = pAB := by
                have hp := pointTensor_free
                  (OrthogonalIndex.matrixPoint.{u, v} A)
                  (OrthogonalIndex.matrixPoint.{u, v} B)
                have ht :=
                  (OrthogonalIndex.tensorMap_blockSum.{u, v} A B).1
                have hte := ConcreteCategory.congr_hom
                  (congrArg Under.Hom.right ht) t
                simp only [Under.comp_right, ConcreteCategory.comp_apply] at hte
                dsimp only [param, cH]
                rw [ha, hb]
                exact (congrArg tensorMap.right hp).symm.trans hte
              let xy : EuclideanSpace ℝ (Fin (m + p)) :=
                (EuclideanSpace.finAddEquivProd (n := m) (m := p)).symm
                  (x₀, y₀)
              let xyLift : liftedEuclidean.{v} (m + p) := ULift.up xy
              let xPoint : S₁.right :=
                ((ULift.up x₀ : liftedEuclidean.{v} m) :
                  OnePoint (liftedEuclidean.{v} m))
              let yPoint : S₂.right :=
                ((ULift.up y₀ : liftedEuclidean.{v} p) :
                  OnePoint (liftedEuclidean.{v} p))
              have hxPoint : x = xPoint := hx
              have hyPoint : y = yPoint := hy
              have hSplit :
                  liftedFinAddHomeomorph.{v} m p xyLift =
                    (ULift.up x₀, ULift.up y₀) := by
                change
                  (ULift.up
                      ((EuclideanSpace.finAddEquivProd
                        (n := m) (m := p)) xy).1,
                    ULift.up
                      ((EuclideanSpace.finAddEquivProd
                        (n := m) (m := p)) xy).2) =
                    (ULift.up x₀, ULift.up y₀)
                rw [show (EuclideanSpace.finAddEquivProd
                    (n := m) (m := p)) xy = (x₀, y₀) by
                  exact (EuclideanSpace.finAddEquivProd
                    (n := m) (m := p)).apply_symm_apply (x₀, y₀)]
              let cXY : (S₁.right ⊗ S₂.right : CGWH.{u, v}) := Classical.choose
                ((CGWH.prodComparisonToTop_bijective S₁.right S₂.right).2
                  (xPoint, yPoint))
              have hcSXY : cS = cXY := by
                apply (CGWH.prodComparisonToTop_bijective S₁.right S₂.right).1
                have hSource : CGWH.prodComparisonToTop S₁.right S₂.right cS =
                    (x, y) :=
                  Classical.choose_spec
                    ((CGWH.prodComparisonToTop_bijective S₁.right S₂.right).2 (x, y))
                have hPair : (x, y) = (xPoint, yPoint) :=
                  Prod.ext hxPoint hyPoint
                have hTarget : CGWH.prodComparisonToTop S₁.right S₂.right cXY =
                    (xPoint, yPoint) :=
                  Classical.choose_spec
                    ((CGWH.prodComparisonToTop_bijective S₁.right S₂.right).2 (xPoint, yPoint))
                exact hSource.trans (hPair.trans hTarget.symm)
              have hDelta := orthogonalSphereTensorIso_coe.{u, v}
                m p xyLift
              change deltaIn.hom.right
                  (xyLift : OnePoint (liftedEuclidean.{v} (m + p))) =
                qSmash S₁ S₂ (Classical.choose
                  ((CGWH.prodComparisonToTop_bijective
                    S₁.right S₂.right).2
                    (((liftedFinAddHomeomorph.{v} m p xyLift).1 :
                        OnePoint (liftedEuclidean.{v} m)),
                      ((liftedFinAddHomeomorph.{v} m p xyLift).2 :
                        OnePoint (liftedEuclidean.{v} p))))) at hDelta
              rw [hSplit] at hDelta
              have hDelta' :
                  deltaIn.hom.right
                      (xyLift : OnePoint (liftedEuclidean.{v} (m + p))) =
                    qSmash S₁ S₂ cS := by
                rw [hcSXY]
                exact hDelta
              have hCancel := ConcreteCategory.congr_hom
                (congrArg Under.Hom.right deltaIn.hom_inv_id)
                (xyLift : OnePoint (liftedEuclidean.{v} (m + p)))
              simp only [Under.comp_right, Under.id_right] at hCancel
              have hsphere :
                  sphere =
                    (xyLift : OnePoint (liftedEuclidean.{v} (m + p))) := by
                dsimp only [sphere]
                calc
                  _ = deltaIn.inv.right
                      (deltaIn.hom.right
                        (xyLift : OnePoint
                          (liftedEuclidean.{v} (m + p)))) :=
                    congrArg deltaIn.inv.right hDelta'.symm
                  _ = _ := hCancel
              let cABXY : (Hsum.right ⊗ Ssum.right : CGWH.{u, v}) := Classical.choose
                ((CGWH.prodComparisonToTop_bijective
                  Hsum.right Ssum.right).2
                    (pAB,
                      (xyLift : OnePoint
                        (liftedEuclidean.{v} (m + p)))))
              have hcParam : cParamSphere = cABXY := by
                apply (CGWH.prodComparisonToTop_bijective Hsum.right Ssum.right).1
                have hSource : CGWH.prodComparisonToTop Hsum.right Ssum.right cParamSphere =
                    (param, sphere) :=
                  Classical.choose_spec
                    ((CGWH.prodComparisonToTop_bijective Hsum.right Ssum.right).2 (param, sphere))
                have hPair : (param, sphere) =
                    (pAB, (xyLift : OnePoint (liftedEuclidean.{v} (m + p)))) :=
                  Prod.ext hparam hsphere
                have hTarget : CGWH.prodComparisonToTop Hsum.right Ssum.right cABXY =
                    (pAB, (xyLift : OnePoint (liftedEuclidean.{v} (m + p)))) :=
                  Classical.choose_spec
                    ((CGWH.prodComparisonToTop_bijective Hsum.right Ssum.right).2
                      (pAB, (xyLift : OnePoint (liftedEuclidean.{v} (m + p)))))
                exact hSource.trans (hPair.trans hTarget.symm)
              have hActSum :=
                orthogonalSphereAction_coe.{u, v} AB xy
              change
                (orthogonalSphereAction.{u, v} (m + p) (n + q)).right
                    (qSmash Hsum Ssum cABXY) =
                  ((ULift.up ((EuclideanSpace.equiv (Fin (n + q)) ℝ).symm
                    (AB.1 *ᵥ xy.ofLp)) :
                      liftedEuclidean.{v} (n + q)) :
                    OnePoint (liftedEuclidean.{v} (n + q))) at hActSum
              let outVec : EuclideanSpace ℝ (Fin (n + q)) :=
                (EuclideanSpace.equiv (Fin (n + q)) ℝ).symm
                  (AB.1 *ᵥ xy.ofLp)
              let outLift : liftedEuclidean.{v} (n + q) := ULift.up outVec
              have hout :
                  outSum =
                    (outLift : OnePoint (liftedEuclidean.{v} (n + q))) := by
                dsimp only [outSum]
                rw [hcParam]
                exact hActSum
              let Ax : EuclideanSpace ℝ (Fin n) :=
                (EuclideanSpace.equiv (Fin n) ℝ).symm (A.1 *ᵥ x₀.ofLp)
              let By : EuclideanSpace ℝ (Fin q) :=
                (EuclideanSpace.equiv (Fin q) ℝ).symm (B.1 *ᵥ y₀.ofLp)
              have hOutSplit :
                  (EuclideanSpace.finAddEquivProd (n := n) (m := q)) outVec =
                    (Ax, By) := by
                apply Prod.ext
                · apply WithLp.ofLp_injective
                  funext i
                  dsimp [outVec, Ax, AB, xy]
                  simp [OrthogonalMatrixHom.blockSum, Matrix.mulVec,
                    dotProduct, Fin.sum_univ_add]
                · apply WithLp.ofLp_injective
                  funext i
                  dsimp [outVec, By, AB, xy]
                  simp [OrthogonalMatrixHom.blockSum, Matrix.mulVec,
                    dotProduct, Fin.sum_univ_add]
              have hOutLiftSplit :
                  liftedFinAddHomeomorph.{v} n q outLift =
                    (ULift.up Ax, ULift.up By) := by
                change
                  (ULift.up
                      ((EuclideanSpace.finAddEquivProd
                        (n := n) (m := q)) outVec).1,
                    ULift.up
                      ((EuclideanSpace.finAddEquivProd
                        (n := n) (m := q)) outVec).2) =
                    (ULift.up Ax, ULift.up By)
                rw [hOutSplit]
              let AxPoint : T₁.right :=
                ((ULift.up Ax : liftedEuclidean.{v} n) :
                  OnePoint (liftedEuclidean.{v} n))
              let ByPoint : T₂.right :=
                ((ULift.up By : liftedEuclidean.{v} q) :
                  OnePoint (liftedEuclidean.{v} q))
              let cOut : (T₁.right ⊗ T₂.right : CGWH.{u, v}) := Classical.choose
                ((CGWH.prodComparisonToTop_bijective T₁.right T₂.right).2
                  (AxPoint, ByPoint))
              have hDeltaOut :=
                orthogonalSphereTensorIso_coe.{u, v} n q outLift
              change deltaOut.hom.right
                  (outLift : OnePoint (liftedEuclidean.{v} (n + q))) =
                qSmash T₁ T₂ (Classical.choose
                  ((CGWH.prodComparisonToTop_bijective
                    T₁.right T₂.right).2
                    (((liftedFinAddHomeomorph.{v} n q outLift).1 :
                        OnePoint (liftedEuclidean.{v} n)),
                      ((liftedFinAddHomeomorph.{v} n q outLift).2 :
                        OnePoint (liftedEuclidean.{v} q))))) at hDeltaOut
              rw [hOutLiftSplit] at hDeltaOut
              have hleft : leftOut = qSmash T₁ T₂ cOut := by
                dsimp only [leftOut]
                rw [hout]
                exact hDeltaOut
              let cA : (H₁.right ⊗ S₁.right : CGWH.{u, v}) := Classical.choose
                ((CGWH.prodComparisonToTop_bijective H₁.right S₁.right).2
                  (pA, xPoint))
              have hcA : cAX = cA := by
                apply (CGWH.prodComparisonToTop_bijective H₁.right S₁.right).1
                have hSource : CGWH.prodComparisonToTop H₁.right S₁.right cAX =
                    (a, x) :=
                  Classical.choose_spec
                    ((CGWH.prodComparisonToTop_bijective H₁.right S₁.right).2 (a, x))
                have hPair : (a, x) = (pA, xPoint) :=
                  Prod.ext ha hxPoint
                have hTarget : CGWH.prodComparisonToTop H₁.right S₁.right cA =
                    (pA, xPoint) :=
                  Classical.choose_spec
                    ((CGWH.prodComparisonToTop_bijective H₁.right S₁.right).2 (pA, xPoint))
                exact hSource.trans (hPair.trans hTarget.symm)
              have hActA := orthogonalSphereAction_coe.{u, v} A x₀
              change (orthogonalSphereAction.{u, v} m n).right
                  (qSmash H₁ S₁ cA) = AxPoint at hActA
              have haction₁ : action₁ = AxPoint := by
                dsimp only [action₁]
                rw [hcA]
                exact hActA
              let cB : (H₂.right ⊗ S₂.right : CGWH.{u, v}) := Classical.choose
                ((CGWH.prodComparisonToTop_bijective H₂.right S₂.right).2
                  (pB, yPoint))
              have hcB : cBY = cB := by
                apply (CGWH.prodComparisonToTop_bijective H₂.right S₂.right).1
                have hSource : CGWH.prodComparisonToTop H₂.right S₂.right cBY =
                    (b, y) :=
                  Classical.choose_spec
                    ((CGWH.prodComparisonToTop_bijective H₂.right S₂.right).2 (b, y))
                have hPair : (b, y) = (pB, yPoint) :=
                  Prod.ext hb hyPoint
                have hTarget : CGWH.prodComparisonToTop H₂.right S₂.right cB =
                    (pB, yPoint) :=
                  Classical.choose_spec
                    ((CGWH.prodComparisonToTop_bijective H₂.right S₂.right).2 (pB, yPoint))
                exact hSource.trans (hPair.trans hTarget.symm)
              have hActB := orthogonalSphereAction_coe.{u, v} B y₀
              change (orthogonalSphereAction.{u, v} p q).right
                  (qSmash H₂ S₂ cB) = ByPoint at hActB
              have haction₂ : action₂ = ByPoint := by
                dsimp only [action₂]
                rw [hcB]
                exact hActB
              have hcActions : cActions = cOut := by
                apply (CGWH.prodComparisonToTop_bijective T₁.right T₂.right).1
                have hSource : CGWH.prodComparisonToTop T₁.right T₂.right cActions =
                    (action₁, action₂) :=
                  Classical.choose_spec
                    ((CGWH.prodComparisonToTop_bijective T₁.right T₂.right).2 (action₁, action₂))
                have hPair : (action₁, action₂) = (AxPoint, ByPoint) :=
                  Prod.ext haction₁ haction₂
                have hTarget : CGWH.prodComparisonToTop T₁.right T₂.right cOut =
                    (AxPoint, ByPoint) :=
                  Classical.choose_spec
                    ((CGWH.prodComparisonToTop_bijective T₁.right T₂.right).2 (AxPoint, ByPoint))
                exact hSource.trans (hPair.trans hTarget.symm)
              rw [hleft, hcActions]

/-- The native enriched identity acts identically on the representation
sphere. -/
theorem orthogonalSphereAction_identity (n : OrthogonalIndex) :
    (λ_ (orthogonalSphere.{u, v} n)).inv ≫
        (@eId PointedCGWH.{u, v} _ _ OrthogonalIndex
          (OrthogonalIndex.enrichedCategory.{u, v}) n ⊗ₘ
          𝟙 (orthogonalSphere.{u, v} n)) ≫
      orthogonalSphereAction.{u, v} n n =
    𝟙 (orthogonalSphere.{u, v} n) :=
  action_identity n

/-- Native enriched composition agrees with successive action on
representation spheres. -/
theorem orthogonalSphereAction_composition
    (m n p : OrthogonalIndex) :
    ((@eComp PointedCGWH.{u, v} _ _ OrthogonalIndex
          (OrthogonalIndex.enrichedCategory.{u, v}) m n p) ⊗ₘ
        𝟙 (orthogonalSphere.{u, v} m)) ≫
      orthogonalSphereAction.{u, v} m p =
    (α_ (OrthogonalIndex.hom.{u, v} m n)
      (OrthogonalIndex.hom.{u, v} n p)
      (orthogonalSphere.{u, v} m)).hom ≫
      (𝟙 (OrthogonalIndex.hom.{u, v} m n) ⊗ₘ
        (β_ (OrthogonalIndex.hom.{u, v} n p)
          (orthogonalSphere.{u, v} m)).hom) ≫
      (α_ (OrthogonalIndex.hom.{u, v} m n)
        (orthogonalSphere.{u, v} m)
        (OrthogonalIndex.hom.{u, v} n p)).inv ≫
      (orthogonalSphereAction.{u, v} m n ⊗ₘ
        𝟙 (OrthogonalIndex.hom.{u, v} n p)) ≫
      (β_ (orthogonalSphere.{u, v} n)
        (OrthogonalIndex.hom.{u, v} n p)).hom ≫
      orthogonalSphereAction.{u, v} n p :=
  action_composition m n p

/-- Direct sums of orthogonal matrices act componentwise under the
representation-sphere splitting. -/
theorem orthogonalSphereAction_blockSum
    (m n p q : OrthogonalIndex) :
    (OrthogonalIndex.tensorMap.{u, v} m n p q ⊗ₘ
        (orthogonalSphereTensorIso.{u, v} m p).inv) ≫
      orthogonalSphereAction.{u, v} (m + p) (n + q) ≫
      (orthogonalSphereTensorIso.{u, v} n q).hom =
    MonoidalCategory.tensorμ
        (OrthogonalIndex.hom.{u, v} m n)
        (OrthogonalIndex.hom.{u, v} p q)
        (orthogonalSphere.{u, v} m)
        (orthogonalSphere.{u, v} p) ≫
      (orthogonalSphereAction.{u, v} m n ⊗ₘ
        orthogonalSphereAction.{u, v} p q) :=
  action_blockSum m n p q

end PointedCGWH
