/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.MatrixIndex
public import MathlibExt.CategoryTheory.Enriched.Monoidal.Basic
public import MathlibExt.Topology.Category.PointedCGWH.Separator
public import MathlibExt.CategoryTheory.Monoidal.Pointed.Free
public import MathlibExt.Topology.Category.PointedCGWH.Closed
public import MathlibExt.Topology.Category.PointedCGWH.Zero

/-!
# The native enriched orthogonal indexing category

This file equips the standard finite-dimensional skeleton with its native
PointedCGWH-enriched orthogonal hom objects and direct-sum structure.  The
basepoint is freely adjoined; it is not a one-point compactification.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory TopologicalSpace
open scoped ZeroObject

attribute [local instance] HasZeroObject.zeroMorphismsOfZeroObject

universe u v

namespace CategoryTheory.Spectra
namespace OrthogonalIndex

/-- The CGWH space of orthogonal matrix morphisms between two indices. -/
private noncomputable def rawHomCGWH
    (m n : OrthogonalIndex) : CGWH.{u, v} := by
  letI : PseudoMetrizableSpace (Matrix (Fin n) (Fin m) ℝ) :=
    inferInstanceAs (PseudoMetrizableSpace (Fin n → Fin m → ℝ))
  letI : PseudoMetrizableSpace (OrthogonalMatrixHom m n) :=
    Topology.IsInducing.subtypeVal.pseudoMetrizableSpace
  letI : PseudoMetrizableSpace
      (ULift.{v, 0} (OrthogonalMatrixHom m n)) :=
    Homeomorph.ulift.isInducing.pseudoMetrizableSpace
  exact CGWH.of.{u, v} (ULift.{v, 0} (OrthogonalMatrixHom m n))

/-- The native hom object, with a categorical disjoint basepoint. -/
noncomputable def hom (m n : OrthogonalIndex) : PointedCGWH.{u, v} := by
  let matrixHom
      (m n : OrthogonalIndex) : CGWH.{u, v} := by
    letI : PseudoMetrizableSpace (Matrix (Fin n) (Fin m) ℝ) :=
      inferInstanceAs (PseudoMetrizableSpace (Fin n → Fin m → ℝ))
    letI : PseudoMetrizableSpace (OrthogonalMatrixHom m n) :=
      Topology.IsInducing.subtypeVal.pseudoMetrizableSpace
    letI : PseudoMetrizableSpace
        (ULift.{v, 0} (OrthogonalMatrixHom m n)) :=
      Homeomorph.ulift.isInducing.pseudoMetrizableSpace
    exact CGWH.of.{u, v} (ULift.{v, 0} (OrthogonalMatrixHom m n))
  exact (Under.costar CGWH.point).obj (matrixHom m n)

/-- The generalized point corresponding to a raw orthogonal matrix. -/
noncomputable def matrixPoint
    {m n : OrthogonalIndex} (A : OrthogonalMatrixHom m n) :
    𝟙_ PointedCGWH.{u, v} ⟶ hom.{u, v} m n := by
  let matrixHom
      (m n : OrthogonalIndex) : CGWH.{u, v} := by
    letI : PseudoMetrizableSpace (Matrix (Fin n) (Fin m) ℝ) :=
      inferInstanceAs (PseudoMetrizableSpace (Fin n → Fin m → ℝ))
    letI : PseudoMetrizableSpace (OrthogonalMatrixHom m n) :=
      Topology.IsInducing.subtypeVal.pseudoMetrizableSpace
    letI : PseudoMetrizableSpace
        (ULift.{v, 0} (OrthogonalMatrixHom m n)) :=
      Homeomorph.ulift.isInducing.pseudoMetrizableSpace
    exact CGWH.of.{u, v} (ULift.{v, 0} (OrthogonalMatrixHom m n))
  exact (Under.costar CGWH.point).map
    ((CGWH.pointHomEquiv (matrixHom m n)).symm (ULift.up A))

private noncomputable def rawPointFromUnit
    {m n : OrthogonalIndex} (A : OrthogonalMatrixHom m n) :
    𝟙_ CGWH.{u, v} ⟶ rawHomCGWH.{u, v} m n :=
  (CGWH.point_isTerminal.uniqueUpToIso
      CartesianMonoidalCategory.isTerminalTensorUnit).inv ≫
    (CGWH.pointHomEquiv (rawHomCGWH.{u, v} m n)).symm (ULift.up A)

private theorem freePoint_cases
    (Z : CGWH.{u, v})
    (f : 𝟙_ PointedCGWH.{u, v} ⟶
      (Under.costar CGWH.point.{u, v}).obj Z) :
    f = 0 ∨ ∃ z : Z,
      f = (Under.costar CGWH.point.{u, v}).map
        ((CGWH.pointHomEquiv Z).symm z) := by
  let X := CGWH.cgwhToTop.obj CGWH.point.{u, v}
  let Y := CGWH.cgwhToTop.obj Z
  let I := ULift.{v, 0} WalkingPair
  let eI : I ≃ WalkingPair := Equiv.ulift
  let eIdx : Discrete I ≌ Discrete WalkingPair := Discrete.equivalence eI
  let G := pair CGWH.point.{u, v} Z
  let F := eIdx.functor ⋙ G
  let family : I → CGWH.{u, v} := fun i ↦ F.obj ⟨i⟩
  let F₀ := Discrete.functor family
  let w : eIdx.functor ⋙ G ≅ F₀ := Discrete.natIsoFunctor
  let targetIso : Limits.colimit F₀ ≅ Limits.colimit G :=
    CategoryTheory.Limits.HasColimit.isoOfEquivalence eIdx w
  let topFamily : I → TopCat.{v} := fun i ↦
    CompactlyGenerated.compactlyGeneratedToTop.obj
      (CGWH.cgwhToCompactlyGenerated.obj (family i))
  let sourceIso : (∐ topFamily) ≅ TopCat.of (Σ i, topFamily i) :=
    TopCat.sigmaIsoSigma _
  let comparison := CGWH.coproductComparisonIso family
  let e : TopCat.of (Σ i, topFamily i) ≅
      CGWH.cgwhToTop.obj (CGWH.point.{u, v} ⨿ Z) :=
    sourceIso.symm ≪≫ comparison ≪≫ CGWH.cgwhToTop.mapIso targetIso
  let iL : I := ULift.up WalkingPair.left
  let iR : I := ULift.up WalkingPair.right
  have hComparison (i : I) :
      Limits.Sigma.ι topFamily i ≫ comparison.hom =
        CGWH.cgwhToTop.map (Limits.Sigma.ι family i) := by
    exact CGWH.coproductComparisonIso_ι family i
  have hTargetL : Limits.Sigma.ι family iL ≫ targetIso.hom =
      (coprod.inl : CGWH.point.{u, v} ⟶ CGWH.point.{u, v} ⨿ Z) := by
    calc
      _ = w.inv.app (Discrete.mk iL) ≫
          Limits.colimit.ι G (eIdx.functor.obj (Discrete.mk iL)) :=
        CategoryTheory.Limits.HasColimit.ι_isoOfEquivalence_hom
          eIdx w (Discrete.mk iL)
      _ = _ := by rfl
  have hTargetR : Limits.Sigma.ι family iR ≫ targetIso.hom =
      (coprod.inr : Z ⟶ CGWH.point.{u, v} ⨿ Z) := by
    calc
      _ = w.inv.app (Discrete.mk iR) ≫
          Limits.colimit.ι G (eIdx.functor.obj (Discrete.mk iR)) :=
        CategoryTheory.Limits.HasColimit.ι_isoOfEquivalence_hom
          eIdx w (Discrete.mk iR)
      _ = _ := by rfl
  have hInl (a : topFamily iL) : e.hom ⟨iL, a⟩ =
      (coprod.inl : CGWH.point.{u, v} ⟶ CGWH.point.{u, v} ⨿ Z)
        (show X from a) := by
    change (CGWH.cgwhToTop.map targetIso.hom)
        (comparison.hom (sourceIso.inv ⟨iL, a⟩)) = _
    rw [show sourceIso.inv ⟨iL, a⟩ = Limits.Sigma.ι topFamily iL a from
        by simpa [sourceIso] using
          (TopCat.sigmaIsoSigma_inv_apply topFamily iL a)]
    have htotal : Limits.Sigma.ι topFamily iL ≫ comparison.hom ≫
          CGWH.cgwhToTop.map targetIso.hom =
        CGWH.cgwhToTop.map
          (coprod.inl : CGWH.point.{u, v} ⟶ CGWH.point.{u, v} ⨿ Z) := by
      slice_lhs 1 2 => rw [hComparison]
      rw [← CGWH.cgwhToTop.map_comp, hTargetL]
      rfl
    exact ConcreteCategory.congr_hom htotal a
  have hInr (b : topFamily iR) : e.hom ⟨iR, b⟩ =
      (coprod.inr : Z ⟶ CGWH.point.{u, v} ⨿ Z) (show Y from b) := by
    change (CGWH.cgwhToTop.map targetIso.hom)
        (comparison.hom (sourceIso.inv ⟨iR, b⟩)) = _
    rw [show sourceIso.inv ⟨iR, b⟩ = Limits.Sigma.ι topFamily iR b from
        by simpa [sourceIso] using
          (TopCat.sigmaIsoSigma_inv_apply topFamily iR b)]
    have htotal : Limits.Sigma.ι topFamily iR ≫ comparison.hom ≫
          CGWH.cgwhToTop.map targetIso.hom =
        CGWH.cgwhToTop.map
          (coprod.inr : Z ⟶ CGWH.point.{u, v} ⨿ Z) := by
      slice_lhs 1 2 => rw [hComparison]
      rw [← CGWH.cgwhToTop.map_comp, hTargetR]
      rfl
    exact ConcreteCategory.congr_hom htotal b
  let H := (Under.costar CGWH.point.{u, v}).obj Z
  let adj := Under.costarAdjForget CGWH.point.{u, v}
  let freeGenerator : CGWH.point.{u, v} ⟶
      (𝟙_ PointedCGWH.{u, v}).right := coprod.inr
  let adjEquiv : (𝟙_ PointedCGWH.{u, v} ⟶ H) ≃
      (CGWH.point.{u, v} ⟶ H.right) := adj.homEquiv CGWH.point.{u, v} H
  have hadj (g : 𝟙_ PointedCGWH.{u, v} ⟶ H) :
      adjEquiv g = freeGenerator ≫ g.right := rfl
  have zeroRightIsTerminal : IsTerminal
      ((0 : PointedCGWH.{u, v}).right) := by
    let pointZero : PointedCGWH.{u, v} := Under.mk (𝟙 CGWH.point.{u, v})
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
        hom_inv_id := congrArg (fun g ↦ g.right) zeroPointedIso.hom_inv_id
        inv_hom_id := congrArg (fun g ↦ g.right) zeroPointedIso.inv_hom_id }
    exact IsTerminal.ofIso CGWH.point_isTerminal zeroRightIso.symm
  have hzero : freeGenerator ≫
        (0 : 𝟙_ PointedCGWH.{u, v} ⟶ H).right = H.hom := by
    change freeGenerator ≫
        ((default : 𝟙_ PointedCGWH.{u, v} ⟶
          (0 : PointedCGWH.{u, v})).right ≫
        (default : (0 : PointedCGWH.{u, v}) ⟶ H).right) = _
    rw [← Category.assoc]
    have hfirst : freeGenerator ≫
        (default : 𝟙_ PointedCGWH.{u, v} ⟶
          (0 : PointedCGWH.{u, v})).right =
        (0 : PointedCGWH.{u, v}).hom :=
      zeroRightIsTerminal.hom_ext _ _
    rw [hfirst]
    exact Under.w (default : (0 : PointedCGWH.{u, v}) ⟶ H)
  have hzeroPoint :
      CGWH.pointHomEquiv H.right
          (adjEquiv 0) =
        (coprod.inl : CGWH.point.{u, v} ⟶ CGWH.point.{u, v} ⨿ Z)
          PUnit.unit := by
    change (adjEquiv 0) (show CGWH.point.{u, v} from PUnit.unit) = _
    exact (ConcreteCategory.congr_hom (hadj 0) (show CGWH.point.{u, v} from PUnit.unit)).trans
      ((ConcreteCategory.congr_hom hzero (show CGWH.point.{u, v} from PUnit.unit)).trans (by
        have hhom : H.hom =
            (coprod.inl : CGWH.point.{u, v} ⟶ CGWH.point.{u, v} ⨿ Z) :=
          (Under.costar_obj_hom CGWH.point.{u, v} Z).trans (coprod.inl_desc _ _)
        exact ConcreteCategory.congr_hom hhom (show CGWH.point.{u, v} from PUnit.unit)))
  have hpoint (z : Z) :
      CGWH.pointHomEquiv H.right
          (adjEquiv
            ((Under.costar CGWH.point.{u, v}).map
              ((CGWH.pointHomEquiv Z).symm z))) =
        (coprod.inr : Z ⟶ CGWH.point.{u, v} ⨿ Z) z := by
    let g : 𝟙_ PointedCGWH.{u, v} ⟶ H :=
      (Under.costar CGWH.point.{u, v}).map ((CGWH.pointHomEquiv Z).symm z)
    let t : CGWH.point.{u, v} := by
      change PUnit
      exact PUnit.unit
    have hmap : freeGenerator ≫ g.right =
        (CGWH.pointHomEquiv Z).symm z ≫
          (coprod.inr : Z ⟶ CGWH.point.{u, v} ⨿ Z) := by
      change (coprod.inr : CGWH.point.{u, v} ⟶ CGWH.point.{u, v} ⨿ CGWH.point.{u, v}) ≫
        coprod.map (𝟙 CGWH.point.{u, v}) ((CGWH.pointHomEquiv Z).symm z) = _
      exact coprod.inr_map _ _
    change (adjEquiv g) t = _
    exact (ConcreteCategory.congr_hom (hadj g) t).trans
      ((ConcreteCategory.congr_hom hmap t).trans (by
        change (coprod.inr : Z ⟶ CGWH.point.{u, v} ⨿ Z)
          ((CGWH.pointHomEquiv Z).symm z t) = _
        exact congrArg (ConcreteCategory.hom (coprod.inr : Z ⟶ CGWH.point.{u, v} ⨿ Z))
          (CGWH.pointHomEquiv_symm_apply_apply Z z t)))
  let b : CGWH.point.{u, v} ⟶ H.right := adjEquiv f
  let x : H.right := CGWH.pointHomEquiv H.right b
  let sx : Σ i, topFamily i := e.inv x
  have hx : e.hom sx = x := ConcreteCategory.congr_hom e.inv_hom_id x
  rcases sx with ⟨i, y⟩
  rcases i with ⟨i⟩
  cases i with
  | left =>
      change X at y
      left
      apply adjEquiv.injective
      apply (CGWH.pointHomEquiv H.right).injective
      change x = _
      exact hx.symm.trans ((hInl (show topFamily iL from y)).trans (by
        cases y
        exact hzeroPoint.symm))
  | right =>
      change Y at y
      right
      refine ⟨y, ?_⟩
      apply adjEquiv.injective
      apply (CGWH.pointHomEquiv H.right).injective
      change x = _
      exact hx.symm.trans ((hInr (show topFamily iR from y)).trans (hpoint y).symm)

/-- An unequal-dimensional hom object is the pointed zero object. -/
noncomputable def homOfNe
    {m n : OrthogonalIndex} (h : m ≠ n) :
    hom.{u, v} m n ≅ (0 : PointedCGWH.{u, v}) := by
  let matrixHom
      (m n : OrthogonalIndex) : CGWH.{u, v} := by
    letI : PseudoMetrizableSpace (Matrix (Fin n) (Fin m) ℝ) :=
      inferInstanceAs (PseudoMetrizableSpace (Fin n → Fin m → ℝ))
    letI : PseudoMetrizableSpace (OrthogonalMatrixHom m n) :=
      Topology.IsInducing.subtypeVal.pseudoMetrizableSpace
    letI : PseudoMetrizableSpace
        (ULift.{v, 0} (OrthogonalMatrixHom m n)) :=
      Homeomorph.ulift.isInducing.pseudoMetrizableSpace
    exact CGWH.of.{u, v} (ULift.{v, 0} (OrthogonalMatrixHom m n))
  let hRaw : IsInitial (matrixHom m n) := by
    letI : IsEmpty (OrthogonalMatrixHom m n) :=
      ⟨fun A ↦ h ((OrthogonalMatrixHom.nonempty_iff m n).1 ⟨A⟩)⟩
    letI : IsEmpty (ULift.{v, 0} (OrthogonalMatrixHom m n)) :=
      inferInstance
    letI : IsEmpty (matrixHom m n : Type v) := by
      change IsEmpty (ULift.{v, 0} (OrthogonalMatrixHom m n))
      infer_instance
    letI : DiscreteTopology (matrixHom m n : Type v) :=
      inferInstance
    exact IsInitial.ofUniqueHom
      (fun X ↦ ConcreteCategory.ofHom
        ⟨isEmptyElim, continuous_of_discreteTopology⟩)
      (fun X f ↦ by
        apply ConcreteCategory.hom_ext
        intro x
        exact isEmptyElim x)
  let adj := Under.costarAdjForget CGWH.point.{u, v}
  let hFree : IsInitial (hom.{u, v} m n) :=
    IsInitial.ofUniqueHom
      (fun Y ↦ (adj.homEquiv _ Y).symm (hRaw.to Y.right))
      (fun Y f ↦ by
        apply (adj.homEquiv _ Y).injective
        exact hRaw.hom_ext _ _)
  exact hFree.uniqueUpToIso HasZeroObject.zeroIsInitial

/-- In equal dimensions the raw part of the hom object is the lifted
orthogonal group with its inherited topology. -/
noncomputable def homSelf (n : OrthogonalIndex) :
    letI : PseudoMetrizableSpace (Matrix (Fin n) (Fin n) ℝ) :=
      inferInstanceAs (PseudoMetrizableSpace (Fin n → Fin n → ℝ))
    letI : PseudoMetrizableSpace
        (Matrix.orthogonalGroup (Fin n) ℝ) :=
      Topology.IsInducing.subtypeVal.pseudoMetrizableSpace
    letI : PseudoMetrizableSpace
        (ULift.{v, 0} (Matrix.orthogonalGroup (Fin n) ℝ)) :=
      Homeomorph.ulift.isInducing.pseudoMetrizableSpace
    hom.{u, v} n n ≅
      (Under.costar CGWH.point).obj
        (CGWH.of.{u, v}
          (ULift.{v, 0} (Matrix.orthogonalGroup (Fin n) ℝ))) := by
  letI : PseudoMetrizableSpace (Matrix (Fin n) (Fin n) ℝ) :=
    inferInstanceAs (PseudoMetrizableSpace (Fin n → Fin n → ℝ))
  letI : PseudoMetrizableSpace
      (Matrix.orthogonalGroup (Fin n) ℝ) :=
    Topology.IsInducing.subtypeVal.pseudoMetrizableSpace
  letI : PseudoMetrizableSpace
      (ULift.{v, 0} (Matrix.orthogonalGroup (Fin n) ℝ)) :=
    Homeomorph.ulift.isInducing.pseudoMetrizableSpace
  let e : ULift.{v, 0} (OrthogonalMatrixHom n n) ≃ₜ
      ULift.{v, 0} (Matrix.orthogonalGroup (Fin n) ℝ) :=
    (Homeomorph.ulift (X := OrthogonalMatrixHom n n)).trans
      ((OrthogonalMatrixHom.homeomorphOrthogonalGroup n).trans
        (Homeomorph.ulift
          (X := Matrix.orthogonalGroup (Fin n) ℝ)).symm)
  exact (Under.costar CGWH.point).mapIso
    (CGWH.isoOfHomeo e)

/-- The constant point representing the identity orthogonal matrix morphism. -/
private noncomputable def rawIdentity (n : OrthogonalIndex) :
    𝟙_ CGWH.{u, v} ⟶ rawHomCGWH.{u, v} n n :=
  ConcreteCategory.ofHom
    ⟨fun _ ↦ ULift.up (OrthogonalMatrixHom.id n), continuous_const⟩

/-- Continuous composition of the underlying orthogonal matrix morphisms. -/
private noncomputable def rawComp
    (m n p : OrthogonalIndex) :
    (rawHomCGWH.{u, v} m n ⊗ rawHomCGWH.{u, v} n p) ⟶
      rawHomCGWH.{u, v} m p := by
  let X := rawHomCGWH.{u, v} m n
  let Y := rawHomCGWH.{u, v} n p
  exact ConcreteCategory.ofHom
    ⟨fun z ↦ ULift.up (OrthogonalMatrixHom.comp
        (CartesianMonoidalCategory.fst X Y z).down
        (CartesianMonoidalCategory.snd X Y z).down),
      (Homeomorph.ulift
          (X := OrthogonalMatrixHom m p)).symm.continuous.comp
        (OrthogonalMatrixHom.continuous_comp.comp
          (((Homeomorph.ulift
              (X := OrthogonalMatrixHom m n)).continuous.comp
                (ConcreteCategory.hom
                  (CartesianMonoidalCategory.fst X Y)).continuous).prodMk
            ((Homeomorph.ulift
              (X := OrthogonalMatrixHom n p)).continuous.comp
                (ConcreteCategory.hom
                  (CartesianMonoidalCategory.snd X Y)).continuous)))⟩

@[simp]
private theorem rawComp_apply (m n p : OrthogonalIndex)
    (z : (rawHomCGWH.{u, v} m n ⊗
      rawHomCGWH.{u, v} n p : CGWH.{u, v})) :
    rawComp.{u, v} m n p z =
      ULift.up (OrthogonalMatrixHom.comp
        (CartesianMonoidalCategory.fst
          (rawHomCGWH.{u, v} m n) (rawHomCGWH.{u, v} n p) z).down
      (CartesianMonoidalCategory.snd
          (rawHomCGWH.{u, v} m n) (rawHomCGWH.{u, v} n p) z).down) :=
  rfl

/-- The CGWH enrichment defined by the orthogonal Hom spaces and their composition. -/
@[instance_reducible]
private noncomputable def rawEnrichedCategory :
    EnrichedCategory CGWH.{u, v} OrthogonalIndex where
  Hom := rawHomCGWH
  id := rawIdentity
  comp := rawComp
  id_comp m n := by
    apply (cancel_epi (λ_ (rawHomCGWH.{u, v} m n)).hom).1
    rw [Iso.hom_inv_id_assoc]
    apply ConcreteCategory.hom_ext
    intro z
    rw [ConcreteCategory.comp_apply, rawComp_apply]
    have hFst := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.whiskerRight_fst
        (rawIdentity.{u, v} m) (rawHomCGWH.{u, v} m n)) z
    have hSnd := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.whiskerRight_snd
        (rawIdentity.{u, v} m) (rawHomCGWH.{u, v} m n)) z
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hFst
    rw [ConcreteCategory.comp_apply] at hSnd
    have hId : rawIdentity.{u, v} m
        (ConcreteCategory.hom
          (CartesianMonoidalCategory.fst (𝟙_ CGWH.{u, v})
            (rawHomCGWH.{u, v} m n)) z) =
      ULift.up (OrthogonalMatrixHom.id m) := rfl
    rw [hFst, hSnd, hId, OrthogonalMatrixHom.id_comp]
    exact (ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.leftUnitor_hom
        (rawHomCGWH.{u, v} m n)) z).symm
  comp_id m n := by
    apply (cancel_epi (ρ_ (rawHomCGWH.{u, v} m n)).hom).1
    rw [Iso.hom_inv_id_assoc]
    apply ConcreteCategory.hom_ext
    intro z
    rw [ConcreteCategory.comp_apply, rawComp_apply]
    have hFst := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.whiskerLeft_fst
        (rawHomCGWH.{u, v} m n) (rawIdentity.{u, v} n)) z
    have hSnd := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.whiskerLeft_snd
        (rawHomCGWH.{u, v} m n) (rawIdentity.{u, v} n)) z
    rw [ConcreteCategory.comp_apply] at hFst
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hSnd
    have hId : rawIdentity.{u, v} n
        (ConcreteCategory.hom
          (CartesianMonoidalCategory.snd (rawHomCGWH.{u, v} m n)
            (𝟙_ CGWH.{u, v})) z) =
      ULift.up (OrthogonalMatrixHom.id n) := rfl
    rw [hFst, hSnd, hId, OrthogonalMatrixHom.comp_id]
    exact (ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.rightUnitor_hom
        (rawHomCGWH.{u, v} m n)) z).symm
  assoc m n p q := by
    apply (cancel_epi
      (α_ (rawHomCGWH.{u, v} m n) (rawHomCGWH.{u, v} n p)
        (rawHomCGWH.{u, v} p q)).hom).1
    rw [Iso.hom_inv_id_assoc]
    apply ConcreteCategory.hom_ext
    intro z
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
      ConcreteCategory.comp_apply, rawComp_apply, rawComp_apply]
    have hLeftFst := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.whiskerRight_fst
        (rawComp.{u, v} m n p) (rawHomCGWH.{u, v} p q)) z
    have hLeftSnd := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.whiskerRight_snd
        (rawComp.{u, v} m n p) (rawHomCGWH.{u, v} p q)) z
    let w := ConcreteCategory.hom
      (α_ (rawHomCGWH.{u, v} m n) (rawHomCGWH.{u, v} n p)
        (rawHomCGWH.{u, v} p q)).hom z
    have hRightFst := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.whiskerLeft_fst
        (rawHomCGWH.{u, v} m n) (rawComp.{u, v} n p q)) w
    have hRightSnd := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.whiskerLeft_snd
        (rawHomCGWH.{u, v} m n) (rawComp.{u, v} n p q)) w
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hLeftFst
    rw [ConcreteCategory.comp_apply] at hLeftSnd hRightFst
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hRightSnd
    rw [hLeftFst, hLeftSnd, hRightFst, hRightSnd,
      rawComp_apply, rawComp_apply]
    have hAssocFst := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.associator_hom_fst
        (rawHomCGWH.{u, v} m n) (rawHomCGWH.{u, v} n p)
        (rawHomCGWH.{u, v} p q)) z
    have hAssocSndFst := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.associator_hom_snd_fst
        (rawHomCGWH.{u, v} m n) (rawHomCGWH.{u, v} n p)
        (rawHomCGWH.{u, v} p q)) z
    have hAssocSndSnd := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.associator_hom_snd_snd
        (rawHomCGWH.{u, v} m n) (rawHomCGWH.{u, v} n p)
        (rawHomCGWH.{u, v} p q)) z
    rw [ConcreteCategory.comp_apply] at hAssocFst
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hAssocSndFst
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hAssocSndSnd
    rw [hAssocFst, hAssocSndFst, hAssocSndSnd]
    congr 1
    exact OrthogonalMatrixHom.comp_assoc _ _ _

/-- The native PointedCGWH enrichment of the orthogonal index. -/
@[instance_reducible]
noncomputable def enrichedCategory :
    EnrichedCategory PointedCGWH.{u, v} OrthogonalIndex := by
  let matrixHom
      (m n : OrthogonalIndex) : CGWH.{u, v} := by
    letI : PseudoMetrizableSpace (Matrix (Fin n) (Fin m) ℝ) :=
      inferInstanceAs (PseudoMetrizableSpace (Fin n → Fin m → ℝ))
    letI : PseudoMetrizableSpace (OrthogonalMatrixHom m n) :=
      Topology.IsInducing.subtypeVal.pseudoMetrizableSpace
    letI : PseudoMetrizableSpace
        (ULift.{v, 0} (OrthogonalMatrixHom m n)) :=
      Homeomorph.ulift.isInducing.pseudoMetrizableSpace
    exact CGWH.of.{u, v} (ULift.{v, 0} (OrthogonalMatrixHom m n))
  let matrixIdentity (n : OrthogonalIndex) :
      𝟙_ CGWH.{u, v} ⟶ matrixHom n n :=
    ConcreteCategory.ofHom
      ⟨fun _ ↦ ULift.up (OrthogonalMatrixHom.id n), continuous_const⟩
  let matrixComposition
      (m n p : OrthogonalIndex) :
      (matrixHom m n ⊗ matrixHom n p) ⟶
        matrixHom m p := by
    let X := matrixHom m n
    let Y := matrixHom n p
    exact ConcreteCategory.ofHom
      ⟨fun z ↦ ULift.up (OrthogonalMatrixHom.comp
          (CartesianMonoidalCategory.fst X Y z).down
          (CartesianMonoidalCategory.snd X Y z).down),
        (Homeomorph.ulift
            (X := OrthogonalMatrixHom m p)).symm.continuous.comp
          (OrthogonalMatrixHom.continuous_comp.comp
            (((Homeomorph.ulift
                (X := OrthogonalMatrixHom m n)).continuous.comp
                  (ConcreteCategory.hom
                    (CartesianMonoidalCategory.fst X Y)).continuous).prodMk
              ((Homeomorph.ulift
                (X := OrthogonalMatrixHom n p)).continuous.comp
                  (ConcreteCategory.hom
                    (CartesianMonoidalCategory.snd X Y)).continuous)))⟩
  let matrixEnrichment : EnrichedCategory CGWH.{u, v} OrthogonalIndex :=
    { Hom := matrixHom
      id := matrixIdentity
      comp := matrixComposition
      id_comp := by exact rawEnrichedCategory.{u, v}.id_comp
      comp_id := by exact rawEnrichedCategory.{u, v}.comp_id
      assoc := by exact rawEnrichedCategory.{u, v}.assoc }
  let F := Under.costar CGWH.point.{u, v}
  let _ : EnrichedCategory CGWH.{u, v} OrthogonalIndex :=
    matrixEnrichment
  let _ : BraidedCategory CGWH.{u, v} :=
    BraidedCategory.ofCartesianMonoidalCategory
  let _ : SymmetricCategory CGWH.{u, v} := inferInstance
  let _ : MonoidalCategory PointedCGWH.{u, v} :=
    CategoryTheory.Pointed.smashMonoidalCategory
      CGWH.point.{u, v} CGWH.point_isTerminal
  let _ : F.Monoidal :=
    (CategoryTheory.Pointed.costarCoreMonoidal
      CGWH.point.{u, v} CGWH.point_isTerminal).toMonoidal
  exact inferInstanceAs
    (EnrichedCategory PointedCGWH.{u, v}
      (TransportEnrichment F OrthogonalIndex))

private theorem freePoint_eq_coreUnit_map
    (Z : CGWH.{u, v}) (z : Z) :
    let F := Under.costar CGWH.point.{u, v}
    letI : BraidedCategory CGWH.{u, v} :=
      BraidedCategory.ofCartesianMonoidalCategory
    letI : SymmetricCategory CGWH.{u, v} := inferInstance
    letI : MonoidalCategory PointedCGWH.{u, v} :=
      CategoryTheory.Pointed.smashMonoidalCategory
        CGWH.point.{u, v} CGWH.point_isTerminal
    letI : F.Monoidal :=
      (CategoryTheory.Pointed.costarCoreMonoidal
        CGWH.point.{u, v} CGWH.point_isTerminal).toMonoidal
    F.map ((CGWH.pointHomEquiv Z).symm z) =
      Functor.LaxMonoidal.ε F ≫
        F.map ((CGWH.point_isTerminal.uniqueUpToIso
            CartesianMonoidalCategory.isTerminalTensorUnit).inv ≫
          (CGWH.pointHomEquiv Z).symm z) := by
  dsimp only
  let F := Under.costar CGWH.point.{u, v}
  let _ : BraidedCategory CGWH.{u, v} :=
    BraidedCategory.ofCartesianMonoidalCategory
  let _ : SymmetricCategory CGWH.{u, v} := inferInstance
  let _ : MonoidalCategory PointedCGWH.{u, v} :=
    CategoryTheory.Pointed.smashMonoidalCategory
      CGWH.point.{u, v} CGWH.point_isTerminal
  let core := CategoryTheory.Pointed.costarCoreMonoidal
    CGWH.point.{u, v} CGWH.point_isTerminal
  let _ : F.Monoidal := core.toMonoidal
  let p : CGWH.point.{u, v} ≅ 𝟙_ CGWH.{u, v} :=
    CGWH.point_isTerminal.uniqueUpToIso
      CartesianMonoidalCategory.isTerminalTensorUnit
  let freeGenerator : CGWH.point.{u, v} ⟶
      (CategoryTheory.Pointed.smashUnit CGWH.point.{u, v}).right :=
    coprod.inr
  have hFUnit : (F.obj (𝟙_ CGWH.{u, v})).hom =
      (coprod.inl : CGWH.point.{u, v} ⟶
        CGWH.point.{u, v} ⨿ 𝟙_ CGWH.{u, v}) :=
    (Under.costar_obj_hom CGWH.point.{u, v} (𝟙_ CGWH.{u, v})).trans
      (coprod.inl_desc _ _)
  have hSphere :
      (CategoryTheory.Pointed.smashUnit CGWH.point.{u, v}).hom =
        (coprod.inl : CGWH.point.{u, v} ⟶
          CGWH.point.{u, v} ⨿ CGWH.point.{u, v}) :=
    (Under.costar_obj_hom CGWH.point.{u, v} CGWH.point.{u, v}).trans
      (coprod.inl_desc _ _)
  have hetaRight :
      (((CategoryTheory.Pointed.costarCoreMonoidal
        CGWH.point.{u, v} CGWH.point_isTerminal).toOplaxMonoidal).η).right =
      coprod.desc
        (CategoryTheory.Pointed.smashUnit CGWH.point.{u, v}).hom
        (p.inv ≫ freeGenerator) := by
    simp only [Functor.CoreMonoidal.toOplaxMonoidal_η,
      CategoryTheory.Pointed.costarCoreMonoidal,
      Functor.CoreMonoidal.ofOplaxMonoidal_εIso,
      Iso.symm_inv, asIso_hom]
    rw [Adjunction.leftAdjointOplaxMonoidal_η]
    change (((Under.costarAdjForget CGWH.point.{u, v}).homEquiv
      (𝟙_ CGWH.{u, v})
      (CategoryTheory.Pointed.smashUnit CGWH.point.{u, v})).symm
        (p.inv ≫ freeGenerator)).right = _
    let U := CategoryTheory.Pointed.smashUnit CGWH.point.{u, v}
    let E : (((Under.costar CGWH.point.{u, v}).obj (𝟙_ CGWH.{u, v})) ⟶ U) ≃
        ((𝟙_ CGWH.{u, v}) ⟶ U.right) :=
      (Under.costarAdjForget CGWH.point.{u, v}).homEquiv (𝟙_ CGWH.{u, v}) U
    let g : ((Under.costar CGWH.point.{u, v}).obj (𝟙_ CGWH.{u, v})) ⟶ U :=
      Under.homMk (coprod.desc U.hom (p.inv ≫ freeGenerator)) (by
        have hunit : ((Under.costar CGWH.point.{u, v}).obj (𝟙_ CGWH.{u, v})).hom =
            (coprod.inl : CGWH.point.{u, v} ⟶ CGWH.point.{u, v} ⨿ 𝟙_ CGWH.{u, v}) := hFUnit
        change ((Under.costar CGWH.point.{u, v}).obj (𝟙_ CGWH.{u, v})).hom ≫
          coprod.desc U.hom (p.inv ≫ freeGenerator) = U.hom
        exact (congrArg (fun q => q ≫ coprod.desc U.hom (p.inv ≫ freeGenerator)) hunit).trans
          (coprod.inl_desc _ _))
    have hE : E g = p.inv ≫ freeGenerator := by
      change (coprod.inr : (𝟙_ CGWH.{u, v}) ⟶ CGWH.point.{u, v} ⨿ 𝟙_ CGWH.{u, v}) ≫
        coprod.desc U.hom (p.inv ≫ freeGenerator) = _
      exact coprod.inr_desc _ _
    have hInv : E.symm (p.inv ≫ freeGenerator) = g :=
      (congrArg E.symm hE).symm.trans (E.symm_apply_apply g)
    exact congrArg Under.Hom.right hInv
  let e : F.obj (𝟙_ CGWH.{u, v}) ≅
      CategoryTheory.Pointed.smashUnit CGWH.point.{u, v} :=
    Under.isoMk (coprod.mapIso (Iso.refl _) p.symm) (by
      change (F.obj (𝟙_ CGWH.{u, v})).hom ≫
          coprod.map (𝟙 CGWH.point.{u, v}) p.inv =
        (CategoryTheory.Pointed.smashUnit CGWH.point.{u, v}).hom
      have hInlMap :
          (coprod.inl : CGWH.point.{u, v} ⟶ CGWH.point.{u, v} ⨿ 𝟙_ CGWH.{u, v}) ≫
            coprod.map (𝟙 CGWH.point.{u, v}) p.inv =
              (coprod.inl : CGWH.point.{u, v} ⟶ CGWH.point.{u, v} ⨿ CGWH.point.{u, v}) :=
        (coprod.inl_map _ _).trans (Category.id_comp _)
      exact (congrArg (fun q => q ≫ coprod.map (𝟙 CGWH.point.{u, v}) p.inv) hFUnit).trans
        (hInlMap.trans hSphere.symm))
  have heta : Functor.OplaxMonoidal.η F = e.hom := by
    apply Under.UnderMorphism.ext
    rw [hetaRight]
    rw [hSphere]
    change coprod.desc coprod.inl (p.inv ≫ freeGenerator) =
      coprod.map (𝟙 CGWH.point.{u, v}) p.inv
    apply coprod.hom_ext
    · simp
    · dsimp only [freeGenerator]
      rw [coprod.inr_desc, coprod.inr_map]
  have hCoreInv : core.εIso.inv = e.hom := by
    change Functor.OplaxMonoidal.η F = e.hom
    exact heta
  have hCoreHom : core.εIso.hom = e.inv := by
    apply (cancel_mono e.hom).1
    calc
      core.εIso.hom ≫ e.hom =
          core.εIso.hom ≫ core.εIso.inv := by rw [hCoreInv]
      _ = 𝟙 _ := core.εIso.hom_inv_id
      _ = e.inv ≫ e.hom := e.inv_hom_id.symm
  apply Under.UnderMorphism.ext
  rw [Under.comp_right]
  change coprod.map (𝟙 CGWH.point.{u, v})
      ((CGWH.pointHomEquiv Z).symm z) =
    core.εIso.hom.right ≫
      coprod.map (𝟙 CGWH.point.{u, v})
        (p.inv ≫ (CGWH.pointHomEquiv Z).symm z)
  rw [congrArg Under.Hom.right hCoreHom]
  change coprod.map (𝟙 CGWH.point.{u, v})
      ((CGWH.pointHomEquiv Z).symm z) =
    coprod.map (𝟙 CGWH.point.{u, v}) p.hom ≫
      coprod.map (𝟙 CGWH.point.{u, v})
        (p.inv ≫ (CGWH.pointHomEquiv Z).symm z)
  apply coprod.hom_ext
  · simp
  · simp only [coprod.inr_map_assoc]
    conv_lhs => rw [coprod.inr_map]
    conv_rhs => rw [coprod.inr_map]
    have hp : p.hom ≫
        (p.inv ≫ (CGWH.pointHomEquiv Z).symm z) =
      (CGWH.pointHomEquiv Z).symm z := by
      rw [← Category.assoc, p.hom_inv_id, Category.id_comp]
    conv_rhs => rw [← Category.assoc, hp]

@[instance_reducible]
private noncomputable def costarLaxBraided :
    let F := Under.costar CGWH.point.{u, v}
    letI : BraidedCategory CGWH.{u, v} :=
      BraidedCategory.ofCartesianMonoidalCategory
    letI : SymmetricCategory CGWH.{u, v} := inferInstance
    letI : MonoidalCategory PointedCGWH.{u, v} :=
      CategoryTheory.Pointed.smashMonoidalCategory
        CGWH.point.{u, v} CGWH.point_isTerminal
    letI : SymmetricCategory PointedCGWH.{u, v} :=
      CategoryTheory.Pointed.smashSymmetricCategory
        CGWH.point.{u, v} CGWH.point_isTerminal
    letI : F.Monoidal :=
      (CategoryTheory.Pointed.costarCoreMonoidal
        CGWH.point.{u, v} CGWH.point_isTerminal).toMonoidal
    F.LaxBraided := by
  dsimp only
  let F := Under.costar CGWH.point.{u, v}
  let _ : BraidedCategory CGWH.{u, v} :=
    BraidedCategory.ofCartesianMonoidalCategory
  let _ : SymmetricCategory CGWH.{u, v} := inferInstance
  let _ : MonoidalCategory PointedCGWH.{u, v} :=
    CategoryTheory.Pointed.smashMonoidalCategory
      CGWH.point.{u, v} CGWH.point_isTerminal
  let _ : SymmetricCategory PointedCGWH.{u, v} :=
    CategoryTheory.Pointed.smashSymmetricCategory
      CGWH.point.{u, v} CGWH.point_isTerminal
  let core := CategoryTheory.Pointed.costarCoreMonoidal
    CGWH.point.{u, v} CGWH.point_isTerminal
  let _ : F.Monoidal := core.toMonoidal
  have pointTensor {A B : CGWH.{u, v}}
      (a : 𝟙_ CGWH.{u, v} ⟶ A) (b : 𝟙_ CGWH.{u, v} ⟶ B) :
      (λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫
            ((Functor.LaxMonoidal.ε F ≫ F.map a) ⊗ₘ
              (Functor.LaxMonoidal.ε F ≫ F.map b)) ≫
          Functor.LaxMonoidal.μ F A B =
        Functor.LaxMonoidal.ε F ≫
          F.map ((λ_ (𝟙_ CGWH.{u, v})).inv ≫ (a ⊗ₘ b)) := by
    rw [← tensorHom_comp_tensorHom]
    simp only [Category.assoc]
    rw [Functor.LaxMonoidal.μ_natural]
    rw [MonoidalCategory.tensorHom_def']
    simp only [Category.assoc]
    rw [MonoidalCategory.id_whiskerLeft]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [Functor.LaxMonoidal.left_unitality_inv_assoc]
    rw [← Functor.map_comp]
  refine
    { braided := ?_ }
  intro X Y
  apply PointedCGWH.isSeparator_tensorUnit.def
  intro h
  let k : 𝟙_ PointedCGWH.{u, v} ⟶ F.obj (X ⊗ Y) :=
    h ≫ (core.μIso X Y).hom
  have hk : h = k ≫ (core.μIso X Y).inv := by
    dsimp only [k]
    simp
  rcases freePoint_cases.{u, v} (X ⊗ Y) k with hkzero | ⟨z, hkz⟩
  · rw [hk, hkzero]
    simp
  · let p : CGWH.point.{u, v} ≅ 𝟙_ CGWH.{u, v} :=
      CGWH.point_isTerminal.uniqueUpToIso
        CartesianMonoidalCategory.isTerminalTensorUnit
    let x : X := CartesianMonoidalCategory.fst X Y z
    let y : Y := CartesianMonoidalCategory.snd X Y z
    let qX : CGWH.point.{u, v} ⟶ X :=
      (CGWH.pointHomEquiv X).symm x
    let qY : CGWH.point.{u, v} ⟶ Y :=
      (CGWH.pointHomEquiv Y).symm y
    let qXY : CGWH.point.{u, v} ⟶ X ⊗ Y :=
      (CGWH.pointHomEquiv (X ⊗ Y)).symm z
    let a : 𝟙_ CGWH.{u, v} ⟶ X := p.inv ≫ qX
    let b : 𝟙_ CGWH.{u, v} ⟶ Y := p.inv ≫ qY
    have hPair : p.hom ≫ (λ_ (𝟙_ CGWH.{u, v})).inv ≫
        (a ⊗ₘ b) = CartesianMonoidalCategory.lift qX qY := by
      apply CartesianMonoidalCategory.hom_ext
      · simp only [Category.assoc,
          CartesianMonoidalCategory.tensorHom_fst,
          CartesianMonoidalCategory.lift_fst]
        have ht : p.hom ≫ (λ_ (𝟙_ CGWH.{u, v})).inv ≫
            CartesianMonoidalCategory.fst (𝟙_ CGWH.{u, v})
              (𝟙_ CGWH.{u, v}) = p.hom :=
          CartesianMonoidalCategory.isTerminalTensorUnit.hom_ext _ _
        change (p.hom ≫ (λ_ (𝟙_ CGWH.{u, v})).inv ≫
            CartesianMonoidalCategory.fst (𝟙_ CGWH.{u, v})
              (𝟙_ CGWH.{u, v})) ≫ a = qX
        rw [ht]
        dsimp only [a]
        rw [← Category.assoc, p.hom_inv_id, Category.id_comp]
      · simp only [Category.assoc,
          CartesianMonoidalCategory.tensorHom_snd,
          CartesianMonoidalCategory.lift_snd]
        have ht : p.hom ≫ (λ_ (𝟙_ CGWH.{u, v})).inv ≫
            CartesianMonoidalCategory.snd (𝟙_ CGWH.{u, v})
              (𝟙_ CGWH.{u, v}) = p.hom :=
          CartesianMonoidalCategory.isTerminalTensorUnit.hom_ext _ _
        change (p.hom ≫ (λ_ (𝟙_ CGWH.{u, v})).inv ≫
            CartesianMonoidalCategory.snd (𝟙_ CGWH.{u, v})
              (𝟙_ CGWH.{u, v})) ≫ b = qY
        rw [ht]
        dsimp only [b]
        rw [← Category.assoc, p.hom_inv_id, Category.id_comp]
    have hQ : CartesianMonoidalCategory.lift qX qY = qXY := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [CartesianMonoidalCategory.lift_fst]
        apply ConcreteCategory.hom_ext
        intro t
        have hProjection : CartesianMonoidalCategory.fst X Y
            ((CGWH.pointHomEquiv (X ⊗ Y)).symm z t) = x :=
          congrArg (ConcreteCategory.hom (CartesianMonoidalCategory.fst X Y))
            (CGWH.pointHomEquiv_symm_apply_apply (X ⊗ Y) z t)
        exact (CGWH.pointHomEquiv_symm_apply_apply X x t).trans hProjection.symm
      · rw [CartesianMonoidalCategory.lift_snd]
        apply ConcreteCategory.hom_ext
        intro t
        have hProjection : CartesianMonoidalCategory.snd X Y
            ((CGWH.pointHomEquiv (X ⊗ Y)).symm z t) = y :=
          congrArg (ConcreteCategory.hom (CartesianMonoidalCategory.snd X Y))
            (CGWH.pointHomEquiv_symm_apply_apply (X ⊗ Y) z t)
        exact (CGWH.pointHomEquiv_symm_apply_apply Y y t).trans hProjection.symm
    have hRaw : (λ_ (𝟙_ CGWH.{u, v})).inv ≫ (a ⊗ₘ b) =
        p.inv ≫ qXY := by
      apply (cancel_epi p.hom).1
      calc
        p.hom ≫ ((λ_ (𝟙_ CGWH.{u, v})).inv ≫ (a ⊗ₘ b)) =
            CartesianMonoidalCategory.lift qX qY := by
              simpa only [Category.assoc] using hPair
        _ = qXY := hQ
        _ = p.hom ≫ (p.inv ≫ qXY) := by simp
    let fa : 𝟙_ PointedCGWH.{u, v} ⟶ F.obj X :=
      Functor.LaxMonoidal.ε F ≫ F.map a
    let fb : 𝟙_ PointedCGWH.{u, v} ⟶ F.obj Y :=
      Functor.LaxMonoidal.ε F ≫ F.map b
    let r : 𝟙_ PointedCGWH.{u, v} ⟶ F.obj X ⊗ F.obj Y :=
      (λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫ (fa ⊗ₘ fb)
    have hrμ : r ≫ (core.μIso X Y).hom = F.map qXY := by
      change (λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫
            ((Functor.LaxMonoidal.ε (Under.costar CGWH.point.{u, v}) ≫
                (Under.costar CGWH.point.{u, v}).map a) ⊗ₘ
              (Functor.LaxMonoidal.ε (Under.costar CGWH.point.{u, v}) ≫
                (Under.costar CGWH.point.{u, v}).map b)) ≫
          Functor.LaxMonoidal.μ (Under.costar CGWH.point.{u, v}) X Y =
        (Under.costar CGWH.point.{u, v}).map qXY
      rw [pointTensor a b, hRaw]
      exact (freePoint_eq_coreUnit_map.{u, v} (X ⊗ Y) z).symm
    have hr : h = r := by
      apply (cancel_mono (core.μIso X Y).hom).1
      rw [hrμ]
      change k = F.map qXY
      exact hkz
    let z' : (Y ⊗ X : CGWH.{u, v}) :=
      ConcreteCategory.hom (β_ X Y).hom z
    let qYX : CGWH.point.{u, v} ⟶ Y ⊗ X :=
      (CGWH.pointHomEquiv (Y ⊗ X)).symm z'
    have hQSwap : qXY ≫ (β_ X Y).hom = qYX := by
      apply ConcreteCategory.hom_ext
      intro t
      have hBraidedPoint : (β_ X Y).hom
          ((CGWH.pointHomEquiv (X ⊗ Y)).symm z t) = z' :=
        congrArg (ConcreteCategory.hom (β_ X Y).hom)
          (CGWH.pointHomEquiv_symm_apply_apply (X ⊗ Y) z t)
      exact hBraidedPoint.trans
        (CGWH.pointHomEquiv_symm_apply_apply (Y ⊗ X) z' t).symm
    let r' : 𝟙_ PointedCGWH.{u, v} ⟶ F.obj Y ⊗ F.obj X :=
      (λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫ (fb ⊗ₘ fa)
    have hRawSwap : (λ_ (𝟙_ CGWH.{u, v})).inv ≫ (b ⊗ₘ a) =
        p.inv ≫ qYX := by
      have hPairSwap : p.hom ≫ (λ_ (𝟙_ CGWH.{u, v})).inv ≫
          (b ⊗ₘ a) = CartesianMonoidalCategory.lift qY qX := by
        apply CartesianMonoidalCategory.hom_ext
        · simp only [Category.assoc,
            CartesianMonoidalCategory.tensorHom_fst,
            CartesianMonoidalCategory.lift_fst]
          have ht : p.hom ≫ (λ_ (𝟙_ CGWH.{u, v})).inv ≫
              CartesianMonoidalCategory.fst (𝟙_ CGWH.{u, v})
                (𝟙_ CGWH.{u, v}) = p.hom :=
            CartesianMonoidalCategory.isTerminalTensorUnit.hom_ext _ _
          change (p.hom ≫ (λ_ (𝟙_ CGWH.{u, v})).inv ≫
              CartesianMonoidalCategory.fst (𝟙_ CGWH.{u, v})
                (𝟙_ CGWH.{u, v})) ≫ b = qY
          rw [ht]
          dsimp only [b]
          rw [← Category.assoc, p.hom_inv_id, Category.id_comp]
        · simp only [Category.assoc,
            CartesianMonoidalCategory.tensorHom_snd,
            CartesianMonoidalCategory.lift_snd]
          have ht : p.hom ≫ (λ_ (𝟙_ CGWH.{u, v})).inv ≫
              CartesianMonoidalCategory.snd (𝟙_ CGWH.{u, v})
                (𝟙_ CGWH.{u, v}) = p.hom :=
            CartesianMonoidalCategory.isTerminalTensorUnit.hom_ext _ _
          change (p.hom ≫ (λ_ (𝟙_ CGWH.{u, v})).inv ≫
              CartesianMonoidalCategory.snd (𝟙_ CGWH.{u, v})
                (𝟙_ CGWH.{u, v})) ≫ a = qX
          rw [ht]
          dsimp only [a]
          rw [← Category.assoc, p.hom_inv_id, Category.id_comp]
      have hQ' : CartesianMonoidalCategory.lift qY qX = qYX := by
        apply CartesianMonoidalCategory.hom_ext
        · rw [CartesianMonoidalCategory.lift_fst, ← hQSwap,
            Category.assoc, CartesianMonoidalCategory.braiding_hom_fst,
            ← hQ, CartesianMonoidalCategory.lift_snd]
        · rw [CartesianMonoidalCategory.lift_snd, ← hQSwap,
            Category.assoc, CartesianMonoidalCategory.braiding_hom_snd,
            ← hQ, CartesianMonoidalCategory.lift_fst]
      apply (cancel_epi p.hom).1
      calc
        p.hom ≫ ((λ_ (𝟙_ CGWH.{u, v})).inv ≫ (b ⊗ₘ a)) =
            CartesianMonoidalCategory.lift qY qX := by
              simpa only [Category.assoc] using hPairSwap
        _ = qYX := hQ'
        _ = p.hom ≫ (p.inv ≫ qYX) := by simp
    have hrμ' : r' ≫ (core.μIso Y X).hom = F.map qYX := by
      change (λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫
            ((Functor.LaxMonoidal.ε (Under.costar CGWH.point.{u, v}) ≫
                (Under.costar CGWH.point.{u, v}).map b) ⊗ₘ
              (Functor.LaxMonoidal.ε (Under.costar CGWH.point.{u, v}) ≫
                (Under.costar CGWH.point.{u, v}).map a)) ≫
          Functor.LaxMonoidal.μ (Under.costar CGWH.point.{u, v}) Y X =
        (Under.costar CGWH.point.{u, v}).map qYX
      rw [pointTensor b a, hRawSwap]
      exact (freePoint_eq_coreUnit_map.{u, v} (Y ⊗ X) z').symm
    have hbraid : r ≫ (β_ (F.obj X) (F.obj Y)).hom = r' := by
      dsimp only [r, r']
      simp only [Category.assoc]
      rw [BraidedCategory.braiding_naturality]
      rw [← Category.assoc, leftUnitor_inv_braiding]
      rw [unitors_inv_equal]
    have hStart : h ≫ (core.μIso X Y).hom ≫ F.map (β_ X Y).hom =
        r ≫ (core.μIso X Y).hom ≫ F.map (β_ X Y).hom :=
      congrArg (fun t ↦ t ≫ (core.μIso X Y).hom ≫ F.map (β_ X Y).hom) hr
    have hMiddle : r ≫ (core.μIso X Y).hom ≫ F.map (β_ X Y).hom =
        F.map qXY ≫ F.map (β_ X Y).hom := by
      exact (Category.assoc _ _ _).symm.trans
        (congrArg (fun t ↦ t ≫ F.map (β_ X Y).hom) hrμ)
    have hSwap : F.map qXY ≫ F.map (β_ X Y).hom = F.map qYX := by
      exact (F.map_comp qXY (β_ X Y).hom).symm.trans (congrArg F.map hQSwap)
    have hBraidValue : r' ≫ (core.μIso Y X).hom =
        r ≫ (β_ (F.obj X) (F.obj Y)).hom ≫ (core.μIso Y X).hom :=
      (congrArg (fun t ↦ t ≫ (core.μIso Y X).hom) hbraid).symm.trans
        (Category.assoc _ _ _)
    have hEnd : r ≫ (β_ (F.obj X) (F.obj Y)).hom ≫ (core.μIso Y X).hom =
        h ≫ (β_ (F.obj X) (F.obj Y)).hom ≫ (core.μIso Y X).hom :=
      congrArg (fun t ↦ t ≫ (β_ (F.obj X) (F.obj Y)).hom ≫
        (core.μIso Y X).hom) hr.symm
    exact hStart.trans (hMiddle.trans (hSwap.trans
      (hrμ'.symm.trans (hBraidValue.trans hEnd))))

/-- The enriched identity is the freely based raw identity matrix. -/
theorem enrichedCategory_id (n : OrthogonalIndex) :
    @eId PointedCGWH.{u, v} _ _ OrthogonalIndex
        (enrichedCategory.{u, v}) n =
      matrixPoint.{u, v} (OrthogonalMatrixHom.id n) := by
  let F := Under.costar CGWH.point.{u, v}
  let _ : EnrichedCategory CGWH.{u, v} OrthogonalIndex :=
    rawEnrichedCategory.{u, v}
  let _ : BraidedCategory CGWH.{u, v} :=
    BraidedCategory.ofCartesianMonoidalCategory
  let _ : SymmetricCategory CGWH.{u, v} := inferInstance
  let _ : MonoidalCategory PointedCGWH.{u, v} :=
    CategoryTheory.Pointed.smashMonoidalCategory
      CGWH.point.{u, v} CGWH.point_isTerminal
  let core := CategoryTheory.Pointed.costarCoreMonoidal
    CGWH.point.{u, v} CGWH.point_isTerminal
  let _ : F.Monoidal :=
    core.toMonoidal
  change Functor.LaxMonoidal.ε F ≫ F.map (rawIdentity.{u, v} n) =
    F.map ((CGWH.pointHomEquiv (rawHomCGWH.{u, v} n n)).symm
      (ULift.up (OrthogonalMatrixHom.id n)))
  apply Under.UnderMorphism.ext
  rw [Under.comp_right]
  change core.εIso.hom.right ≫
      coprod.map (𝟙 CGWH.point.{u, v}) (rawIdentity.{u, v} n) =
    coprod.map (𝟙 CGWH.point.{u, v})
      ((CGWH.pointHomEquiv (rawHomCGWH.{u, v} n n)).symm
        (ULift.up (OrthogonalMatrixHom.id n)))
  let p : CGWH.point.{u, v} ≅ 𝟙_ CGWH.{u, v} :=
    CGWH.point_isTerminal.uniqueUpToIso
      CartesianMonoidalCategory.isTerminalTensorUnit
  let freePoint : CGWH.point.{u, v} ⟶
      (CategoryTheory.Pointed.smashUnit CGWH.point.{u, v}).right :=
    coprod.inr
  have hFUnit : (F.obj (𝟙_ CGWH.{u, v})).hom =
      (coprod.inl : CGWH.point.{u, v} ⟶
        CGWH.point.{u, v} ⨿ 𝟙_ CGWH.{u, v}) :=
    (Under.costar_obj_hom CGWH.point.{u, v} (𝟙_ CGWH.{u, v})).trans
      (coprod.inl_desc _ _)
  have hSphere :
      (CategoryTheory.Pointed.smashUnit CGWH.point.{u, v}).hom =
        (coprod.inl : CGWH.point.{u, v} ⟶
          CGWH.point.{u, v} ⨿ CGWH.point.{u, v}) :=
    (Under.costar_obj_hom CGWH.point.{u, v} CGWH.point.{u, v}).trans
      (coprod.inl_desc _ _)
  have hetaRight :
      (((CategoryTheory.Pointed.costarCoreMonoidal
        CGWH.point.{u, v} CGWH.point_isTerminal).toOplaxMonoidal).η).right =
      coprod.desc
        (CategoryTheory.Pointed.smashUnit CGWH.point.{u, v}).hom
        (p.inv ≫ freePoint) := by
    simp only [Functor.CoreMonoidal.toOplaxMonoidal_η,
      CategoryTheory.Pointed.costarCoreMonoidal,
      Functor.CoreMonoidal.ofOplaxMonoidal_εIso,
      Iso.symm_inv, asIso_hom]
    rw [Adjunction.leftAdjointOplaxMonoidal_η]
    change (((Under.costarAdjForget CGWH.point.{u, v}).homEquiv
      (𝟙_ CGWH.{u, v})
      (CategoryTheory.Pointed.smashUnit CGWH.point.{u, v})).symm
        (p.inv ≫ freePoint)).right = _
    let U := CategoryTheory.Pointed.smashUnit CGWH.point.{u, v}
    let E : (((Under.costar CGWH.point.{u, v}).obj (𝟙_ CGWH.{u, v})) ⟶ U) ≃
        ((𝟙_ CGWH.{u, v}) ⟶ U.right) :=
      (Under.costarAdjForget CGWH.point.{u, v}).homEquiv (𝟙_ CGWH.{u, v}) U
    let g : ((Under.costar CGWH.point.{u, v}).obj (𝟙_ CGWH.{u, v})) ⟶ U :=
      Under.homMk (coprod.desc U.hom (p.inv ≫ freePoint)) (by
        have hunit : ((Under.costar CGWH.point.{u, v}).obj (𝟙_ CGWH.{u, v})).hom =
            (coprod.inl : CGWH.point.{u, v} ⟶ CGWH.point.{u, v} ⨿ 𝟙_ CGWH.{u, v}) := hFUnit
        change ((Under.costar CGWH.point.{u, v}).obj (𝟙_ CGWH.{u, v})).hom ≫
          coprod.desc U.hom (p.inv ≫ freePoint) = U.hom
        exact (congrArg (fun q => q ≫ coprod.desc U.hom (p.inv ≫ freePoint)) hunit).trans
          (coprod.inl_desc _ _))
    have hE : E g = p.inv ≫ freePoint := by
      change (coprod.inr : (𝟙_ CGWH.{u, v}) ⟶ CGWH.point.{u, v} ⨿ 𝟙_ CGWH.{u, v}) ≫
        coprod.desc U.hom (p.inv ≫ freePoint) = _
      exact coprod.inr_desc _ _
    have hInv : E.symm (p.inv ≫ freePoint) = g :=
      (congrArg E.symm hE).symm.trans (E.symm_apply_apply g)
    exact congrArg Under.Hom.right hInv
  let e : F.obj (𝟙_ CGWH.{u, v}) ≅
      CategoryTheory.Pointed.smashUnit CGWH.point.{u, v} :=
    Under.isoMk (coprod.mapIso (Iso.refl _) p.symm) (by
      change (F.obj (𝟙_ CGWH.{u, v})).hom ≫
          coprod.map (𝟙 CGWH.point.{u, v}) p.inv =
        (CategoryTheory.Pointed.smashUnit CGWH.point.{u, v}).hom
      have hInlMap :
          (coprod.inl : CGWH.point.{u, v} ⟶ CGWH.point.{u, v} ⨿ 𝟙_ CGWH.{u, v}) ≫
            coprod.map (𝟙 CGWH.point.{u, v}) p.inv =
              (coprod.inl : CGWH.point.{u, v} ⟶ CGWH.point.{u, v} ⨿ CGWH.point.{u, v}) :=
        (coprod.inl_map _ _).trans (Category.id_comp _)
      exact (congrArg (fun q => q ≫ coprod.map (𝟙 CGWH.point.{u, v}) p.inv) hFUnit).trans
        (hInlMap.trans hSphere.symm))
  have heta : Functor.OplaxMonoidal.η F = e.hom := by
    apply Under.UnderMorphism.ext
    rw [hetaRight]
    rw [hSphere]
    change coprod.desc coprod.inl (p.inv ≫ freePoint) =
      coprod.map (𝟙 CGWH.point.{u, v}) p.inv
    apply coprod.hom_ext
    · simp
    · dsimp only [freePoint]
      rw [coprod.inr_desc, coprod.inr_map]
  have hCoreInv : core.εIso.inv = e.hom := by
    change Functor.OplaxMonoidal.η F = e.hom
    exact heta
  have hCoreHom : core.εIso.hom = e.inv := by
    apply (cancel_mono e.hom).1
    calc
      core.εIso.hom ≫ e.hom =
          core.εIso.hom ≫ core.εIso.inv := by rw [hCoreInv]
      _ = 𝟙 _ := core.εIso.hom_inv_id
      _ = e.inv ≫ e.hom := e.inv_hom_id.symm
  rw [congrArg Under.Hom.right hCoreHom]
  change coprod.map (𝟙 CGWH.point.{u, v}) p.hom ≫
      coprod.map (𝟙 CGWH.point.{u, v}) (rawIdentity.{u, v} n) =
    coprod.map (𝟙 CGWH.point.{u, v})
      ((CGWH.pointHomEquiv (rawHomCGWH.{u, v} n n)).symm
        (ULift.up (OrthogonalMatrixHom.id n)))
  apply coprod.hom_ext
  · simp
  · rw [← Category.assoc, coprod.inr_map, Category.assoc,
      coprod.inr_map]
    have hPoint : p.hom ≫ rawIdentity.{u, v} n =
        (CGWH.pointHomEquiv (rawHomCGWH.{u, v} n n)).symm
          (ULift.up (OrthogonalMatrixHom.id n)) := by
      apply ConcreteCategory.hom_ext
      intro x
      rw [ConcreteCategory.comp_apply, rawIdentity]
      cases x
      rfl
    slice_lhs 1 2 => rw [hPoint]
    rw [coprod.inr_map]

/-- Composition multiplies matrices in categorical order and absorbs each
basepoint face. -/
theorem enrichedCategory_comp
    {m n p : OrthogonalIndex}
    (A : OrthogonalMatrixHom m n)
    (B : OrthogonalMatrixHom n p) :
    let a : 𝟙_ PointedCGWH.{u, v} ⟶ hom.{u, v} m n :=
      matrixPoint.{u, v} A
    let b : 𝟙_ PointedCGWH.{u, v} ⟶ hom.{u, v} n p :=
      matrixPoint.{u, v} B
    let ba : 𝟙_ PointedCGWH.{u, v} ⟶ hom.{u, v} m p :=
      matrixPoint.{u, v} (OrthogonalMatrixHom.comp A B)
    ((λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫ (a ⊗ₘ b) ≫
        @eComp PointedCGWH.{u, v} _ _ OrthogonalIndex
          (enrichedCategory.{u, v}) m n p = ba) ∧
    ((λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫
        ((0 : 𝟙_ PointedCGWH.{u, v} ⟶ hom.{u, v} m n) ⊗ₘ b) ≫
        @eComp PointedCGWH.{u, v} _ _ OrthogonalIndex
          (enrichedCategory.{u, v}) m n p = 0) ∧
    ((λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫
        (a ⊗ₘ (0 : 𝟙_ PointedCGWH.{u, v} ⟶ hom.{u, v} n p)) ≫
        @eComp PointedCGWH.{u, v} _ _ OrthogonalIndex
          (enrichedCategory.{u, v}) m n p = 0) := by
  dsimp only
  let F := Under.costar CGWH.point.{u, v}
  let _ : EnrichedCategory CGWH.{u, v} OrthogonalIndex :=
    rawEnrichedCategory.{u, v}
  let _ : BraidedCategory CGWH.{u, v} :=
    BraidedCategory.ofCartesianMonoidalCategory
  let _ : SymmetricCategory CGWH.{u, v} := inferInstance
  let _ : MonoidalCategory PointedCGWH.{u, v} :=
    CategoryTheory.Pointed.smashMonoidalCategory
      CGWH.point.{u, v} CGWH.point_isTerminal
  let core := CategoryTheory.Pointed.costarCoreMonoidal
    CGWH.point.{u, v} CGWH.point_isTerminal
  let _ : F.Monoidal := core.toMonoidal
  have pointTensor {X Y : CGWH.{u, v}}
      (x : 𝟙_ CGWH.{u, v} ⟶ X) (y : 𝟙_ CGWH.{u, v} ⟶ Y) :
      (λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫
            ((Functor.LaxMonoidal.ε F ≫ F.map x) ⊗ₘ
              (Functor.LaxMonoidal.ε F ≫ F.map y)) ≫
          Functor.LaxMonoidal.μ F X Y =
        Functor.LaxMonoidal.ε F ≫
          F.map ((λ_ (𝟙_ CGWH.{u, v})).inv ≫ (x ⊗ₘ y)) := by
    rw [← tensorHom_comp_tensorHom]
    simp only [Category.assoc]
    rw [Functor.LaxMonoidal.μ_natural]
    rw [MonoidalCategory.tensorHom_def']
    simp only [Category.assoc]
    rw [MonoidalCategory.id_whiskerLeft]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [Functor.LaxMonoidal.left_unitality_inv_assoc]
    rw [← Functor.map_comp]
  have matrixPoint_eq {a b : OrthogonalIndex}
      (M : OrthogonalMatrixHom a b) :
      matrixPoint.{u, v} M = Functor.LaxMonoidal.ε F ≫
        F.map (rawPointFromUnit.{u, v} M) := by
    exact freePoint_eq_coreUnit_map.{u, v}
      (rawHomCGWH.{u, v} a b) (ULift.up M)
  constructor
  · rw [matrixPoint_eq A,
      matrixPoint_eq B,
      matrixPoint_eq
        (OrthogonalMatrixHom.comp A B)]
    change (λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫
          ((Functor.LaxMonoidal.ε F ≫
              F.map (rawPointFromUnit.{u, v} A)) ⊗ₘ
            (Functor.LaxMonoidal.ε F ≫
              F.map (rawPointFromUnit.{u, v} B))) ≫
        Functor.LaxMonoidal.μ F (rawHomCGWH.{u, v} m n)
          (rawHomCGWH.{u, v} n p) ≫
        F.map (rawComp.{u, v} m n p) =
      Functor.LaxMonoidal.ε F ≫
        F.map (rawPointFromUnit.{u, v}
          (OrthogonalMatrixHom.comp A B))
    slice_lhs 1 3 => rw [pointTensor
      (rawPointFromUnit.{u, v} A) (rawPointFromUnit.{u, v} B)]
    rw [Category.assoc, ← F.map_comp]
    change Functor.LaxMonoidal.ε F ≫
        F.map (((λ_ (𝟙_ CGWH.{u, v})).inv ≫
          (rawPointFromUnit.{u, v} A ⊗ₘ
            rawPointFromUnit.{u, v} B)) ≫
          rawComp.{u, v} m n p) =
      Functor.LaxMonoidal.ε F ≫
        F.map (rawPointFromUnit.{u, v}
          (OrthogonalMatrixHom.comp A B))
    apply congrArg (fun k => Functor.LaxMonoidal.ε F ≫ k)
    apply congrArg (fun k => F.map k)
    let pUnit : CGWH.point.{u, v} ≅ 𝟙_ CGWH.{u, v} :=
      CGWH.point_isTerminal.uniqueUpToIso
        CartesianMonoidalCategory.isTerminalTensorUnit
    apply (cancel_epi pUnit.hom).1
    let qA : CGWH.point.{u, v} ⟶ rawHomCGWH.{u, v} m n :=
      (CGWH.pointHomEquiv (rawHomCGWH.{u, v} m n)).symm (ULift.up A)
    let qB : CGWH.point.{u, v} ⟶ rawHomCGWH.{u, v} n p :=
      (CGWH.pointHomEquiv (rawHomCGWH.{u, v} n p)).symm (ULift.up B)
    let qAB : CGWH.point.{u, v} ⟶ rawHomCGWH.{u, v} m p :=
      (CGWH.pointHomEquiv (rawHomCGWH.{u, v} m p)).symm
        (ULift.up (OrthogonalMatrixHom.comp A B))
    have hpA : pUnit.hom ≫ rawPointFromUnit.{u, v} A = qA := by
      change pUnit.hom ≫ (pUnit.inv ≫ qA) = qA
      rw [← Category.assoc, pUnit.hom_inv_id, Category.id_comp]
    have hpB : pUnit.hom ≫ rawPointFromUnit.{u, v} B = qB := by
      change pUnit.hom ≫ (pUnit.inv ≫ qB) = qB
      rw [← Category.assoc, pUnit.hom_inv_id, Category.id_comp]
    have hpAB : pUnit.hom ≫
        rawPointFromUnit.{u, v} (OrthogonalMatrixHom.comp A B) = qAB := by
      change pUnit.hom ≫ (pUnit.inv ≫ qAB) = qAB
      rw [← Category.assoc, pUnit.hom_inv_id, Category.id_comp]
    have hPair : pUnit.hom ≫ (λ_ (𝟙_ CGWH.{u, v})).inv ≫
        (rawPointFromUnit.{u, v} A ⊗ₘ rawPointFromUnit.{u, v} B) =
      CartesianMonoidalCategory.lift qA qB := by
      apply CartesianMonoidalCategory.hom_ext
      · simp only [Category.assoc,
          CartesianMonoidalCategory.tensorHom_fst,
          CartesianMonoidalCategory.lift_fst]
        have ht : pUnit.hom ≫ (λ_ (𝟙_ CGWH.{u, v})).inv ≫
            CartesianMonoidalCategory.fst (𝟙_ CGWH.{u, v})
              (𝟙_ CGWH.{u, v}) = pUnit.hom :=
          CartesianMonoidalCategory.isTerminalTensorUnit.hom_ext _ _
        calc
          _ = (pUnit.hom ≫ (λ_ (𝟙_ CGWH.{u, v})).inv ≫
                CartesianMonoidalCategory.fst (𝟙_ CGWH.{u, v})
                  (𝟙_ CGWH.{u, v})) ≫
              rawPointFromUnit.{u, v} A := by
                simp only [Category.assoc]
          _ = pUnit.hom ≫ rawPointFromUnit.{u, v} A := by rw [ht]
          _ = qA := hpA
      · simp only [Category.assoc,
          CartesianMonoidalCategory.tensorHom_snd,
          CartesianMonoidalCategory.lift_snd]
        have ht : pUnit.hom ≫ (λ_ (𝟙_ CGWH.{u, v})).inv ≫
            CartesianMonoidalCategory.snd (𝟙_ CGWH.{u, v})
              (𝟙_ CGWH.{u, v}) = pUnit.hom :=
          CartesianMonoidalCategory.isTerminalTensorUnit.hom_ext _ _
        calc
          _ = (pUnit.hom ≫ (λ_ (𝟙_ CGWH.{u, v})).inv ≫
                CartesianMonoidalCategory.snd (𝟙_ CGWH.{u, v})
                  (𝟙_ CGWH.{u, v})) ≫
              rawPointFromUnit.{u, v} B := by
                simp only [Category.assoc]
          _ = pUnit.hom ≫ rawPointFromUnit.{u, v} B := by rw [ht]
          _ = qB := hpB
    change pUnit.hom ≫
        (((λ_ (𝟙_ CGWH.{u, v})).inv ≫
          (rawPointFromUnit.{u, v} A ⊗ₘ
            rawPointFromUnit.{u, v} B)) ≫ rawComp.{u, v} m n p) =
      pUnit.hom ≫
        rawPointFromUnit.{u, v} (OrthogonalMatrixHom.comp A B)
    calc
      _ = (pUnit.hom ≫ (λ_ (𝟙_ CGWH.{u, v})).inv ≫
          (rawPointFromUnit.{u, v} A ⊗ₘ
            rawPointFromUnit.{u, v} B)) ≫ rawComp.{u, v} m n p := by
            simp only [Category.assoc]
      _ = CartesianMonoidalCategory.lift qA qB ≫
          rawComp.{u, v} m n p := by rw [hPair]
      _ = qAB := by
        apply ConcreteCategory.hom_ext
        intro x
        rw [ConcreteCategory.comp_apply, rawComp_apply]
        have hfst := ConcreteCategory.congr_hom
          (CartesianMonoidalCategory.lift_fst qA qB) x
        have hsnd := ConcreteCategory.congr_hom
          (CartesianMonoidalCategory.lift_snd qA qB) x
        rw [ConcreteCategory.comp_apply] at hfst hsnd
        have hfst' :
            (ConcreteCategory.hom
              (CartesianMonoidalCategory.fst
                (rawHomCGWH.{u, v} m n) (rawHomCGWH.{u, v} n p))
              (ConcreteCategory.hom
                (CartesianMonoidalCategory.lift qA qB) x)).down = A := by
          rw [hfst]
          cases x
          rfl
        have hsnd' :
            (ConcreteCategory.hom
              (CartesianMonoidalCategory.snd
                (rawHomCGWH.{u, v} m n) (rawHomCGWH.{u, v} n p))
              (ConcreteCategory.hom
                (CartesianMonoidalCategory.lift qA qB) x)).down = B := by
          rw [hsnd]
          cases x
          rfl
        rw [hfst', hsnd']
        cases x
        rfl
      _ = _ := hpAB.symm
  constructor
  · have hz :
        ((0 : 𝟙_ PointedCGWH.{u, v} ⟶ hom.{u, v} m n) ⊗ₘ
          matrixPoint.{u, v} B) = 0 := by
      let _ : (tensorRight (𝟙_ PointedCGWH.{u, v})).PreservesZeroMorphisms :=
        inferInstance
      rw [MonoidalCategory.tensorHom_def]
      change (tensorRight (𝟙_ PointedCGWH.{u, v})).map 0 ≫ _ = 0
      rw [Functor.map_zero, zero_comp]
    have hTensorZero :
        (λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫
        ((0 : 𝟙_ PointedCGWH.{u, v} ⟶ hom.{u, v} m n) ⊗ₘ matrixPoint.{u, v} B) ≫
            @eComp PointedCGWH.{u, v} _ _ OrthogonalIndex (enrichedCategory.{u, v}) m n p =
          (λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫
            (0 : (𝟙_ PointedCGWH.{u, v} ⊗ 𝟙_ PointedCGWH.{u, v}) ⟶
              hom.{u, v} m n ⊗ hom.{u, v} n p) ≫
            @eComp PointedCGWH.{u, v} _ _ OrthogonalIndex (enrichedCategory.{u, v}) m n p :=
      congrArg (fun q => (λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫ q ≫
        @eComp PointedCGWH.{u, v} _ _ OrthogonalIndex (enrichedCategory.{u, v}) m n p) hz
    have hCompZero :
        (0 : (𝟙_ PointedCGWH.{u, v} ⊗ 𝟙_ PointedCGWH.{u, v}) ⟶
          hom.{u, v} m n ⊗ hom.{u, v} n p) ≫
            @eComp PointedCGWH.{u, v} _ _ OrthogonalIndex (enrichedCategory.{u, v}) m n p =
          (0 : (𝟙_ PointedCGWH.{u, v} ⊗ 𝟙_ PointedCGWH.{u, v}) ⟶ hom.{u, v} m p) :=
      zero_comp (f := @eComp PointedCGWH.{u, v} _ _ OrthogonalIndex
        (enrichedCategory.{u, v}) m n p)
    exact hTensorZero.trans
      ((congrArg (fun q => (λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫ q) hCompZero).trans
        (comp_zero (f := (λ_ (𝟙_ PointedCGWH.{u, v})).inv)))
  · have hz :
        (matrixPoint.{u, v} A ⊗ₘ
          (0 : 𝟙_ PointedCGWH.{u, v} ⟶ hom.{u, v} n p)) = 0 := by
      let _ : (tensorLeft (𝟙_ PointedCGWH.{u, v})).PreservesZeroMorphisms :=
        inferInstance
      rw [MonoidalCategory.tensorHom_def']
      change (tensorLeft (𝟙_ PointedCGWH.{u, v})).map 0 ≫ _ = 0
      rw [Functor.map_zero, zero_comp]
    have hTensorZero :
        (λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫
        (matrixPoint.{u, v} A ⊗ₘ (0 : 𝟙_ PointedCGWH.{u, v} ⟶ hom.{u, v} n p)) ≫
            @eComp PointedCGWH.{u, v} _ _ OrthogonalIndex (enrichedCategory.{u, v}) m n p =
          (λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫
            (0 : (𝟙_ PointedCGWH.{u, v} ⊗ 𝟙_ PointedCGWH.{u, v}) ⟶
              hom.{u, v} m n ⊗ hom.{u, v} n p) ≫
            @eComp PointedCGWH.{u, v} _ _ OrthogonalIndex (enrichedCategory.{u, v}) m n p :=
      congrArg (fun q => (λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫ q ≫
        @eComp PointedCGWH.{u, v} _ _ OrthogonalIndex (enrichedCategory.{u, v}) m n p) hz
    have hCompZero :
        (0 : (𝟙_ PointedCGWH.{u, v} ⊗ 𝟙_ PointedCGWH.{u, v}) ⟶
          hom.{u, v} m n ⊗ hom.{u, v} n p) ≫
            @eComp PointedCGWH.{u, v} _ _ OrthogonalIndex (enrichedCategory.{u, v}) m n p =
          (0 : (𝟙_ PointedCGWH.{u, v} ⊗ 𝟙_ PointedCGWH.{u, v}) ⟶ hom.{u, v} m p) :=
      zero_comp (f := @eComp PointedCGWH.{u, v} _ _ OrthogonalIndex
        (enrichedCategory.{u, v}) m n p)
    exact hTensorZero.trans
      ((congrArg (fun q => (λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫ q) hCompZero).trans
        (comp_zero (f := (λ_ (𝟙_ PointedCGWH.{u, v})).inv)))

/-- The continuous block sum of two orthogonal matrix morphisms. -/
private noncomputable def rawBlockSum
    (m m' n n' : OrthogonalIndex) :
    (rawHomCGWH.{u, v} m m' ⊗ rawHomCGWH.{u, v} n n') ⟶
      rawHomCGWH.{u, v} (m + n) (m' + n') := by
  let X := rawHomCGWH.{u, v} m m'
  let Y := rawHomCGWH.{u, v} n n'
  exact ConcreteCategory.ofHom
    ⟨fun z ↦ ULift.up (OrthogonalMatrixHom.blockSum
        (CartesianMonoidalCategory.fst X Y z).down
        (CartesianMonoidalCategory.snd X Y z).down),
      (Homeomorph.ulift
          (X := OrthogonalMatrixHom (m + n) (m' + n'))).symm.continuous.comp
        (OrthogonalMatrixHom.continuous_blockSum.comp
          (((Homeomorph.ulift
              (X := OrthogonalMatrixHom m m')).continuous.comp
                (ConcreteCategory.hom
                  (CartesianMonoidalCategory.fst X Y)).continuous).prodMk
            ((Homeomorph.ulift
              (X := OrthogonalMatrixHom n n')).continuous.comp
                (ConcreteCategory.hom
                  (CartesianMonoidalCategory.snd X Y)).continuous)))⟩

@[simp]
private theorem rawBlockSum_apply
    (m m' n n' : OrthogonalIndex)
    (z : (rawHomCGWH.{u, v} m m' ⊗
      rawHomCGWH.{u, v} n n' : CGWH.{u, v})) :
    rawBlockSum.{u, v} m m' n n' z =
      ULift.up (OrthogonalMatrixHom.blockSum
        (CartesianMonoidalCategory.fst
          (rawHomCGWH.{u, v} m m') (rawHomCGWH.{u, v} n n') z).down
        (CartesianMonoidalCategory.snd
          (rawHomCGWH.{u, v} m m') (rawHomCGWH.{u, v} n n') z).down) :=
  rfl

/-- Direct sum on native enriched hom objects. -/
noncomputable def tensorMap
    (m m' n n' : OrthogonalIndex) :
    (hom.{u, v} m m' ⊗ hom.{u, v} n n') ⟶
      hom.{u, v} (m + n) (m' + n') := by
  let matrixHom
      (m n : OrthogonalIndex) : CGWH.{u, v} := by
    letI : PseudoMetrizableSpace (Matrix (Fin n) (Fin m) ℝ) :=
      inferInstanceAs (PseudoMetrizableSpace (Fin n → Fin m → ℝ))
    letI : PseudoMetrizableSpace (OrthogonalMatrixHom m n) :=
      Topology.IsInducing.subtypeVal.pseudoMetrizableSpace
    letI : PseudoMetrizableSpace
        (ULift.{v, 0} (OrthogonalMatrixHom m n)) :=
      Homeomorph.ulift.isInducing.pseudoMetrizableSpace
    exact CGWH.of.{u, v} (ULift.{v, 0} (OrthogonalMatrixHom m n))
  let matrixBlockSum
      (m m' n n' : OrthogonalIndex) :
      (matrixHom m m' ⊗ matrixHom n n') ⟶
        matrixHom (m + n) (m' + n') := by
    let X := matrixHom m m'
    let Y := matrixHom n n'
    exact ConcreteCategory.ofHom
      ⟨fun z ↦ ULift.up (OrthogonalMatrixHom.blockSum
          (CartesianMonoidalCategory.fst X Y z).down
          (CartesianMonoidalCategory.snd X Y z).down),
        (Homeomorph.ulift
            (X := OrthogonalMatrixHom (m + n) (m' + n'))).symm.continuous.comp
          (OrthogonalMatrixHom.continuous_blockSum.comp
            (((Homeomorph.ulift
                (X := OrthogonalMatrixHom m m')).continuous.comp
                  (ConcreteCategory.hom
                    (CartesianMonoidalCategory.fst X Y)).continuous).prodMk
              ((Homeomorph.ulift
                (X := OrthogonalMatrixHom n n')).continuous.comp
                  (ConcreteCategory.hom
                    (CartesianMonoidalCategory.snd X Y)).continuous)))⟩
  let F := Under.costar CGWH.point.{u, v}
  let _ : BraidedCategory CGWH.{u, v} :=
    BraidedCategory.ofCartesianMonoidalCategory
  let _ : SymmetricCategory CGWH.{u, v} := inferInstance
  let core := CategoryTheory.Pointed.costarCoreMonoidal
    CGWH.point.{u, v} CGWH.point_isTerminal
  exact (core.μIso (matrixHom m m')
      (matrixHom n n')).hom ≫
    F.map (matrixBlockSum m m' n n')

/-- Direct sum sends two matrix generators to their ordered block sum and
absorbs either basepoint face. -/
theorem tensorMap_blockSum
    {m m' n n' : OrthogonalIndex}
    (A : OrthogonalMatrixHom m m')
    (B : OrthogonalMatrixHom n n') :
    let a : 𝟙_ PointedCGWH.{u, v} ⟶ hom.{u, v} m m' :=
      matrixPoint.{u, v} A
    let b : 𝟙_ PointedCGWH.{u, v} ⟶ hom.{u, v} n n' :=
      matrixPoint.{u, v} B
    let ab : 𝟙_ PointedCGWH.{u, v} ⟶ hom.{u, v} (m + n) (m' + n') :=
      matrixPoint.{u, v} (OrthogonalMatrixHom.blockSum A B)
    ((λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫ (a ⊗ₘ b) ≫
        tensorMap.{u, v} m m' n n' = ab) ∧
    ((λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫
        ((0 : 𝟙_ PointedCGWH.{u, v} ⟶ hom.{u, v} m m') ⊗ₘ b) ≫
        tensorMap.{u, v} m m' n n' = 0) ∧
    ((λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫
        (a ⊗ₘ (0 : 𝟙_ PointedCGWH.{u, v} ⟶ hom.{u, v} n n')) ≫
        tensorMap.{u, v} m m' n n' = 0) := by
  dsimp only
  let F := Under.costar CGWH.point.{u, v}
  let _ : BraidedCategory CGWH.{u, v} :=
    BraidedCategory.ofCartesianMonoidalCategory
  let _ : SymmetricCategory CGWH.{u, v} := inferInstance
  let _ : MonoidalCategory PointedCGWH.{u, v} :=
    CategoryTheory.Pointed.smashMonoidalCategory
      CGWH.point.{u, v} CGWH.point_isTerminal
  let core := CategoryTheory.Pointed.costarCoreMonoidal
    CGWH.point.{u, v} CGWH.point_isTerminal
  let _ : F.Monoidal := core.toMonoidal
  have pointTensor {X Y : CGWH.{u, v}}
      (x : 𝟙_ CGWH.{u, v} ⟶ X) (y : 𝟙_ CGWH.{u, v} ⟶ Y) :
      (λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫
            ((Functor.LaxMonoidal.ε F ≫ F.map x) ⊗ₘ
              (Functor.LaxMonoidal.ε F ≫ F.map y)) ≫
          Functor.LaxMonoidal.μ F X Y =
        Functor.LaxMonoidal.ε F ≫
          F.map ((λ_ (𝟙_ CGWH.{u, v})).inv ≫ (x ⊗ₘ y)) := by
    rw [← tensorHom_comp_tensorHom]
    simp only [Category.assoc]
    rw [Functor.LaxMonoidal.μ_natural]
    rw [MonoidalCategory.tensorHom_def']
    simp only [Category.assoc]
    rw [MonoidalCategory.id_whiskerLeft]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [Functor.LaxMonoidal.left_unitality_inv_assoc]
    rw [← Functor.map_comp]
  have matrixPoint_eq {a b : OrthogonalIndex}
      (M : OrthogonalMatrixHom a b) :
      matrixPoint.{u, v} M = Functor.LaxMonoidal.ε F ≫
        F.map (rawPointFromUnit.{u, v} M) := by
    exact freePoint_eq_coreUnit_map.{u, v}
      (rawHomCGWH.{u, v} a b) (ULift.up M)
  constructor
  · rw [matrixPoint_eq A,
      matrixPoint_eq B,
      matrixPoint_eq
        (OrthogonalMatrixHom.blockSum A B)]
    change (λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫
          ((Functor.LaxMonoidal.ε F ≫
              F.map (rawPointFromUnit.{u, v} A)) ⊗ₘ
            (Functor.LaxMonoidal.ε F ≫
              F.map (rawPointFromUnit.{u, v} B))) ≫
        Functor.LaxMonoidal.μ F (rawHomCGWH.{u, v} m m')
          (rawHomCGWH.{u, v} n n') ≫
        F.map (rawBlockSum.{u, v} m m' n n') =
      Functor.LaxMonoidal.ε F ≫
        F.map (rawPointFromUnit.{u, v}
          (OrthogonalMatrixHom.blockSum A B))
    slice_lhs 1 3 => rw [pointTensor
      (rawPointFromUnit.{u, v} A) (rawPointFromUnit.{u, v} B)]
    rw [Category.assoc, ← F.map_comp]
    change Functor.LaxMonoidal.ε F ≫
        F.map (((λ_ (𝟙_ CGWH.{u, v})).inv ≫
          (rawPointFromUnit.{u, v} A ⊗ₘ
            rawPointFromUnit.{u, v} B)) ≫
          rawBlockSum.{u, v} m m' n n') =
      Functor.LaxMonoidal.ε F ≫
        F.map (rawPointFromUnit.{u, v}
          (OrthogonalMatrixHom.blockSum A B))
    apply congrArg (fun k => Functor.LaxMonoidal.ε F ≫ k)
    apply congrArg (fun k => F.map k)
    let pUnit : CGWH.point.{u, v} ≅ 𝟙_ CGWH.{u, v} :=
      CGWH.point_isTerminal.uniqueUpToIso
        CartesianMonoidalCategory.isTerminalTensorUnit
    apply (cancel_epi pUnit.hom).1
    let qA : CGWH.point.{u, v} ⟶ rawHomCGWH.{u, v} m m' :=
      (CGWH.pointHomEquiv (rawHomCGWH.{u, v} m m')).symm (ULift.up A)
    let qB : CGWH.point.{u, v} ⟶ rawHomCGWH.{u, v} n n' :=
      (CGWH.pointHomEquiv (rawHomCGWH.{u, v} n n')).symm (ULift.up B)
    let qAB : CGWH.point.{u, v} ⟶
        rawHomCGWH.{u, v} (m + n) (m' + n') :=
      (CGWH.pointHomEquiv
        (rawHomCGWH.{u, v} (m + n) (m' + n'))).symm
          (ULift.up (OrthogonalMatrixHom.blockSum A B))
    have hpA : pUnit.hom ≫ rawPointFromUnit.{u, v} A = qA := by
      change pUnit.hom ≫ (pUnit.inv ≫ qA) = qA
      rw [← Category.assoc, pUnit.hom_inv_id, Category.id_comp]
    have hpB : pUnit.hom ≫ rawPointFromUnit.{u, v} B = qB := by
      change pUnit.hom ≫ (pUnit.inv ≫ qB) = qB
      rw [← Category.assoc, pUnit.hom_inv_id, Category.id_comp]
    have hpAB : pUnit.hom ≫
        rawPointFromUnit.{u, v} (OrthogonalMatrixHom.blockSum A B) =
      qAB := by
      change pUnit.hom ≫ (pUnit.inv ≫ qAB) = qAB
      rw [← Category.assoc, pUnit.hom_inv_id, Category.id_comp]
    have hPair : pUnit.hom ≫ (λ_ (𝟙_ CGWH.{u, v})).inv ≫
        (rawPointFromUnit.{u, v} A ⊗ₘ rawPointFromUnit.{u, v} B) =
      CartesianMonoidalCategory.lift qA qB := by
      apply CartesianMonoidalCategory.hom_ext
      · simp only [Category.assoc,
          CartesianMonoidalCategory.tensorHom_fst,
          CartesianMonoidalCategory.lift_fst]
        have ht : pUnit.hom ≫ (λ_ (𝟙_ CGWH.{u, v})).inv ≫
            CartesianMonoidalCategory.fst (𝟙_ CGWH.{u, v})
              (𝟙_ CGWH.{u, v}) = pUnit.hom :=
          CartesianMonoidalCategory.isTerminalTensorUnit.hom_ext _ _
        calc
          _ = (pUnit.hom ≫ (λ_ (𝟙_ CGWH.{u, v})).inv ≫
                CartesianMonoidalCategory.fst (𝟙_ CGWH.{u, v})
                  (𝟙_ CGWH.{u, v})) ≫
              rawPointFromUnit.{u, v} A := by simp only [Category.assoc]
          _ = pUnit.hom ≫ rawPointFromUnit.{u, v} A := by rw [ht]
          _ = qA := hpA
      · simp only [Category.assoc,
          CartesianMonoidalCategory.tensorHom_snd,
          CartesianMonoidalCategory.lift_snd]
        have ht : pUnit.hom ≫ (λ_ (𝟙_ CGWH.{u, v})).inv ≫
            CartesianMonoidalCategory.snd (𝟙_ CGWH.{u, v})
              (𝟙_ CGWH.{u, v}) = pUnit.hom :=
          CartesianMonoidalCategory.isTerminalTensorUnit.hom_ext _ _
        calc
          _ = (pUnit.hom ≫ (λ_ (𝟙_ CGWH.{u, v})).inv ≫
                CartesianMonoidalCategory.snd (𝟙_ CGWH.{u, v})
                  (𝟙_ CGWH.{u, v})) ≫
              rawPointFromUnit.{u, v} B := by simp only [Category.assoc]
          _ = pUnit.hom ≫ rawPointFromUnit.{u, v} B := by rw [ht]
          _ = qB := hpB
    change pUnit.hom ≫
        (((λ_ (𝟙_ CGWH.{u, v})).inv ≫
          (rawPointFromUnit.{u, v} A ⊗ₘ
            rawPointFromUnit.{u, v} B)) ≫
          rawBlockSum.{u, v} m m' n n') =
      pUnit.hom ≫
        rawPointFromUnit.{u, v} (OrthogonalMatrixHom.blockSum A B)
    calc
      _ = (pUnit.hom ≫ (λ_ (𝟙_ CGWH.{u, v})).inv ≫
          (rawPointFromUnit.{u, v} A ⊗ₘ
            rawPointFromUnit.{u, v} B)) ≫
          rawBlockSum.{u, v} m m' n n' := by simp only [Category.assoc]
      _ = CartesianMonoidalCategory.lift qA qB ≫
          rawBlockSum.{u, v} m m' n n' := by rw [hPair]
      _ = qAB := by
        apply ConcreteCategory.hom_ext
        intro x
        rw [ConcreteCategory.comp_apply, rawBlockSum_apply]
        have hfst := ConcreteCategory.congr_hom
          (CartesianMonoidalCategory.lift_fst qA qB) x
        have hsnd := ConcreteCategory.congr_hom
          (CartesianMonoidalCategory.lift_snd qA qB) x
        rw [ConcreteCategory.comp_apply] at hfst hsnd
        have hfst' :
            (ConcreteCategory.hom
              (CartesianMonoidalCategory.fst
                (rawHomCGWH.{u, v} m m') (rawHomCGWH.{u, v} n n'))
              (ConcreteCategory.hom
                (CartesianMonoidalCategory.lift qA qB) x)).down = A := by
          rw [hfst]
          cases x
          rfl
        have hsnd' :
            (ConcreteCategory.hom
              (CartesianMonoidalCategory.snd
                (rawHomCGWH.{u, v} m m') (rawHomCGWH.{u, v} n n'))
              (ConcreteCategory.hom
                (CartesianMonoidalCategory.lift qA qB) x)).down = B := by
          rw [hsnd]
          cases x
          rfl
        rw [hfst', hsnd']
        cases x
        rfl
      _ = _ := hpAB.symm
  constructor
  · have hz :
        ((0 : 𝟙_ PointedCGWH.{u, v} ⟶ hom.{u, v} m m') ⊗ₘ
          matrixPoint.{u, v} B) = 0 := by
      let _ : (tensorRight (𝟙_ PointedCGWH.{u, v})).PreservesZeroMorphisms :=
        inferInstance
      rw [MonoidalCategory.tensorHom_def]
      change (tensorRight (𝟙_ PointedCGWH.{u, v})).map 0 ≫ _ = 0
      rw [Functor.map_zero, zero_comp]
    rw [hz, zero_comp, comp_zero]
  · have hz :
        (matrixPoint.{u, v} A ⊗ₘ
          (0 : 𝟙_ PointedCGWH.{u, v} ⟶ hom.{u, v} n n')) = 0 := by
      let _ : (tensorLeft (𝟙_ PointedCGWH.{u, v})).PreservesZeroMorphisms :=
        inferInstance
      rw [MonoidalCategory.tensorHom_def']
      change (tensorLeft (𝟙_ PointedCGWH.{u, v})).map 0 ≫ _ = 0
      rw [Functor.map_zero, zero_comp]
    rw [hz, zero_comp, comp_zero]

/-- The orthogonal matrix morphism induced by a coordinate equivalence. -/
private noncomputable def coordinateIsometry
    {m n : OrthogonalIndex} (e : Fin m ≃ Fin n) :
    OrthogonalMatrixHom m n := by
  let M : Matrix (Fin n) (Fin m) ℝ :=
    Matrix.reindex e (Equiv.refl (Fin m)) 1
  refine ⟨M, ?_, ?_⟩
  · dsimp only [M]
    rw [Matrix.transpose_reindex]
    change (Matrix.reindexLinearEquiv ℝ ℝ (Equiv.refl (Fin m)) e)
          (1 : Matrix (Fin m) (Fin m) ℝ).transpose *
        (Matrix.reindexLinearEquiv ℝ ℝ e (Equiv.refl (Fin m)))
          (1 : Matrix (Fin m) (Fin m) ℝ) = 1
    rw [Matrix.reindexLinearEquiv_mul]
    simp
  · dsimp only [M]
    rw [Matrix.transpose_reindex]
    change (Matrix.reindexLinearEquiv ℝ ℝ e (Equiv.refl (Fin m)))
          (1 : Matrix (Fin m) (Fin m) ℝ) *
        (Matrix.reindexLinearEquiv ℝ ℝ (Equiv.refl (Fin m)) e)
          (1 : Matrix (Fin m) (Fin m) ℝ).transpose = 1
    rw [Matrix.reindexLinearEquiv_mul]
    simp

/-- The coordinate equivalence obtained by summing two finite coordinate equivalences. -/
private def finAddEquiv
    {a b c d : OrthogonalIndex}
    (e : Fin a ≃ Fin b) (f : Fin c ≃ Fin d) :
    Fin (a + c) ≃ Fin (b + d) :=
  (finSumFinEquiv : Fin a ⊕ Fin c ≃ Fin (a + c)).symm.trans
    ((Equiv.sumCongr e f).trans
      (finSumFinEquiv : Fin b ⊕ Fin d ≃ Fin (b + d)))

private theorem coordinateLaws :
    (∀ {a b c d : OrthogonalIndex}
      (e : Fin b ≃ Fin d) (f : Fin a ≃ Fin c)
      (A : OrthogonalMatrixHom a b) (B : OrthogonalMatrixHom c d),
      Matrix.reindex e f A.1 = B.1 →
        OrthogonalMatrixHom.comp A (coordinateIsometry e) =
          OrthogonalMatrixHom.comp (coordinateIsometry f) B) ∧
    (∀ {a b c d : OrthogonalIndex}
      (e : Fin a ≃ Fin b) (f : Fin c ≃ Fin d),
      OrthogonalMatrixHom.blockSum (coordinateIsometry e)
          (coordinateIsometry f) = coordinateIsometry (finAddEquiv e f)) ∧
    (∀ {a b c : OrthogonalIndex}
      (e : Fin a ≃ Fin b) (f : Fin b ≃ Fin c),
      OrthogonalMatrixHom.comp (coordinateIsometry e)
          (coordinateIsometry f) = coordinateIsometry (e.trans f)) ∧
    (∀ a : OrthogonalIndex,
      coordinateIsometry (Equiv.refl (Fin a)) = OrthogonalMatrixHom.id a) := by
  constructor
  · intro a b c d e f A B h
    apply OrthogonalMatrixHom.ext
    dsimp only [OrthogonalMatrixHom.comp, coordinateIsometry]
    rw [← h]
    change
      (Matrix.reindexLinearEquiv ℝ ℝ e (Equiv.refl (Fin b))) 1 *
          (Matrix.reindexLinearEquiv ℝ ℝ (Equiv.refl (Fin b))
            (Equiv.refl (Fin a))) A.1 =
        (Matrix.reindexLinearEquiv ℝ ℝ e f) A.1 *
          (Matrix.reindexLinearEquiv ℝ ℝ f (Equiv.refl (Fin a))) 1
    rw [Matrix.reindexLinearEquiv_mul,
      Matrix.reindexLinearEquiv_mul]
    simp
  constructor
  · intro a b c d e f
    apply OrthogonalMatrixHom.ext
    ext i j
    simp only [OrthogonalMatrixHom.blockSum, coordinateIsometry,
      Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.one_apply]
    rcases hi : (finSumFinEquiv : Fin b ⊕ Fin d ≃ Fin (b + d)).symm i
        with ib | id <;>
      rcases hj : (finSumFinEquiv : Fin a ⊕ Fin c ≃ Fin (a + c)).symm j
        with ja | jc
    · have hi' := congrArg
        (finSumFinEquiv : Fin b ⊕ Fin d ≃ Fin (b + d)) hi
      have hj' := congrArg
        (finSumFinEquiv : Fin a ⊕ Fin c ≃ Fin (a + c)) hj
      rw [Equiv.apply_symm_apply] at hi' hj'
      subst i
      subst j
      simp [finAddEquiv, Matrix.one_apply, Equiv.symm_apply_eq]
    · have hi' := congrArg
        (finSumFinEquiv : Fin b ⊕ Fin d ≃ Fin (b + d)) hi
      have hj' := congrArg
        (finSumFinEquiv : Fin a ⊕ Fin c ≃ Fin (a + c)) hj
      rw [Equiv.apply_symm_apply] at hi' hj'
      subst i
      subst j
      have hne : Fin.castAdd c (e.symm ib) ≠ Fin.natAdd a jc := by
        intro h
        have hval := congrArg Fin.val h
        simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
        omega
      simp [finAddEquiv, hne]
    · have hi' := congrArg
        (finSumFinEquiv : Fin b ⊕ Fin d ≃ Fin (b + d)) hi
      have hj' := congrArg
        (finSumFinEquiv : Fin a ⊕ Fin c ≃ Fin (a + c)) hj
      rw [Equiv.apply_symm_apply] at hi' hj'
      subst i
      subst j
      have hne : Fin.natAdd a (f.symm id) ≠ Fin.castAdd c ja := by
        intro h
        have hval := congrArg Fin.val h
        simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
        omega
      simp [finAddEquiv, hne]
    · have hi' := congrArg
        (finSumFinEquiv : Fin b ⊕ Fin d ≃ Fin (b + d)) hi
      have hj' := congrArg
        (finSumFinEquiv : Fin a ⊕ Fin c ≃ Fin (a + c)) hj
      rw [Equiv.apply_symm_apply] at hi' hj'
      subst i
      subst j
      simp [finAddEquiv, Matrix.one_apply, Equiv.symm_apply_eq]
  constructor
  · intro a b c e f
    apply OrthogonalMatrixHom.ext
    ext i j
    suffices hEq : (if f.symm i = e j then (1 : ℝ) else 0) =
        if e.symm (f.symm i) = j then 1 else 0 by
      simpa [coordinateIsometry, OrthogonalMatrixHom.comp,
        Matrix.reindex_apply, Matrix.one_apply, Function.comp_def] using hEq
    by_cases h : f.symm i = e j
    · simp [h]
    · have h' : e.symm (f.symm i) ≠ j := by
        intro h'
        apply h
        simpa using congrArg e h'
      simp [h, h']
  · intro a
    apply OrthogonalMatrixHom.ext
    ext i j
    simp [coordinateIsometry, OrthogonalMatrixHom.id,
      Matrix.reindex_apply, Matrix.one_apply]

/-- The raw coordinate block swap. -/
noncomputable def blockSwap (m n : OrthogonalIndex) :
    OrthogonalMatrixHom (m + n) (n + m) := by
  let isometryMatrix
      {m n : OrthogonalIndex} (e : Fin m ≃ Fin n) :
      OrthogonalMatrixHom m n := by
    let M : Matrix (Fin n) (Fin m) ℝ :=
      Matrix.reindex e (Equiv.refl (Fin m)) 1
    refine ⟨M, ?_, ?_⟩
    · dsimp only [M]
      rw [Matrix.transpose_reindex]
      change (Matrix.reindexLinearEquiv ℝ ℝ (Equiv.refl (Fin m)) e)
            (1 : Matrix (Fin m) (Fin m) ℝ).transpose *
          (Matrix.reindexLinearEquiv ℝ ℝ e (Equiv.refl (Fin m)))
            (1 : Matrix (Fin m) (Fin m) ℝ) = 1
      rw [Matrix.reindexLinearEquiv_mul]
      simp
    · dsimp only [M]
      rw [Matrix.transpose_reindex]
      change (Matrix.reindexLinearEquiv ℝ ℝ e (Equiv.refl (Fin m)))
            (1 : Matrix (Fin m) (Fin m) ℝ) *
          (Matrix.reindexLinearEquiv ℝ ℝ (Equiv.refl (Fin m)) e)
            (1 : Matrix (Fin m) (Fin m) ℝ).transpose = 1
      rw [Matrix.reindexLinearEquiv_mul]
      simp
  exact isometryMatrix (finAddFlip : Fin (m + n) ≃ Fin (n + m))

/-- Matrix entries of the raw block swap. -/
theorem blockSwap_matrix (m n : OrthogonalIndex)
    (i : Fin (n + m)) (j : Fin (m + n)) :
    (blockSwap m n).1 i j = if i = finAddFlip j then 1 else 0 := by
  simp [blockSwap, Matrix.reindex_apply,
    Matrix.one_apply, Equiv.symm_apply_eq]

/-- The ordinary category selected from the native enrichment. -/
@[instance_reducible]
noncomputable def category : Category.{v} OrthogonalIndex := by
  let _ : EnrichedCategory PointedCGWH.{u, v} OrthogonalIndex :=
    enrichedCategory.{u, v}
  exact inferInstanceAs
    (Category (ForgetEnrichment PointedCGWH.{u, v} OrthogonalIndex))

/-- The selected ordinary/enriched compatibility, definitionally using the
native enrichment. -/
@[instance_reducible]
noncomputable def enrichedOrdinaryCategory :
    @EnrichedOrdinaryCategory PointedCGWH.{u, v} _ _ OrthogonalIndex
      (category.{u, v}) := by
  let _ : EnrichedCategory PointedCGWH.{u, v} OrthogonalIndex :=
    enrichedCategory.{u, v}
  let _ : Category.{v} OrthogonalIndex := category.{u, v}
  exact
    { toEnrichedCategory := enrichedCategory.{u, v}
      homEquiv := Equiv.refl _
      homEquiv_id := fun _ ↦ rfl
      homEquiv_comp := fun _ _ ↦ rfl }

/-- The ordinary orthogonal-index morphism represented by an orthogonal matrix. -/
private noncomputable def ordinaryPoint
    {m n : OrthogonalIndex} (A : OrthogonalMatrixHom m n) :
    letI : Category.{v} OrthogonalIndex := category.{u, v}
    m ⟶ n := by
  change 𝟙_ PointedCGWH.{u, v} ⟶ hom.{u, v} m n
  exact matrixPoint.{u, v} A

private theorem ordinaryPoint_comp
    {m n p : OrthogonalIndex}
    (A : OrthogonalMatrixHom m n) (B : OrthogonalMatrixHom n p) :
    letI : Category.{v} OrthogonalIndex := category.{u, v}
    ordinaryPoint.{u, v} A ≫ ordinaryPoint.{u, v} B =
      ordinaryPoint.{u, v} (OrthogonalMatrixHom.comp A B) := by
  unfold ordinaryPoint
  change (λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫
      (matrixPoint.{u, v} A ⊗ₘ matrixPoint.{u, v} B) ≫
        @eComp PointedCGWH.{u, v} _ _ OrthogonalIndex
          (enrichedCategory.{u, v}) m n p = _
  exact (enrichedCategory_comp.{u, v} A B).1

/-- The coordinate isometry reassociating three sums of orthogonal indices. -/
private noncomputable def associatorHom
    (a b c : OrthogonalIndex) :
    OrthogonalMatrixHom ((a + b) + c) (a + (b + c)) :=
  coordinateIsometry (finCongr (Nat.add_assoc a b c))

/-- The coordinate isometry removing a zero summand on the left. -/
private noncomputable def leftUnitorHom (a : OrthogonalIndex) :
    OrthogonalMatrixHom (0 + a) a :=
  coordinateIsometry (finCongr (Nat.zero_add a))

/-- The coordinate isometry removing a zero summand on the right. -/
private noncomputable def rightUnitorHom (a : OrthogonalIndex) :
    OrthogonalMatrixHom (a + 0) a :=
  coordinateIsometry (finCongr (Nat.add_zero a))

private theorem coordinatePoint_hom_inv_id
    {a b : OrthogonalIndex} (e : Fin a ≃ Fin b) :
    letI : Category.{v} OrthogonalIndex := category.{u, v}
    ordinaryPoint.{u, v} (coordinateIsometry e) ≫
      ordinaryPoint.{u, v} (coordinateIsometry e.symm) = 𝟙 a := by
  let _ : Category.{v} OrthogonalIndex := category.{u, v}
  have hComp :
      OrthogonalMatrixHom.comp (coordinateIsometry e)
        (coordinateIsometry e.symm) =
      coordinateIsometry (Equiv.refl (Fin a)) := by
    rw [coordinateLaws.2.2.1]
    congr 1
    exact e.self_trans_symm
  have hRaw :
      OrthogonalMatrixHom.comp (coordinateIsometry e)
        (coordinateIsometry e.symm) = OrthogonalMatrixHom.id a :=
    hComp.trans (coordinateLaws.2.2.2 a)
  calc
    ordinaryPoint.{u, v} (coordinateIsometry e) ≫
        ordinaryPoint.{u, v} (coordinateIsometry e.symm) =
      ordinaryPoint.{u, v} (OrthogonalMatrixHom.comp
        (coordinateIsometry e) (coordinateIsometry e.symm)) :=
      ordinaryPoint_comp.{u, v} _ _
    _ = ordinaryPoint.{u, v} (OrthogonalMatrixHom.id a) :=
      congrArg ordinaryPoint.{u, v} hRaw
    _ = 𝟙 a := by
      unfold ordinaryPoint
      change matrixPoint.{u, v} (OrthogonalMatrixHom.id a) =
        @eId PointedCGWH.{u, v} _ _ OrthogonalIndex (enrichedCategory.{u, v}) a
      exact (enrichedCategory_id.{u, v} a).symm

private theorem coordinatePoint_inv_hom_id
    {a b : OrthogonalIndex} (e : Fin a ≃ Fin b) :
    letI : Category.{v} OrthogonalIndex := category.{u, v}
    ordinaryPoint.{u, v} (coordinateIsometry e.symm) ≫
      ordinaryPoint.{u, v} (coordinateIsometry e) = 𝟙 b := by
  let _ : Category.{v} OrthogonalIndex := category.{u, v}
  have hComp :
      OrthogonalMatrixHom.comp (coordinateIsometry e.symm)
        (coordinateIsometry e) =
      coordinateIsometry (Equiv.refl (Fin b)) := by
    rw [coordinateLaws.2.2.1]
    congr 1
    exact e.symm_trans_self
  have hRaw :
      OrthogonalMatrixHom.comp (coordinateIsometry e.symm)
        (coordinateIsometry e) = OrthogonalMatrixHom.id b :=
    hComp.trans (coordinateLaws.2.2.2 b)
  calc
    ordinaryPoint.{u, v} (coordinateIsometry e.symm) ≫
        ordinaryPoint.{u, v} (coordinateIsometry e) =
      ordinaryPoint.{u, v} (OrthogonalMatrixHom.comp
        (coordinateIsometry e.symm) (coordinateIsometry e)) :=
      ordinaryPoint_comp.{u, v} _ _
    _ = ordinaryPoint.{u, v} (OrthogonalMatrixHom.id b) :=
      congrArg ordinaryPoint.{u, v} hRaw
    _ = 𝟙 b := by
      unfold ordinaryPoint
      change matrixPoint.{u, v} (OrthogonalMatrixHom.id b) =
        @eId PointedCGWH.{u, v} _ _ OrthogonalIndex (enrichedCategory.{u, v}) b
      exact (enrichedCategory_id.{u, v} b).symm

/-- The selected zero-morphism dictionary for the native ordinary category.
This value uses the same zero arrows and laws as the selected monoidal data. -/
@[instance_reducible]
noncomputable def zeroMorphisms :
    letI : Category.{v} OrthogonalIndex := category.{u, v}
    HasZeroMorphisms OrthogonalIndex := by
  let _ : Category.{v} OrthogonalIndex := category.{u, v}
  let pointOf {m n : OrthogonalIndex} (f : m ⟶ n) :
      𝟙_ PointedCGWH.{u, v} ⟶ hom.{u, v} m n := by
    change 𝟙_ PointedCGWH.{u, v} ⟶ hom.{u, v} m n at f
    exact f
  let homOf {m n : OrthogonalIndex}
      (f : 𝟙_ PointedCGWH.{u, v} ⟶ hom.{u, v} m n) : m ⟶ n := by
    change 𝟙_ PointedCGWH.{u, v} ⟶ hom.{u, v} m n
    exact f
  let zeroMorphisms : HasZeroMorphisms OrthogonalIndex :=
    { zero := fun m n ↦
        ⟨homOf (0 : 𝟙_ PointedCGWH.{u, v} ⟶ hom.{u, v} m n)⟩
      comp_zero := by
        intro X Y f Z
        change (λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫
            (pointOf f ⊗ₘ
              (0 : 𝟙_ PointedCGWH.{u, v} ⟶ hom.{u, v} Y Z)) ≫
              @eComp PointedCGWH.{u, v} _ _ OrthogonalIndex
                (enrichedCategory.{u, v}) X Y Z = 0
        have hz :
            (pointOf f ⊗ₘ (0 : 𝟙_ PointedCGWH.{u, v} ⟶
              hom.{u, v} Y Z)) = 0 := by
          let _ : (tensorLeft (𝟙_ PointedCGWH.{u, v})).PreservesZeroMorphisms :=
            inferInstance
          rw [MonoidalCategory.tensorHom_def']
          change (tensorLeft (𝟙_ PointedCGWH.{u, v})).map 0 ≫ _ = 0
          rw [Functor.map_zero, zero_comp]
        have hTensorZero :
            (λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫
            (pointOf f ⊗ₘ (0 : 𝟙_ PointedCGWH.{u, v} ⟶ hom.{u, v} Y Z)) ≫
                @eComp PointedCGWH.{u, v} _ _ OrthogonalIndex (enrichedCategory.{u, v}) X Y Z =
              (λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫
                (0 : (𝟙_ PointedCGWH.{u, v} ⊗ 𝟙_ PointedCGWH.{u, v}) ⟶
                  hom.{u, v} X Y ⊗ hom.{u, v} Y Z) ≫
                @eComp PointedCGWH.{u, v} _ _ OrthogonalIndex (enrichedCategory.{u, v}) X Y Z :=
          congrArg (fun q => (λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫ q ≫
            @eComp PointedCGWH.{u, v} _ _ OrthogonalIndex (enrichedCategory.{u, v}) X Y Z) hz
        have hCompZero :
            (0 : (𝟙_ PointedCGWH.{u, v} ⊗ 𝟙_ PointedCGWH.{u, v}) ⟶
              hom.{u, v} X Y ⊗ hom.{u, v} Y Z) ≫
                @eComp PointedCGWH.{u, v} _ _ OrthogonalIndex (enrichedCategory.{u, v}) X Y Z =
              (0 : (𝟙_ PointedCGWH.{u, v} ⊗ 𝟙_ PointedCGWH.{u, v}) ⟶ hom.{u, v} X Z) :=
          zero_comp (f := @eComp PointedCGWH.{u, v} _ _ OrthogonalIndex
            (enrichedCategory.{u, v}) X Y Z)
        exact hTensorZero.trans
          ((congrArg (fun q => (λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫ q) hCompZero).trans
            (comp_zero (f := (λ_ (𝟙_ PointedCGWH.{u, v})).inv)))
      zero_comp := by
        intro X Y Z f
        change (λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫
            ((0 : 𝟙_ PointedCGWH.{u, v} ⟶ hom.{u, v} X Y) ⊗ₘ
              pointOf f) ≫
              @eComp PointedCGWH.{u, v} _ _ OrthogonalIndex
                (enrichedCategory.{u, v}) X Y Z = 0
        have hz :
            ((0 : 𝟙_ PointedCGWH.{u, v} ⟶ hom.{u, v} X Y) ⊗ₘ
              pointOf f) = 0 := by
          let _ : (tensorRight (𝟙_ PointedCGWH.{u, v})).PreservesZeroMorphisms :=
            inferInstance
          rw [MonoidalCategory.tensorHom_def]
          change (tensorRight (𝟙_ PointedCGWH.{u, v})).map 0 ≫ _ = 0
          rw [Functor.map_zero, zero_comp]
        have hTensorZero :
            (λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫
            ((0 : 𝟙_ PointedCGWH.{u, v} ⟶ hom.{u, v} X Y) ⊗ₘ pointOf f) ≫
                @eComp PointedCGWH.{u, v} _ _ OrthogonalIndex (enrichedCategory.{u, v}) X Y Z =
              (λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫
                (0 : (𝟙_ PointedCGWH.{u, v} ⊗ 𝟙_ PointedCGWH.{u, v}) ⟶
                  hom.{u, v} X Y ⊗ hom.{u, v} Y Z) ≫
                @eComp PointedCGWH.{u, v} _ _ OrthogonalIndex (enrichedCategory.{u, v}) X Y Z :=
          congrArg (fun q => (λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫ q ≫
            @eComp PointedCGWH.{u, v} _ _ OrthogonalIndex (enrichedCategory.{u, v}) X Y Z) hz
        have hCompZero :
            (0 : (𝟙_ PointedCGWH.{u, v} ⊗ 𝟙_ PointedCGWH.{u, v}) ⟶
              hom.{u, v} X Y ⊗ hom.{u, v} Y Z) ≫
                @eComp PointedCGWH.{u, v} _ _ OrthogonalIndex (enrichedCategory.{u, v}) X Y Z =
              (0 : (𝟙_ PointedCGWH.{u, v} ⊗ 𝟙_ PointedCGWH.{u, v}) ⟶ hom.{u, v} X Z) :=
          zero_comp (f := @eComp PointedCGWH.{u, v} _ _ OrthogonalIndex
            (enrichedCategory.{u, v}) X Y Z)
        exact hTensorZero.trans
          ((congrArg (fun q => (λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫ q) hCompZero).trans
            (comp_zero (f := (λ_ (𝟙_ PointedCGWH.{u, v})).inv))) }
  exact zeroMorphisms

/-- Zero morphisms in the pointed ordinary orthogonal-index category. -/
@[instance_reducible]
private noncomputable def ordinaryZeroMorphisms :
    letI : Category.{v} OrthogonalIndex := category.{u, v}
    HasZeroMorphisms OrthogonalIndex :=
  zeroMorphisms.{u, v}

/-- The selected direct-sum monoidal structure on the native orthogonal
index. -/
@[instance_reducible]
noncomputable def monoidalCategory :
    @MonoidalCategory OrthogonalIndex (category.{u, v}) := by
  let _ : Category.{v} OrthogonalIndex := category.{u, v}
  let isometryMatrix
      {m n : OrthogonalIndex} (e : Fin m ≃ Fin n) :
      OrthogonalMatrixHom m n := by
    let M : Matrix (Fin n) (Fin m) ℝ :=
      Matrix.reindex e (Equiv.refl (Fin m)) 1
    refine ⟨M, ?_, ?_⟩
    · dsimp only [M]
      rw [Matrix.transpose_reindex]
      change (Matrix.reindexLinearEquiv ℝ ℝ (Equiv.refl (Fin m)) e)
            (1 : Matrix (Fin m) (Fin m) ℝ).transpose *
          (Matrix.reindexLinearEquiv ℝ ℝ e (Equiv.refl (Fin m)))
            (1 : Matrix (Fin m) (Fin m) ℝ) = 1
      rw [Matrix.reindexLinearEquiv_mul]
      simp
    · dsimp only [M]
      rw [Matrix.transpose_reindex]
      change (Matrix.reindexLinearEquiv ℝ ℝ e (Equiv.refl (Fin m)))
            (1 : Matrix (Fin m) (Fin m) ℝ) *
          (Matrix.reindexLinearEquiv ℝ ℝ (Equiv.refl (Fin m)) e)
            (1 : Matrix (Fin m) (Fin m) ℝ).transpose = 1
      rw [Matrix.reindexLinearEquiv_mul]
      simp
  let sumCoordinates
      {a b c d : OrthogonalIndex}
      (e : Fin a ≃ Fin b) (f : Fin c ≃ Fin d) :
      Fin (a + c) ≃ Fin (b + d) :=
    (finSumFinEquiv : Fin a ⊕ Fin c ≃ Fin (a + c)).symm.trans
      ((Equiv.sumCongr e f).trans
        (finSumFinEquiv : Fin b ⊕ Fin d ≃ Fin (b + d)))
  let matrixArrow
      {m n : OrthogonalIndex} (A : OrthogonalMatrixHom m n) :
      letI : Category.{v} OrthogonalIndex := category.{u, v}
      m ⟶ n := by
    change 𝟙_ PointedCGWH.{u, v} ⟶ hom.{u, v} m n
    exact matrixPoint.{u, v} A
  have matrixArrow_comp {m n p : OrthogonalIndex}
      (A : OrthogonalMatrixHom m n) (B : OrthogonalMatrixHom n p) :
      matrixArrow A ≫ matrixArrow B =
        matrixArrow (OrthogonalMatrixHom.comp A B) := by
    unfold matrixArrow
    change (λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫
        (matrixPoint.{u, v} A ⊗ₘ matrixPoint.{u, v} B) ≫
          @eComp PointedCGWH.{u, v} _ _ OrthogonalIndex
            (enrichedCategory.{u, v}) m n p = _
    exact (enrichedCategory_comp.{u, v} A B).1
  let associatorMatrix
      (a b c : OrthogonalIndex) :
      OrthogonalMatrixHom ((a + b) + c) (a + (b + c)) :=
    isometryMatrix (finCongr (Nat.add_assoc a b c))
  let leftUnitorMatrix (a : OrthogonalIndex) :
      OrthogonalMatrixHom (0 + a) a :=
    isometryMatrix (finCongr (Nat.zero_add a))
  let rightUnitorMatrix (a : OrthogonalIndex) :
      OrthogonalMatrixHom (a + 0) a :=
    isometryMatrix (finCongr (Nat.add_zero a))
  let pointOf {m n : OrthogonalIndex} (f : m ⟶ n) :
      𝟙_ PointedCGWH.{u, v} ⟶ hom.{u, v} m n := by
    change 𝟙_ PointedCGWH.{u, v} ⟶ hom.{u, v} m n at f
    exact f
  let homOf {m n : OrthogonalIndex}
      (f : 𝟙_ PointedCGWH.{u, v} ⟶ hom.{u, v} m n) : m ⟶ n := by
    change 𝟙_ PointedCGWH.{u, v} ⟶ hom.{u, v} m n
    exact f
  let zeroMorphisms : HasZeroMorphisms OrthogonalIndex := zeroMorphisms
  let _ : HasZeroMorphisms OrthogonalIndex := zeroMorphisms
  have category_id (n : OrthogonalIndex) :
      (𝟙 n) = matrixArrow (OrthogonalMatrixHom.id n) := by
    unfold matrixArrow
    change @eId PointedCGWH.{u, v} _ _ OrthogonalIndex
      (enrichedCategory.{u, v}) n = _
    exact enrichedCategory_id.{u, v} n
  have isometryMatrix_naturality
      {a b c d : OrthogonalIndex}
      (e : Fin b ≃ Fin d) (f : Fin a ≃ Fin c)
      (A : OrthogonalMatrixHom a b) (B : OrthogonalMatrixHom c d)
      (h : Matrix.reindex e f A.1 = B.1) :
      OrthogonalMatrixHom.comp A (isometryMatrix e) =
        OrthogonalMatrixHom.comp (isometryMatrix f) B :=
    (by exact coordinateLaws.1 e f A B h)
  have isometryMatrix_blockSum
      {a b c d : OrthogonalIndex}
      (e : Fin a ≃ Fin b) (f : Fin c ≃ Fin d) :
      OrthogonalMatrixHom.blockSum (isometryMatrix e)
          (isometryMatrix f) = isometryMatrix (sumCoordinates e f) :=
    (by exact coordinateLaws.2.1 e f)
  have isometryMatrix_comp
      {a b c : OrthogonalIndex}
      (e : Fin a ≃ Fin b) (f : Fin b ≃ Fin c) :
      OrthogonalMatrixHom.comp (isometryMatrix e)
          (isometryMatrix f) = isometryMatrix (e.trans f) :=
    (by exact coordinateLaws.2.2.1 e f)
  have isometryMatrix_refl (a : OrthogonalIndex) :
      isometryMatrix (Equiv.refl (Fin a)) = OrthogonalMatrixHom.id a :=
    (by exact coordinateLaws.2.2.2 a)
  have homCases {m n : OrthogonalIndex} (f : m ⟶ n) :
      f = 0 ∨ ∃ A : OrthogonalMatrixHom m n,
        f = matrixArrow A := by
    exact (by
      change f = 0 ∨ ∃ A : OrthogonalMatrixHom m n,
        f = matrixPoint.{u, v} A
      rcases freePoint_cases.{u, v} (rawHomCGWH.{u, v} m n) f with
        h | ⟨z, h⟩
      · exact Or.inl h
      · change ULift.{v, 0} (OrthogonalMatrixHom m n) at z
        rcases z with ⟨A⟩
        exact Or.inr ⟨A, h⟩
    )
  let pointTensor {m m' n n' : OrthogonalIndex}
      (f : 𝟙_ PointedCGWH.{u, v} ⟶ hom.{u, v} m m')
      (g : 𝟙_ PointedCGWH.{u, v} ⟶ hom.{u, v} n n') :
      𝟙_ PointedCGWH.{u, v} ⟶ hom.{u, v} (m + n) (m' + n') :=
    (λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫ (f ⊗ₘ g) ≫
      tensorMap.{u, v} m m' n n'
  let tensorO {m m' n n' : OrthogonalIndex}
      (f : m ⟶ m') (g : n ⟶ n') : (m + n) ⟶ (m' + n') :=
    homOf (pointTensor (pointOf f) (pointOf g))
  have tensorO_matrix {m m' n n' : OrthogonalIndex}
      (A : OrthogonalMatrixHom m m') (B : OrthogonalMatrixHom n n') :
      tensorO (matrixArrow A) (matrixArrow B) =
        matrixArrow (OrthogonalMatrixHom.blockSum A B) := by
    change pointTensor (matrixPoint.{u, v} A)
      (matrixPoint.{u, v} B) =
        matrixPoint.{u, v} (OrthogonalMatrixHom.blockSum A B)
    exact (tensorMap_blockSum.{u, v} A B).1
  have tensorO_zero_left {m m' n n' : OrthogonalIndex}
      (g : n ⟶ n') : tensorO (0 : m ⟶ m') g = 0 := by
    change pointTensor
      (0 : 𝟙_ PointedCGWH.{u, v} ⟶ hom.{u, v} m m')
        (pointOf g) = 0
    dsimp only [pointTensor]
    have hz :
        ((0 : 𝟙_ PointedCGWH.{u, v} ⟶ hom.{u, v} m m') ⊗ₘ
          pointOf g) = 0 := by
      let _ : (tensorRight (𝟙_ PointedCGWH.{u, v})).PreservesZeroMorphisms :=
        inferInstance
      rw [MonoidalCategory.tensorHom_def]
      change (tensorRight (𝟙_ PointedCGWH.{u, v})).map 0 ≫ _ = 0
      rw [Functor.map_zero, zero_comp]
    rw [hz, zero_comp, comp_zero]
  have tensorO_zero_right {m m' n n' : OrthogonalIndex}
      (f : m ⟶ m') : tensorO f (0 : n ⟶ n') = 0 := by
    change pointTensor (pointOf f)
      (0 : 𝟙_ PointedCGWH.{u, v} ⟶ hom.{u, v} n n') = 0
    dsimp only [pointTensor]
    have hz :
        (pointOf f ⊗ₘ
          (0 : 𝟙_ PointedCGWH.{u, v} ⟶ hom.{u, v} n n')) = 0 := by
      let _ : (tensorLeft (𝟙_ PointedCGWH.{u, v})).PreservesZeroMorphisms :=
        inferInstance
      rw [MonoidalCategory.tensorHom_def']
      change (tensorLeft (𝟙_ PointedCGWH.{u, v})).map 0 ≫ _ = 0
      rw [Functor.map_zero, zero_comp]
    rw [hz, zero_comp, comp_zero]
  have blockSum_id (m n : OrthogonalIndex) :
      OrthogonalMatrixHom.blockSum (OrthogonalMatrixHom.id m)
        (OrthogonalMatrixHom.id n) = OrthogonalMatrixHom.id (m + n) := by
    apply OrthogonalMatrixHom.ext
    simp [OrthogonalMatrixHom.blockSum, OrthogonalMatrixHom.id]
  have sumCoordinates_val {a b c d : OrthogonalIndex}
      (e : Fin a ≃ Fin b) (f : Fin c ≃ Fin d)
      (he : ∀ i, (e i).val = i.val) (hf : ∀ i, (f i).val = i.val)
      (i : Fin (a + c)) : (sumCoordinates e f i).val = i.val := by
    have hab : a = b := Fin.equiv_iff_eq.mp ⟨e⟩
    rcases h : (finSumFinEquiv : Fin a ⊕ Fin c ≃ Fin (a + c)).symm i
        with ia | ic
    · have hi := congrArg
        (finSumFinEquiv : Fin a ⊕ Fin c ≃ Fin (a + c)) h
      rw [Equiv.apply_symm_apply] at hi
      have hval := congrArg Fin.val hi
      simp only [sumCoordinates, Equiv.trans_apply, h, Equiv.sumCongr_apply,
        Sum.map_inl, finSumFinEquiv_apply_left, Fin.val_castAdd]
      rw [he]
      exact hval.symm
    · have hi := congrArg
        (finSumFinEquiv : Fin a ⊕ Fin c ≃ Fin (a + c)) h
      rw [Equiv.apply_symm_apply] at hi
      have hval := congrArg Fin.val hi
      simp only [sumCoordinates, Equiv.trans_apply, h, Equiv.sumCongr_apply,
        Sum.map_inr, finSumFinEquiv_apply_right, Fin.val_natAdd]
      rw [hf, ← hab]
      exact hval.symm
  let coordinateIso {a b : OrthogonalIndex} (e : Fin a ≃ Fin b) : a ≅ b :=
    { hom := matrixArrow (isometryMatrix e)
      inv := matrixArrow (isometryMatrix e.symm)
      hom_inv_id := (by exact coordinatePoint_hom_inv_id.{u, v} e)
      inv_hom_id := (by exact coordinatePoint_inv_hom_id.{u, v} e) }
  let ops : MonoidalCategoryStruct OrthogonalIndex :=
    { tensorObj := fun m n ↦ m + n
      whiskerLeft := fun X {_ _} f ↦ tensorO (𝟙 X) f
      whiskerRight := fun {_ _} f Y ↦ tensorO f (𝟙 Y)
      tensorHom := fun {_ _ _ _} f g ↦ tensorO f g
      tensorUnit := 0
      associator := fun a b c ↦ coordinateIso
        (finCongr (Nat.add_assoc a b c))
      leftUnitor := fun a ↦ coordinateIso
        (finCongr (Nat.zero_add a))
      rightUnitor := fun a ↦ coordinateIso
        (finCongr (Nat.add_zero a)) }
  let _ : MonoidalCategoryStruct OrthogonalIndex := ops
  exact MonoidalCategory.ofTensorHom
    (id_tensorHom_id := by
      intro m n
      change tensorO (𝟙 m) (𝟙 n) = 𝟙 (m + n)
      rw [category_id, category_id, tensorO_matrix,
        blockSum_id, category_id])
    (id_tensorHom := by
      intro _ _ _ _
      rfl)
    (tensorHom_id := by
      intro _ _ _ _
      rfl)
    (tensorHom_comp_tensorHom := by
      intro X₁ Y₁ Z₁ X₂ Y₂ Z₂ f₁ f₂ g₁ g₂
      change tensorO f₁ f₂ ≫ tensorO g₁ g₂ =
        tensorO (f₁ ≫ g₁) (f₂ ≫ g₂)
      rcases homCases f₁ with rfl | ⟨A, rfl⟩ <;>
        rcases homCases f₂ with rfl | ⟨B, rfl⟩ <;>
        rcases homCases g₁ with rfl | ⟨A', rfl⟩ <;>
        rcases homCases g₂ with rfl | ⟨B', rfl⟩ <;>
        simp only [tensorO_zero_left, tensorO_zero_right,
          zero_comp, comp_zero, tensorO_matrix, matrixArrow_comp]
      exact congrArg matrixArrow
        (OrthogonalMatrixHom.blockSum_comp A A' B B').symm)
    (associator_naturality := by
      intro X₁ X₂ X₃ Y₁ Y₂ Y₃ f₁ f₂ f₃
      change tensorO (tensorO f₁ f₂) f₃ ≫
          matrixArrow (associatorMatrix Y₁ Y₂ Y₃) =
        matrixArrow (associatorMatrix X₁ X₂ X₃) ≫
          tensorO f₁ (tensorO f₂ f₃)
      rcases homCases f₁ with rfl | ⟨A, rfl⟩ <;>
        rcases homCases f₂ with rfl | ⟨B, rfl⟩ <;>
        rcases homCases f₃ with rfl | ⟨C, rfl⟩ <;>
        simp only [tensorO_zero_left, tensorO_zero_right,
          zero_comp, comp_zero, tensorO_matrix, matrixArrow_comp]
      exact congrArg matrixArrow
        (isometryMatrix_naturality
          (finCongr (Nat.add_assoc Y₁ Y₂ Y₃))
          (finCongr (Nat.add_assoc X₁ X₂ X₃))
          (OrthogonalMatrixHom.blockSum
            (OrthogonalMatrixHom.blockSum A B) C)
          (OrthogonalMatrixHom.blockSum A
            (OrthogonalMatrixHom.blockSum B C))
          (OrthogonalMatrixHom.blockSum_assoc A B C)))
    (leftUnitor_naturality := by
      intro X Y f
      change tensorO (𝟙 0) f ≫
          matrixArrow (leftUnitorMatrix Y) =
        matrixArrow (leftUnitorMatrix X) ≫ f
      rcases homCases f with rfl | ⟨A, rfl⟩
      · simp only [tensorO_zero_right, zero_comp, comp_zero]
      · rw [category_id, tensorO_matrix, matrixArrow_comp,
          matrixArrow_comp]
        exact congrArg matrixArrow
          (isometryMatrix_naturality
            (finCongr (Nat.zero_add Y))
            (finCongr (Nat.zero_add X))
            (OrthogonalMatrixHom.blockSum (OrthogonalMatrixHom.id 0) A) A
            (OrthogonalMatrixHom.blockSum_zero_left A)))
    (rightUnitor_naturality := by
      intro X Y f
      change tensorO f (𝟙 0) ≫
          matrixArrow (rightUnitorMatrix Y) =
        matrixArrow (rightUnitorMatrix X) ≫ f
      rcases homCases f with rfl | ⟨A, rfl⟩
      · simp only [tensorO_zero_left, zero_comp, comp_zero]
      · rw [category_id, tensorO_matrix, matrixArrow_comp,
          matrixArrow_comp]
        exact congrArg matrixArrow
          (isometryMatrix_naturality
            (finCongr (Nat.add_zero Y))
            (finCongr (Nat.add_zero X))
            (OrthogonalMatrixHom.blockSum A (OrthogonalMatrixHom.id 0)) A
            (OrthogonalMatrixHom.blockSum_zero_right A)))
    (pentagon := by
      intro W X Y Z
      change tensorO
          (matrixArrow (associatorMatrix W X Y)) (𝟙 Z) ≫
            matrixArrow (associatorMatrix W (X + Y) Z) ≫
              tensorO (𝟙 W)
                (matrixArrow (associatorMatrix X Y Z)) =
        matrixArrow (associatorMatrix (W + X) Y Z) ≫
          matrixArrow (associatorMatrix W X (Y + Z))
      rw [category_id, category_id, tensorO_matrix,
        tensorO_matrix]
      rw [show OrthogonalMatrixHom.id Z =
          isometryMatrix (Equiv.refl (Fin Z)) from
            (isometryMatrix_refl Z).symm,
        show OrthogonalMatrixHom.id W =
          isometryMatrix (Equiv.refl (Fin W)) from
            (isometryMatrix_refl W).symm]
      dsimp only [associatorMatrix]
      rw [isometryMatrix_blockSum,
        isometryMatrix_blockSum, matrixArrow_comp,
        matrixArrow_comp, matrixArrow_comp]
      apply congrArg matrixArrow
      rw [isometryMatrix_comp, isometryMatrix_comp,
        isometryMatrix_comp]
      let e₁ := sumCoordinates (finCongr (Nat.add_assoc W X Y))
        (Equiv.refl (Fin Z))
      let e₂ := finCongr (Nat.add_assoc W (X + Y) Z)
      let e₃ := sumCoordinates (Equiv.refl (Fin W))
        (finCongr (Nat.add_assoc X Y Z))
      let r₁ := finCongr (Nat.add_assoc (W + X) Y Z)
      let r₂ := finCongr (Nat.add_assoc W X (Y + Z))
      change isometryMatrix (e₁.trans (e₂.trans e₃)) =
        isometryMatrix (r₁.trans r₂)
      congr 1
      apply Equiv.ext
      intro i
      apply Fin.ext
      change (e₃ (e₂ (e₁ i))).val = (r₂ (r₁ i)).val
      calc
        _ = (e₂ (e₁ i)).val := sumCoordinates_val _ _
          (fun _ ↦ rfl) (fun _ ↦ rfl) _
        _ = (e₁ i).val := by rfl
        _ = i.val := sumCoordinates_val _ _
          (fun _ ↦ rfl) (fun _ ↦ rfl) _
        _ = _ := by rfl)
    (triangle := by
      intro X Y
      change matrixArrow (associatorMatrix X 0 Y) ≫
          tensorO (𝟙 X)
            (matrixArrow (leftUnitorMatrix Y)) =
        tensorO (matrixArrow (rightUnitorMatrix X)) (𝟙 Y)
      rw [category_id, category_id, tensorO_matrix,
        tensorO_matrix]
      rw [show OrthogonalMatrixHom.id X =
          isometryMatrix (Equiv.refl (Fin X)) from
            (isometryMatrix_refl X).symm,
        show OrthogonalMatrixHom.id Y =
          isometryMatrix (Equiv.refl (Fin Y)) from
            (isometryMatrix_refl Y).symm]
      dsimp only [associatorMatrix, leftUnitorMatrix, rightUnitorMatrix]
      rw [isometryMatrix_blockSum,
        isometryMatrix_blockSum, matrixArrow_comp,
        isometryMatrix_comp]
      apply congrArg matrixArrow
      let e₁ := finCongr (Nat.add_assoc X 0 Y)
      let e₂ := sumCoordinates (Equiv.refl (Fin X))
        (finCongr (Nat.zero_add Y))
      let r := sumCoordinates (finCongr (Nat.add_zero X))
        (Equiv.refl (Fin Y))
      change isometryMatrix (e₁.trans e₂) = isometryMatrix r
      congr 1
      apply Equiv.ext
      intro i
      apply Fin.ext
      change (e₂ (e₁ i)).val = (r i).val
      calc
        _ = (e₁ i).val := sumCoordinates_val _ _
          (fun _ ↦ rfl) (fun _ ↦ rfl) _
        _ = i.val := by rfl
        _ = _ := (sumCoordinates_val _ _
          (fun _ ↦ rfl) (fun _ ↦ rfl) _).symm)

/-- The selected block-swap symmetric structure on the native orthogonal
index. -/
@[instance_reducible]
noncomputable def symmetricCategory :
    @SymmetricCategory OrthogonalIndex (category.{u, v})
      (monoidalCategory.{u, v}) := by
  let _ : Category.{v} OrthogonalIndex := category.{u, v}
  let isometryMatrix
      {m n : OrthogonalIndex} (e : Fin m ≃ Fin n) :
      OrthogonalMatrixHom m n := by
    let M : Matrix (Fin n) (Fin m) ℝ :=
      Matrix.reindex e (Equiv.refl (Fin m)) 1
    refine ⟨M, ?_, ?_⟩
    · dsimp only [M]
      rw [Matrix.transpose_reindex]
      change (Matrix.reindexLinearEquiv ℝ ℝ (Equiv.refl (Fin m)) e)
            (1 : Matrix (Fin m) (Fin m) ℝ).transpose *
          (Matrix.reindexLinearEquiv ℝ ℝ e (Equiv.refl (Fin m)))
            (1 : Matrix (Fin m) (Fin m) ℝ) = 1
      rw [Matrix.reindexLinearEquiv_mul]
      simp
    · dsimp only [M]
      rw [Matrix.transpose_reindex]
      change (Matrix.reindexLinearEquiv ℝ ℝ e (Equiv.refl (Fin m)))
            (1 : Matrix (Fin m) (Fin m) ℝ) *
          (Matrix.reindexLinearEquiv ℝ ℝ (Equiv.refl (Fin m)) e)
            (1 : Matrix (Fin m) (Fin m) ℝ).transpose = 1
      rw [Matrix.reindexLinearEquiv_mul]
      simp
  let sumCoordinates
      {a b c d : OrthogonalIndex}
      (e : Fin a ≃ Fin b) (f : Fin c ≃ Fin d) :
      Fin (a + c) ≃ Fin (b + d) :=
    (finSumFinEquiv : Fin a ⊕ Fin c ≃ Fin (a + c)).symm.trans
      ((Equiv.sumCongr e f).trans
        (finSumFinEquiv : Fin b ⊕ Fin d ≃ Fin (b + d)))
  let matrixArrow
      {m n : OrthogonalIndex} (A : OrthogonalMatrixHom m n) :
      letI : Category.{v} OrthogonalIndex := category.{u, v}
      m ⟶ n := by
    change 𝟙_ PointedCGWH.{u, v} ⟶ hom.{u, v} m n
    exact matrixPoint.{u, v} A
  have matrixArrow_comp {m n p : OrthogonalIndex}
      (A : OrthogonalMatrixHom m n) (B : OrthogonalMatrixHom n p) :
      matrixArrow A ≫ matrixArrow B =
        matrixArrow (OrthogonalMatrixHom.comp A B) := by
    unfold matrixArrow
    change (λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫
        (matrixPoint.{u, v} A ⊗ₘ matrixPoint.{u, v} B) ≫
          @eComp PointedCGWH.{u, v} _ _ OrthogonalIndex
            (enrichedCategory.{u, v}) m n p = _
    exact (enrichedCategory_comp.{u, v} A B).1
  let associatorMatrix
      (a b c : OrthogonalIndex) :
      OrthogonalMatrixHom ((a + b) + c) (a + (b + c)) :=
    isometryMatrix (finCongr (Nat.add_assoc a b c))
  let _ : MonoidalCategory OrthogonalIndex := monoidalCategory.{u, v}
  let pointOf {m n : OrthogonalIndex} (f : m ⟶ n) :
      𝟙_ PointedCGWH.{u, v} ⟶ hom.{u, v} m n := by
    change 𝟙_ PointedCGWH.{u, v} ⟶ hom.{u, v} m n at f
    exact f
  let homOf {m n : OrthogonalIndex}
      (f : 𝟙_ PointedCGWH.{u, v} ⟶ hom.{u, v} m n) : m ⟶ n := by
    change 𝟙_ PointedCGWH.{u, v} ⟶ hom.{u, v} m n
    exact f
  let zeroMorphisms : HasZeroMorphisms OrthogonalIndex := zeroMorphisms
  let _ : HasZeroMorphisms OrthogonalIndex := zeroMorphisms
  have category_id (n : OrthogonalIndex) :
      (𝟙 n) = matrixArrow (OrthogonalMatrixHom.id n) := by
    unfold matrixArrow
    change @eId PointedCGWH.{u, v} _ _ OrthogonalIndex
      (enrichedCategory.{u, v}) n = _
    exact enrichedCategory_id.{u, v} n
  have isometryMatrix_naturality
      {a b c d : OrthogonalIndex}
      (e : Fin b ≃ Fin d) (f : Fin a ≃ Fin c)
      (A : OrthogonalMatrixHom a b) (B : OrthogonalMatrixHom c d)
      (h : Matrix.reindex e f A.1 = B.1) :
      OrthogonalMatrixHom.comp A (isometryMatrix e) =
        OrthogonalMatrixHom.comp (isometryMatrix f) B :=
    (by exact coordinateLaws.1 e f A B h)
  have isometryMatrix_blockSum
      {a b c d : OrthogonalIndex}
      (e : Fin a ≃ Fin b) (f : Fin c ≃ Fin d) :
      OrthogonalMatrixHom.blockSum (isometryMatrix e)
          (isometryMatrix f) = isometryMatrix (sumCoordinates e f) :=
    (by exact coordinateLaws.2.1 e f)
  have isometryMatrix_comp
      {a b c : OrthogonalIndex}
      (e : Fin a ≃ Fin b) (f : Fin b ≃ Fin c) :
      OrthogonalMatrixHom.comp (isometryMatrix e)
          (isometryMatrix f) = isometryMatrix (e.trans f) :=
    (by exact coordinateLaws.2.2.1 e f)
  have isometryMatrix_refl (a : OrthogonalIndex) :
      isometryMatrix (Equiv.refl (Fin a)) = OrthogonalMatrixHom.id a :=
    (by exact coordinateLaws.2.2.2 a)
  have homCases {m n : OrthogonalIndex} (f : m ⟶ n) :
      f = 0 ∨ ∃ A : OrthogonalMatrixHom m n,
        f = matrixArrow A := by
    exact (by
      change f = 0 ∨ ∃ A : OrthogonalMatrixHom m n,
        f = matrixPoint.{u, v} A
      rcases freePoint_cases.{u, v} (rawHomCGWH.{u, v} m n) f with
        h | ⟨z, h⟩
      · exact Or.inl h
      · change ULift.{v, 0} (OrthogonalMatrixHom m n) at z
        rcases z with ⟨A⟩
        exact Or.inr ⟨A, h⟩
    )
  have tensor_matrix {m m' n n' : OrthogonalIndex}
      (A : OrthogonalMatrixHom m m') (B : OrthogonalMatrixHom n n') :
      matrixArrow A ⊗ₘ matrixArrow B =
        matrixArrow (OrthogonalMatrixHom.blockSum A B) := by
    change (λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫
        (matrixPoint.{u, v} A ⊗ₘ matrixPoint.{u, v} B) ≫
          tensorMap.{u, v} m m' n n' =
        matrixPoint.{u, v} (OrthogonalMatrixHom.blockSum A B)
    exact (tensorMap_blockSum.{u, v} A B).1
  have tensor_zero_left {m m' n n' : OrthogonalIndex}
      (g : n ⟶ n') : (0 : m ⟶ m') ⊗ₘ g = 0 := by
    change (λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫
        ((0 : 𝟙_ PointedCGWH.{u, v} ⟶ hom.{u, v} m m') ⊗ₘ
          pointOf g) ≫ tensorMap.{u, v} m m' n n' = 0
    have hz :
        ((0 : 𝟙_ PointedCGWH.{u, v} ⟶ hom.{u, v} m m') ⊗ₘ
          pointOf g) = 0 := by
      let _ : (tensorRight (𝟙_ PointedCGWH.{u, v})).PreservesZeroMorphisms :=
        inferInstance
      rw [MonoidalCategory.tensorHom_def]
      change (tensorRight (𝟙_ PointedCGWH.{u, v})).map 0 ≫ _ = 0
      rw [Functor.map_zero, zero_comp]
    rw [hz, zero_comp, comp_zero]
  have tensor_zero_right {m m' n n' : OrthogonalIndex}
      (f : m ⟶ m') : f ⊗ₘ (0 : n ⟶ n') = 0 := by
    change (λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫
        (pointOf f ⊗ₘ
          (0 : 𝟙_ PointedCGWH.{u, v} ⟶ hom.{u, v} n n')) ≫
          tensorMap.{u, v} m m' n n' = 0
    have hz :
        (pointOf f ⊗ₘ
          (0 : 𝟙_ PointedCGWH.{u, v} ⟶ hom.{u, v} n n')) = 0 := by
      let _ : (tensorLeft (𝟙_ PointedCGWH.{u, v})).PreservesZeroMorphisms :=
        inferInstance
      rw [MonoidalCategory.tensorHom_def']
      change (tensorLeft (𝟙_ PointedCGWH.{u, v})).map 0 ≫ _ = 0
      rw [Functor.map_zero, zero_comp]
    rw [hz, zero_comp, comp_zero]
  have finAdd_left {a b c d : ℕ}
      (e : Fin a ≃ Fin b) (f : Fin c ≃ Fin d) (x : Fin a) :
      sumCoordinates e f (Fin.castAdd c x) = Fin.castAdd d (e x) := by
    simp [sumCoordinates]
  have finAdd_right {a b c d : ℕ}
      (e : Fin a ≃ Fin b) (f : Fin c ≃ Fin d) (x : Fin c) :
      sumCoordinates e f (Fin.natAdd a x) = Fin.natAdd b (f x) := by
    simp [sumCoordinates]
  have assoc_left (a b c : ℕ) (x : Fin a) :
      finCongr (Nat.add_assoc a b c)
          (Fin.castAdd c (Fin.castAdd b x)) =
        Fin.castAdd (b + c) x := by
    apply Fin.ext
    rfl
  have assoc_middle (a b c : ℕ) (x : Fin b) :
      finCongr (Nat.add_assoc a b c)
          (Fin.castAdd c (Fin.natAdd a x)) =
        Fin.natAdd a (Fin.castAdd c x) := by
    apply Fin.ext
    rfl
  have assoc_right (a b c : ℕ) (x : Fin c) :
      finCongr (Nat.add_assoc a b c) (Fin.natAdd (a + b) x) =
        Fin.natAdd a (Fin.natAdd b x) := by
    apply Fin.ext
    simp only [finCongr_apply_coe, Fin.val_natAdd]
    omega
  have assoc_inv_left (a b c : ℕ) (x : Fin a) :
      (finCongr (Nat.add_assoc a b c)).symm
          (Fin.castAdd (b + c) x) =
        Fin.castAdd c (Fin.castAdd b x) := by
    apply Fin.ext
    rfl
  have assoc_inv_middle (a b c : ℕ) (x : Fin b) :
      (finCongr (Nat.add_assoc a b c)).symm
          (Fin.natAdd a (Fin.castAdd c x)) =
        Fin.castAdd c (Fin.natAdd a x) := by
    apply Fin.ext
    rfl
  have assoc_inv_right (a b c : ℕ) (x : Fin c) :
      (finCongr (Nat.add_assoc a b c)).symm
          (Fin.natAdd a (Fin.natAdd b x)) =
        Fin.natAdd (a + b) x := by
    apply Fin.ext
    simp only [finCongr_symm_apply_coe, Fin.val_natAdd]
    omega
  let coordinateIso {a b : OrthogonalIndex} (e : Fin a ≃ Fin b) : a ≅ b :=
    { hom := matrixArrow (isometryMatrix e)
      inv := matrixArrow (isometryMatrix e.symm)
      hom_inv_id := (by exact coordinatePoint_hom_inv_id.{u, v} e)
      inv_hom_id := (by exact coordinatePoint_inv_hom_id.{u, v} e) }
  have blockSwap_eq (m n : OrthogonalIndex) :
      blockSwap m n =
        isometryMatrix (finAddFlip : Fin (m + n) ≃ Fin (n + m)) := by
    rfl
  let braid (m n : OrthogonalIndex) : m ⊗ n ≅ n ⊗ m :=
    coordinateIso
      (finAddFlip : Fin (m + n) ≃ Fin (n + m))
  let braided : BraidedCategory OrthogonalIndex :=
    @BraidedCategory.mk OrthogonalIndex _ _ braid
      (by
        intro X Y Z f
        change (𝟙 X ⊗ₘ f) ≫
            matrixArrow (blockSwap X Z) =
          matrixArrow (blockSwap X Y) ≫ (f ⊗ₘ 𝟙 X)
        rcases homCases f with rfl | ⟨A, rfl⟩
        · simp only [tensor_zero_left, tensor_zero_right,
            zero_comp, comp_zero]
        · rw [category_id, tensor_matrix, tensor_matrix,
            matrixArrow_comp, matrixArrow_comp]
          exact congrArg matrixArrow
            (isometryMatrix_naturality
              (finAddFlip : Fin (X + Z) ≃ Fin (Z + X))
              (finAddFlip : Fin (X + Y) ≃ Fin (Y + X))
              (OrthogonalMatrixHom.blockSum (OrthogonalMatrixHom.id X) A)
              (OrthogonalMatrixHom.blockSum A (OrthogonalMatrixHom.id X))
              (OrthogonalMatrixHom.blockSum_swap
                (OrthogonalMatrixHom.id X) A)))
      (by
        intro X Y f Z
        change (f ⊗ₘ 𝟙 Z) ≫
            matrixArrow (blockSwap Y Z) =
          matrixArrow (blockSwap X Z) ≫ (𝟙 Z ⊗ₘ f)
        rcases homCases f with rfl | ⟨A, rfl⟩
        · simp only [tensor_zero_left, tensor_zero_right,
            zero_comp, comp_zero]
        · rw [category_id, tensor_matrix, tensor_matrix,
            matrixArrow_comp, matrixArrow_comp]
          exact congrArg matrixArrow
            (isometryMatrix_naturality
              (finAddFlip : Fin (Y + Z) ≃ Fin (Z + Y))
              (finAddFlip : Fin (X + Z) ≃ Fin (Z + X))
              (OrthogonalMatrixHom.blockSum A (OrthogonalMatrixHom.id Z))
              (OrthogonalMatrixHom.blockSum (OrthogonalMatrixHom.id Z) A)
              (OrthogonalMatrixHom.blockSum_swap A
                (OrthogonalMatrixHom.id Z))))
      (by
        intro X Y Z
        change matrixArrow (associatorMatrix X Y Z) ≫
              matrixArrow (blockSwap X (Y + Z)) ≫
                matrixArrow (associatorMatrix Y Z X) =
          (matrixArrow (blockSwap X Y) ⊗ₘ 𝟙 Z) ≫
              matrixArrow (associatorMatrix Y X Z) ≫
                (𝟙 Y ⊗ₘ matrixArrow (blockSwap X Z))
        rw [category_id, category_id, tensor_matrix, tensor_matrix]
        rw [show OrthogonalMatrixHom.id Z =
            isometryMatrix (Equiv.refl (Fin Z)) from
              (isometryMatrix_refl Z).symm,
          show OrthogonalMatrixHom.id Y =
            isometryMatrix (Equiv.refl (Fin Y)) from
              (isometryMatrix_refl Y).symm]
        dsimp only [associatorMatrix]
        simp only [blockSwap_eq]
        rw [isometryMatrix_blockSum, isometryMatrix_blockSum,
          matrixArrow_comp, matrixArrow_comp, matrixArrow_comp,
          matrixArrow_comp]
        simp only [isometryMatrix_comp]
        apply congrArg matrixArrow
        let l₁ := finCongr (Nat.add_assoc X Y Z)
        let l₂ := (finAddFlip : Fin (X + (Y + Z)) ≃ Fin ((Y + Z) + X))
        let l₃ := finCongr (Nat.add_assoc Y Z X)
        let r₁ := sumCoordinates
          (finAddFlip : Fin (X + Y) ≃ Fin (Y + X)) (Equiv.refl (Fin Z))
        let r₂ := finCongr (Nat.add_assoc Y X Z)
        let r₃ := sumCoordinates (Equiv.refl (Fin Y))
          (finAddFlip : Fin (X + Z) ≃ Fin (Z + X))
        change isometryMatrix (l₁.trans (l₂.trans l₃)) =
          isometryMatrix (r₁.trans (r₂.trans r₃))
        congr 1
        apply Equiv.ext
        intro i
        apply Fin.ext
        change (l₃ (l₂ (l₁ i))).val = (r₃ (r₂ (r₁ i))).val
        let src : (Fin X ⊕ Fin Y) ⊕ Fin Z ≃ Fin ((X + Y) + Z) :=
          (Equiv.sumCongr
            (finSumFinEquiv : Fin X ⊕ Fin Y ≃ Fin (X + Y))
            (Equiv.refl (Fin Z))).trans finSumFinEquiv
        rcases src.surjective i with ⟨q, rfl⟩
        rcases q with (x | y) | z
        all_goals simp [src, l₁, l₂, l₃, r₁, r₂, r₃,
          finAddFlip,
          finAdd_left, finAdd_right, assoc_left, assoc_middle, assoc_right])
      (by
        intro X Y Z
        change (coordinateIso
              (finCongr (Nat.add_assoc X Y Z))).inv ≫
              matrixArrow (blockSwap (X + Y) Z) ≫
                (coordinateIso
                  (finCongr (Nat.add_assoc Z X Y))).inv =
          (𝟙 X ⊗ₘ matrixArrow (blockSwap Y Z)) ≫
              (coordinateIso
                (finCongr (Nat.add_assoc X Z Y))).inv ≫
                (matrixArrow (blockSwap X Z) ⊗ₘ 𝟙 Y)
        rw [category_id, category_id, tensor_matrix, tensor_matrix]
        simp only [blockSwap_eq]
        rw [show OrthogonalMatrixHom.id X =
            isometryMatrix (Equiv.refl (Fin X)) from
              (isometryMatrix_refl X).symm,
          show OrthogonalMatrixHom.id Y =
            isometryMatrix (Equiv.refl (Fin Y)) from
              (isometryMatrix_refl Y).symm,
          isometryMatrix_blockSum, isometryMatrix_blockSum]
        have coordinateIso_inv {a b : OrthogonalIndex} (e : Fin a ≃ Fin b) :
            (coordinateIso e).inv =
              matrixArrow (isometryMatrix e.symm) := rfl
        rw [coordinateIso_inv, coordinateIso_inv, coordinateIso_inv]
        rw [matrixArrow_comp, matrixArrow_comp, matrixArrow_comp,
          matrixArrow_comp]
        simp only [isometryMatrix_comp]
        apply congrArg matrixArrow
        let l₁ := (finCongr (Nat.add_assoc X Y Z)).symm
        let l₂ := (finAddFlip : Fin ((X + Y) + Z) ≃ Fin (Z + (X + Y)))
        let l₃ := (finCongr (Nat.add_assoc Z X Y)).symm
        let r₁ := sumCoordinates (Equiv.refl (Fin X))
          (finAddFlip : Fin (Y + Z) ≃ Fin (Z + Y))
        let r₂ := (finCongr (Nat.add_assoc X Z Y)).symm
        let r₃ := sumCoordinates
          (finAddFlip : Fin (X + Z) ≃ Fin (Z + X)) (Equiv.refl (Fin Y))
        change isometryMatrix (l₁.trans (l₂.trans l₃)) =
          isometryMatrix (r₁.trans (r₂.trans r₃))
        congr 1
        apply Equiv.ext
        intro i
        apply Fin.ext
        change (l₃ (l₂ (l₁ i))).val = (r₃ (r₂ (r₁ i))).val
        let src : Fin X ⊕ (Fin Y ⊕ Fin Z) ≃ Fin (X + (Y + Z)) :=
          (Equiv.sumCongr (Equiv.refl (Fin X))
            (finSumFinEquiv : Fin Y ⊕ Fin Z ≃ Fin (Y + Z))).trans
              finSumFinEquiv
        rcases src.surjective i with ⟨q, rfl⟩
        rcases q with x | (y | z)
        all_goals
          dsimp only [src, l₁, l₂, l₃, r₁, r₂, r₃,
            Equiv.trans_apply, Equiv.sumCongr_apply, Equiv.refl_apply]
        all_goals
          simp only [Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr,
            Equiv.refl_apply, finSumFinEquiv_apply_left,
            finSumFinEquiv_apply_right, finAdd_left, finAdd_right,
            assoc_inv_left, assoc_inv_middle, assoc_inv_right,
            finAddFlip_apply_castAdd, finAddFlip_apply_natAdd,
            Fin.val_castAdd, Fin.val_natAdd])
  let _ : BraidedCategory OrthogonalIndex := braided
  exact @SymmetricCategory.mk OrthogonalIndex _ _ braided (by
    intro X Y
    change matrixArrow (blockSwap X Y) ≫
        matrixArrow (blockSwap Y X) = 𝟙 (X ⊗ Y)
    rw [matrixArrow_comp, category_id]
    apply congrArg matrixArrow
    dsimp only [blockSwap]
    rw [isometryMatrix_comp]
    change isometryMatrix (finAddFlip.trans finAddFlip) =
      OrthogonalMatrixHom.id (X + Y)
    rw [← isometryMatrix_refl (X + Y)]
    congr 1
    apply Equiv.ext
    intro i
    rcases (finSumFinEquiv : Fin X ⊕ Fin Y ≃ Fin (X + Y)).surjective i with
      ⟨x | y, rfl⟩ <;>
      simp [finAddFlip])

private theorem rawAssociator_naturality_law
    (i i' j j' k k' : OrthogonalIndex) :
    letI : EnrichedCategory CGWH.{u, v} OrthogonalIndex :=
      rawEnrichedCategory.{u, v}
    letI : BraidedCategory CGWH.{u, v} :=
      BraidedCategory.ofCartesianMonoidalCategory
    let A := rawHomCGWH.{u, v} i i'
    let B := rawHomCGWH.{u, v} j j'
    let C := rawHomCGWH.{u, v} k k'
    let leftRaw : ((A ⊗ B) ⊗ C) ⟶
        rawHomCGWH.{u, v} ((i + j) + k) ((i' + j') + k') :=
      (rawBlockSum.{u, v} i i' j j' ▷ C) ≫
        rawBlockSum.{u, v} (i + j) (i' + j') k k'
    let rightRaw : (A ⊗ (B ⊗ C)) ⟶
        rawHomCGWH.{u, v} (i + (j + k)) (i' + (j' + k')) :=
      (A ◁ rawBlockSum.{u, v} j j' k k') ≫
        rawBlockSum.{u, v} i i' (j + k) (j' + k')
    let aSource := rawPointFromUnit.{u, v} (associatorHom i j k)
    let aTarget := rawPointFromUnit.{u, v} (associatorHom i' j' k')
    (β_ (𝟙_ CGWH.{u, v}) ((A ⊗ B) ⊗ C)).hom ≫
          (leftRaw ⊗ₘ aTarget) ≫
        rawComp.{u, v} ((i + j) + k) ((i' + j') + k')
          (i' + (j' + k')) =
      (aSource ⊗ₘ ((α_ A B C).hom ≫ rightRaw)) ≫
        rawComp.{u, v} ((i + j) + k) (i + (j + k))
          (i' + (j' + k')) := by
  dsimp only
  let _ : EnrichedCategory CGWH.{u, v} OrthogonalIndex :=
    rawEnrichedCategory.{u, v}
  let _ : BraidedCategory CGWH.{u, v} :=
    BraidedCategory.ofCartesianMonoidalCategory
  apply ConcreteCategory.hom_ext
  intro z
  let AObj := rawHomCGWH.{u, v} i i'
  let BObj := rawHomCGWH.{u, v} j j'
  let CObj := rawHomCGWH.{u, v} k k'
  let ABObj := AObj ⊗ BObj
  let HObj := ABObj ⊗ CObj
  let zH : HObj := CartesianMonoidalCategory.snd (𝟙_ CGWH.{u, v}) HObj z
  let zAB : ABObj := CartesianMonoidalCategory.fst ABObj CObj zH
  let zC : CObj := CartesianMonoidalCategory.snd ABObj CObj zH
  let zA : AObj := CartesianMonoidalCategory.fst AObj BObj zAB
  let zB : BObj := CartesianMonoidalCategory.snd AObj BObj zAB
  have hzA : CartesianMonoidalCategory.fst AObj BObj zAB = zA := rfl
  have hzB : CartesianMonoidalCategory.snd AObj BObj zAB = zB := rfl
  have hzC : CartesianMonoidalCategory.snd ABObj CObj zH = zC := rfl
  rcases hA : zA with ⟨A⟩
  rcases hB : zB with ⟨B⟩
  rcases hC : zC with ⟨C⟩
  have hzAB : rawBlockSum.{u, v} i i' j j' zAB =
      ULift.up (OrthogonalMatrixHom.blockSum A B) := by
    rw [rawBlockSum_apply]
    rw [hzA, hzB, hA, hB]
  have hLeft :
      ((rawBlockSum.{u, v} i i' j j' ▷
          rawHomCGWH.{u, v} k k') ≫
        rawBlockSum.{u, v} (i + j) (i' + j') k k') zH =
      ULift.up (OrthogonalMatrixHom.blockSum
        (OrthogonalMatrixHom.blockSum A B) C) := by
    rw [ConcreteCategory.comp_apply, rawBlockSum_apply]
    have hf := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.whiskerRight_fst
        (rawBlockSum.{u, v} i i' j j') CObj) zH
    have hs := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.whiskerRight_snd
        (rawBlockSum.{u, v} i i' j j') CObj) zH
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hf
    rw [ConcreteCategory.comp_apply] at hs
    rw [hf, hs, hzAB, hzC, hC]
  let w : (AObj ⊗ (BObj ⊗ CObj) : CGWH.{u, v}) :=
    (α_ AObj BObj CObj).hom zH
  have hwA : CartesianMonoidalCategory.fst AObj (BObj ⊗ CObj) w =
      (⟨A⟩ : AObj) := by
    rw [← hA]
    exact ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.associator_hom_fst AObj BObj CObj) zH
  have hwB : CartesianMonoidalCategory.fst BObj CObj
      (CartesianMonoidalCategory.snd AObj (BObj ⊗ CObj) w) =
      (⟨B⟩ : BObj) := by
    rw [← hB]
    exact ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.associator_hom_snd_fst AObj BObj CObj) zH
  have hwC : CartesianMonoidalCategory.snd BObj CObj
      (CartesianMonoidalCategory.snd AObj (BObj ⊗ CObj) w) =
      (⟨C⟩ : CObj) := by
    rw [← hC]
    exact ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.associator_hom_snd_snd AObj BObj CObj) zH
  have hRight :
      ((AObj ◁ rawBlockSum.{u, v} j j' k k') ≫
        rawBlockSum.{u, v} i i' (j + k) (j' + k')) w =
      ULift.up (OrthogonalMatrixHom.blockSum A
        (OrthogonalMatrixHom.blockSum B C)) := by
    rw [ConcreteCategory.comp_apply, rawBlockSum_apply]
    have hf := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.whiskerLeft_fst AObj
        (rawBlockSum.{u, v} j j' k k')) w
    have hs := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.whiskerLeft_snd AObj
        (rawBlockSum.{u, v} j j' k k')) w
    rw [ConcreteCategory.comp_apply] at hf
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hs
    have hBC : rawBlockSum.{u, v} j j' k k'
        (CartesianMonoidalCategory.snd AObj (BObj ⊗ CObj) w) =
        ULift.up (OrthogonalMatrixHom.blockSum B C) := by
      rw [rawBlockSum_apply, hwB, hwC]
    rw [hf, hs, hwA, hBC]
  have hRawPoint {a b : OrthogonalIndex}
      (D : OrthogonalMatrixHom a b) (x : (𝟙_ CGWH.{u, v} : Type v)) :
      rawPointFromUnit.{u, v} D x = ULift.up D := by
    let R : CGWH.{u, v} := rawHomCGWH.{u, v} a b
    let d : R := ULift.up D
    let pUnit : CGWH.point.{u, v} ≅ 𝟙_ CGWH.{u, v} :=
      CGWH.point_isTerminal.uniqueUpToIso
        CartesianMonoidalCategory.isTerminalTensorUnit
    change (CGWH.pointHomEquiv R).symm d (pUnit.inv x) = d
    exact CGWH.pointHomEquiv_symm_apply_apply R d (pUnit.inv x)
  let preL : (HObj ⊗ 𝟙_ CGWH.{u, v} : CGWH.{u, v}) :=
    (β_ (𝟙_ CGWH.{u, v}) HObj).hom z
  let yL : (rawHomCGWH.{u, v} ((i + j) + k) ((i' + j') + k') ⊗
      rawHomCGWH.{u, v} ((i' + j') + k') (i' + (j' + k')) : CGWH.{u, v}) :=
    ((rawBlockSum.{u, v} i i' j j' ▷ CObj ≫
        rawBlockSum.{u, v} (i + j) (i' + j') k k') ⊗ₘ
      rawPointFromUnit.{u, v} (associatorHom i' j' k')) preL
  have hpreLf : CartesianMonoidalCategory.fst HObj (𝟙_ CGWH.{u, v}) preL =
      zH := by
    exact ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.braiding_hom_fst
        (𝟙_ CGWH.{u, v}) HObj) z
  have hyLf : CartesianMonoidalCategory.fst
      (rawHomCGWH.{u, v} ((i + j) + k) ((i' + j') + k'))
      (rawHomCGWH.{u, v} ((i' + j') + k') (i' + (j' + k'))) yL =
      ULift.up (OrthogonalMatrixHom.blockSum
        (OrthogonalMatrixHom.blockSum A B) C) := by
    calc
      _ = ((rawBlockSum.{u, v} i i' j j' ▷ CObj ≫
            rawBlockSum.{u, v} (i + j) (i' + j') k k')
          (CartesianMonoidalCategory.fst HObj (𝟙_ CGWH.{u, v}) preL)) := by
            simpa only [ConcreteCategory.comp_apply] using
              ConcreteCategory.congr_hom
                (CartesianMonoidalCategory.tensorHom_fst
                  (rawBlockSum.{u, v} i i' j j' ▷ CObj ≫
                    rawBlockSum.{u, v} (i + j) (i' + j') k k')
                  (rawPointFromUnit.{u, v} (associatorHom i' j' k'))) preL
      _ = _ := by rw [hpreLf, hLeft]
  have hyLs : CartesianMonoidalCategory.snd
      (rawHomCGWH.{u, v} ((i + j) + k) ((i' + j') + k'))
      (rawHomCGWH.{u, v} ((i' + j') + k') (i' + (j' + k'))) yL =
      ULift.up (associatorHom i' j' k') := by
    have hPointValue : CartesianMonoidalCategory.snd
      (rawHomCGWH.{u, v} ((i + j) + k) ((i' + j') + k'))
      (rawHomCGWH.{u, v} ((i' + j') + k') (i' + (j' + k'))) yL =
        rawPointFromUnit.{u, v} (associatorHom i' j' k')
          (CartesianMonoidalCategory.snd HObj (𝟙_ CGWH.{u, v}) preL) := by
          simpa only [ConcreteCategory.comp_apply] using
            ConcreteCategory.congr_hom
              (CartesianMonoidalCategory.tensorHom_snd
                (rawBlockSum.{u, v} i i' j j' ▷ CObj ≫
                  rawBlockSum.{u, v} (i + j) (i' + j') k k')
                (rawPointFromUnit.{u, v} (associatorHom i' j' k'))) preL
    exact hPointValue.trans (hRawPoint _ _)
  let yR : (rawHomCGWH.{u, v} ((i + j) + k) (i + (j + k)) ⊗
      rawHomCGWH.{u, v} (i + (j + k)) (i' + (j' + k')) : CGWH.{u, v}) :=
    (rawPointFromUnit.{u, v} (associatorHom i j k) ⊗ₘ
      ((α_ AObj BObj CObj).hom ≫
        (AObj ◁ rawBlockSum.{u, v} j j' k k') ≫
        rawBlockSum.{u, v} i i' (j + k) (j' + k'))) z
  have hyRf : CartesianMonoidalCategory.fst
      (rawHomCGWH.{u, v} ((i + j) + k) (i + (j + k)))
      (rawHomCGWH.{u, v} (i + (j + k)) (i' + (j' + k'))) yR =
      ULift.up (associatorHom i j k) := by
    have hPointValue : CartesianMonoidalCategory.fst
      (rawHomCGWH.{u, v} ((i + j) + k) (i + (j + k)))
      (rawHomCGWH.{u, v} (i + (j + k)) (i' + (j' + k'))) yR =
        rawPointFromUnit.{u, v} (associatorHom i j k)
          (CartesianMonoidalCategory.fst (𝟙_ CGWH.{u, v}) HObj z) := by
          simpa only [ConcreteCategory.comp_apply] using
            ConcreteCategory.congr_hom
              (CartesianMonoidalCategory.tensorHom_fst
                (rawPointFromUnit.{u, v} (associatorHom i j k))
                ((α_ AObj BObj CObj).hom ≫
                  (AObj ◁ rawBlockSum.{u, v} j j' k k') ≫
                  rawBlockSum.{u, v} i i' (j + k) (j' + k'))) z
    exact hPointValue.trans (hRawPoint _ _)
  have hyRs : CartesianMonoidalCategory.snd
      (rawHomCGWH.{u, v} ((i + j) + k) (i + (j + k)))
      (rawHomCGWH.{u, v} (i + (j + k)) (i' + (j' + k'))) yR =
      ULift.up (OrthogonalMatrixHom.blockSum A
        (OrthogonalMatrixHom.blockSum B C)) := by
    calc
      _ = ((α_ AObj BObj CObj).hom ≫
            (AObj ◁ rawBlockSum.{u, v} j j' k k') ≫
            rawBlockSum.{u, v} i i' (j + k) (j' + k'))
          (CartesianMonoidalCategory.snd (𝟙_ CGWH.{u, v}) HObj z) := by
            simpa only [ConcreteCategory.comp_apply] using
              ConcreteCategory.congr_hom
                (CartesianMonoidalCategory.tensorHom_snd
                  (rawPointFromUnit.{u, v} (associatorHom i j k))
                  ((α_ AObj BObj CObj).hom ≫
                    (AObj ◁ rawBlockSum.{u, v} j j' k k') ≫
                    rawBlockSum.{u, v} i i' (j + k) (j' + k'))) z
      _ = _ := by
        change ((α_ AObj BObj CObj).hom ≫
          (AObj ◁ rawBlockSum.{u, v} j j' k k') ≫
          rawBlockSum.{u, v} i i' (j + k) (j' + k')) zH = _
        rw [ConcreteCategory.comp_apply, hRight]
  change rawComp.{u, v} ((i + j) + k) ((i' + j') + k')
      (i' + (j' + k')) yL =
    rawComp.{u, v} ((i + j) + k) (i + (j + k))
      (i' + (j' + k')) yR
  rw [rawComp_apply, rawComp_apply]
  change ULift.up (OrthogonalMatrixHom.comp
      (ConcreteCategory.hom (CartesianMonoidalCategory.fst
        (rawHomCGWH.{u, v} ((i + j) + k) ((i' + j') + k'))
        (rawHomCGWH.{u, v} ((i' + j') + k') (i' + (j' + k')))) yL).down
      (ConcreteCategory.hom (CartesianMonoidalCategory.snd
        (rawHomCGWH.{u, v} ((i + j) + k) ((i' + j') + k'))
        (rawHomCGWH.{u, v} ((i' + j') + k') (i' + (j' + k')))) yL).down) =
    ULift.up (OrthogonalMatrixHom.comp
      (ConcreteCategory.hom (CartesianMonoidalCategory.fst
        (rawHomCGWH.{u, v} ((i + j) + k) (i + (j + k)))
        (rawHomCGWH.{u, v} (i + (j + k)) (i' + (j' + k')))) yR).down
      (ConcreteCategory.hom (CartesianMonoidalCategory.snd
        (rawHomCGWH.{u, v} ((i + j) + k) (i + (j + k)))
        (rawHomCGWH.{u, v} (i + (j + k)) (i' + (j' + k')))) yR).down)
  rw [hyLf, hyLs, hyRf, hyRs]
  congr 1
  exact coordinateLaws.1
    (finCongr (Nat.add_assoc i' j' k'))
    (finCongr (Nat.add_assoc i j k))
    (OrthogonalMatrixHom.blockSum
      (OrthogonalMatrixHom.blockSum A B) C)
    (OrthogonalMatrixHom.blockSum A
      (OrthogonalMatrixHom.blockSum B C))
    (OrthogonalMatrixHom.blockSum_assoc A B C)

private theorem associator_naturality_law
    (i i' j j' k k' : OrthogonalIndex) :
    letI : Category.{v} OrthogonalIndex := category.{u, v}
    letI : MonoidalCategory OrthogonalIndex := monoidalCategory.{u, v}
    letI : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
      enrichedOrdinaryCategory.{u, v}
    (β_ (𝟙_ PointedCGWH.{u, v})
          (((hom.{u, v} i i' ⊗ hom.{u, v} j j') ⊗
            hom.{u, v} k k'))).hom ≫
          (((tensorMap.{u, v} i i' j j' ▷ hom.{u, v} k k') ≫
              tensorMap.{u, v} (i + j) (i' + j') k k') ⊗ₘ
            eHomEquiv PointedCGWH.{u, v} (α_ i' j' k').hom) ≫
        @eComp PointedCGWH.{u, v} _ _ OrthogonalIndex
          (enrichedCategory.{u, v})
          ((i + j) + k) ((i' + j') + k') (i' + (j' + k')) =
      (eHomEquiv PointedCGWH.{u, v} (α_ i j k).hom ⊗ₘ
          ((α_ (hom.{u, v} i i') (hom.{u, v} j j')
              (hom.{u, v} k k')).hom ≫
            (hom.{u, v} i i' ◁ tensorMap.{u, v} j j' k k') ≫
            tensorMap.{u, v} i i' (j + k) (j' + k'))) ≫
        @eComp PointedCGWH.{u, v} _ _ OrthogonalIndex
          (enrichedCategory.{u, v})
          ((i + j) + k) (i + (j + k)) (i' + (j' + k')) := by
  let _ : Category.{v} OrthogonalIndex := category.{u, v}
  let _ : MonoidalCategory OrthogonalIndex := monoidalCategory.{u, v}
  let _ : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
    enrichedOrdinaryCategory.{u, v}
  let F := Under.costar CGWH.point.{u, v}
  let _ : EnrichedCategory CGWH.{u, v} OrthogonalIndex :=
    rawEnrichedCategory.{u, v}
  let _ : BraidedCategory CGWH.{u, v} :=
    BraidedCategory.ofCartesianMonoidalCategory
  let _ : SymmetricCategory CGWH.{u, v} := inferInstance
  let _ : MonoidalCategory PointedCGWH.{u, v} :=
    CategoryTheory.Pointed.smashMonoidalCategory
      CGWH.point.{u, v} CGWH.point_isTerminal
  let _ : SymmetricCategory PointedCGWH.{u, v} :=
    CategoryTheory.Pointed.smashSymmetricCategory
      CGWH.point.{u, v} CGWH.point_isTerminal
  let core := CategoryTheory.Pointed.costarCoreMonoidal
    CGWH.point.{u, v} CGWH.point_isTerminal
  let _ : F.Monoidal := core.toMonoidal
  let _ : EnrichedCategory PointedCGWH.{u, v} OrthogonalIndex :=
    enrichedCategory.{u, v}
  have eComp_eq (a b c : OrthogonalIndex) :
      @eComp PointedCGWH.{u, v} _ _ OrthogonalIndex
          (enrichedCategory.{u, v}) a b c =
        (core.μIso (rawHomCGWH.{u, v} a b)
            (rawHomCGWH.{u, v} b c)).hom ≫
          F.map (rawComp.{u, v} a b c) := by
    rfl
  have eAssoc_eq (a b c : OrthogonalIndex) :
      eHomEquiv PointedCGWH.{u, v} (α_ a b c).hom =
        matrixPoint.{u, v} (associatorHom a b c) := by
    rfl
  have matrixPoint_eq {a b : OrthogonalIndex}
      (M : OrthogonalMatrixHom a b) :
      matrixPoint.{u, v} M = Functor.LaxMonoidal.ε F ≫
        F.map (rawPointFromUnit.{u, v} M) := by
    exact freePoint_eq_coreUnit_map.{u, v}
      (rawHomCGWH.{u, v} a b) (ULift.up M)
  simp only [tensorMap]
  rw [eComp_eq, eComp_eq, eAssoc_eq, eAssoc_eq]
  rw [matrixPoint_eq (associatorHom i' j' k'),
    matrixPoint_eq (associatorHom i j k)]
  let A := rawHomCGWH.{u, v} i i'
  let B := rawHomCGWH.{u, v} j j'
  let C := rawHomCGWH.{u, v} k k'
  let leftRaw : ((A ⊗ B) ⊗ C) ⟶
      rawHomCGWH.{u, v} ((i + j) + k) ((i' + j') + k') :=
    (rawBlockSum.{u, v} i i' j j' ▷ C) ≫
      rawBlockSum.{u, v} (i + j) (i' + j') k k'
  let rightRaw : (A ⊗ (B ⊗ C)) ⟶
      rawHomCGWH.{u, v} (i + (j + k)) (i' + (j' + k')) :=
    (A ◁ rawBlockSum.{u, v} j j' k k') ≫
      rawBlockSum.{u, v} i i' (j + k) (j' + k')
  let tripleμ : ((F.obj A ⊗ F.obj B) ⊗ F.obj C) ⟶
      F.obj ((A ⊗ B) ⊗ C) :=
    (core.μIso A B).hom ▷ F.obj C ≫
      (core.μIso (A ⊗ B) C).hom
  let leftNative : ((F.obj A ⊗ F.obj B) ⊗ F.obj C) ⟶
      F.obj (rawHomCGWH.{u, v} ((i + j) + k) ((i' + j') + k')) :=
    (((core.μIso A B).hom ≫
        F.map (rawBlockSum.{u, v} i i' j j')) ▷ F.obj C) ≫
      (core.μIso (rawHomCGWH.{u, v} (i + j) (i' + j')) C).hom ≫
      F.map (rawBlockSum.{u, v} (i + j) (i' + j') k k')
  let rightNative : ((F.obj A ⊗ F.obj B) ⊗ F.obj C) ⟶
      F.obj (rawHomCGWH.{u, v} (i + (j + k)) (i' + (j' + k'))) :=
    (α_ (F.obj A) (F.obj B) (F.obj C)).hom ≫
      F.obj A ◁ ((core.μIso B C).hom ≫
        F.map (rawBlockSum.{u, v} j j' k k')) ≫
      (core.μIso A
        (rawHomCGWH.{u, v} (j + k) (j' + k'))).hom ≫
      F.map (rawBlockSum.{u, v} i i' (j + k) (j' + k'))
  have hLeftMap :
      leftNative = tripleμ ≫ F.map leftRaw := by
    dsimp only [leftNative]
    dsimp only [tripleμ, leftRaw]
    rw [comp_whiskerRight_assoc]
    rw [core.μIso_hom_natural_left_assoc]
    simp only [Category.assoc]
    rw [← F.map_comp]
  have hRightMap :
      rightNative = tripleμ ≫ F.map ((α_ A B C).hom ≫ rightRaw) := by
    dsimp only [rightNative]
    dsimp only [tripleμ, rightRaw]
    rw [MonoidalCategory.whiskerLeft_comp_assoc]
    rw [core.μIso_hom_natural_right_assoc]
    rw [← core.associativity_assoc]
    simp only [Category.assoc]
    rw [← F.map_comp, ← F.map_comp]
  change (β_ (𝟙_ PointedCGWH.{u, v})
        ((F.obj A ⊗ F.obj B) ⊗ F.obj C)).hom ≫
      (leftNative ⊗ₘ
        (Functor.LaxMonoidal.ε F ≫
          F.map (rawPointFromUnit.{u, v} (associatorHom i' j' k')))) ≫
      (core.μIso
        (rawHomCGWH.{u, v} ((i + j) + k) ((i' + j') + k'))
        (rawHomCGWH.{u, v} ((i' + j') + k')
          (i' + (j' + k')))).hom ≫
      F.map (rawComp.{u, v} ((i + j) + k) ((i' + j') + k')
        (i' + (j' + k'))) =
    ((Functor.LaxMonoidal.ε F ≫
          F.map (rawPointFromUnit.{u, v} (associatorHom i j k))) ⊗ₘ
        rightNative) ≫
      (core.μIso
        (rawHomCGWH.{u, v} ((i + j) + k) (i + (j + k)))
        (rawHomCGWH.{u, v} (i + (j + k))
          (i' + (j' + k')))).hom ≫
      F.map (rawComp.{u, v} ((i + j) + k) (i + (j + k))
        (i' + (j' + k')))
  rw [hLeftMap, hRightMap]
  let _ : F.LaxBraided := costarLaxBraided.{u, v}
  rw [← tensorHom_comp_tensorHom, ← tensorHom_comp_tensorHom]
  simp only [Category.assoc]
  rw [← BraidedCategory.braiding_naturality_assoc]
  rw [← BraidedCategory.braiding_naturality_assoc]
  change (Functor.LaxMonoidal.ε F ⊗ₘ tripleμ) ≫
      (F.map (rawPointFromUnit.{u, v} (associatorHom i' j' k')) ⊗ₘ
        F.map leftRaw) ≫
      (β_ (F.obj (rawHomCGWH.{u, v} ((i' + j') + k')
          (i' + (j' + k'))))
        (F.obj (rawHomCGWH.{u, v} ((i + j) + k)
          ((i' + j') + k')))).hom ≫
      Functor.LaxMonoidal.μ F
        (rawHomCGWH.{u, v} ((i + j) + k) ((i' + j') + k'))
        (rawHomCGWH.{u, v} ((i' + j') + k') (i' + (j' + k'))) ≫
      F.map (rawComp.{u, v} ((i + j) + k) ((i' + j') + k')
        (i' + (j' + k'))) = _
  rw [← Functor.LaxBraided.braided_assoc]
  rw [Functor.LaxMonoidal.μ_natural_assoc]
  change _ = (Functor.LaxMonoidal.ε F ⊗ₘ tripleμ) ≫
      (F.map (rawPointFromUnit.{u, v} (associatorHom i j k)) ⊗ₘ
        F.map ((α_ A B C).hom ≫ rightRaw)) ≫
      Functor.LaxMonoidal.μ F
        (rawHomCGWH.{u, v} ((i + j) + k) (i + (j + k)))
        (rawHomCGWH.{u, v} (i + (j + k)) (i' + (j' + k'))) ≫
      F.map (rawComp.{u, v} ((i + j) + k) (i + (j + k))
        (i' + (j' + k')))
  rw [Functor.LaxMonoidal.μ_natural_assoc]
  simp only [← F.map_comp]
  have hraw := rawAssociator_naturality_law.{u, v} i i' j j' k k'
  dsimp only at hraw
  rw [← BraidedCategory.braiding_naturality_assoc] at hraw
  rw [hraw]

private theorem leftUnitor_naturality_law
    (i i' : OrthogonalIndex) :
    (β_ (𝟙_ PointedCGWH.{u, v}) (hom.{u, v} i i')).hom ≫
          (((λ_ (hom.{u, v} i i')).inv ≫
                (matrixPoint.{u, v} (OrthogonalMatrixHom.id 0) ⊗ₘ
                  𝟙 (hom.{u, v} i i')) ≫
              tensorMap.{u, v} 0 0 i i') ⊗ₘ
            matrixPoint.{u, v} (leftUnitorHom i')) ≫
        @eComp PointedCGWH.{u, v} _ _ OrthogonalIndex
          (enrichedCategory.{u, v}) (0 + i) (0 + i') i' =
      (matrixPoint.{u, v} (leftUnitorHom i) ⊗ₘ
          𝟙 (hom.{u, v} i i')) ≫
        @eComp PointedCGWH.{u, v} _ _ OrthogonalIndex
          (enrichedCategory.{u, v}) (0 + i) i i' := by
  let F := Under.costar CGWH.point.{u, v}
  let _ : EnrichedCategory CGWH.{u, v} OrthogonalIndex :=
    rawEnrichedCategory.{u, v}
  let _ : BraidedCategory CGWH.{u, v} :=
    BraidedCategory.ofCartesianMonoidalCategory
  let _ : SymmetricCategory CGWH.{u, v} := inferInstance
  let _ : MonoidalCategory PointedCGWH.{u, v} :=
    CategoryTheory.Pointed.smashMonoidalCategory
      CGWH.point.{u, v} CGWH.point_isTerminal
  let _ : SymmetricCategory PointedCGWH.{u, v} :=
    CategoryTheory.Pointed.smashSymmetricCategory
      CGWH.point.{u, v} CGWH.point_isTerminal
  let core := CategoryTheory.Pointed.costarCoreMonoidal
    CGWH.point.{u, v} CGWH.point_isTerminal
  let _ : F.Monoidal := core.toMonoidal
  let _ : F.LaxBraided := costarLaxBraided.{u, v}
  let _ : EnrichedCategory PointedCGWH.{u, v} OrthogonalIndex :=
    enrichedCategory.{u, v}
  let H := rawHomCGWH.{u, v} i i'
  let O := rawHomCGWH.{u, v} 0 0
  let L := rawHomCGWH.{u, v} (0 + i) (0 + i')
  let T := rawHomCGWH.{u, v} (0 + i') i'
  let S := rawHomCGWH.{u, v} (0 + i) i
  let Q := rawHomCGWH.{u, v} (0 + i) i'
  let leftTensorRaw : H ⟶ L :=
    (λ_ H).inv ≫ (rawIdentity.{u, v} 0 ⊗ₘ 𝟙 H) ≫
      rawBlockSum.{u, v} 0 0 i i'
  let aT := rawPointFromUnit.{u, v} (leftUnitorHom i')
  let aS := rawPointFromUnit.{u, v} (leftUnitorHom i)
  have hRawPoint {a b : OrthogonalIndex}
      (D : OrthogonalMatrixHom a b) (x : (𝟙_ CGWH.{u, v} : Type v)) :
      rawPointFromUnit.{u, v} D x = ULift.up D := by
    let R : CGWH.{u, v} := rawHomCGWH.{u, v} a b
    let d : R := ULift.up D
    let pUnit : CGWH.point.{u, v} ≅ 𝟙_ CGWH.{u, v} :=
      CGWH.point_isTerminal.uniqueUpToIso
        CartesianMonoidalCategory.isTerminalTensorUnit
    change (CGWH.pointHomEquiv R).symm d (pUnit.inv x) = d
    exact CGWH.pointHomEquiv_symm_apply_apply R d (pUnit.inv x)
  have hLeftValue (z : H) : leftTensorRaw z =
      ULift.up (OrthogonalMatrixHom.blockSum (OrthogonalMatrixHom.id 0) z.down) := by
    dsimp only [leftTensorRaw]
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
      rawBlockSum_apply]
    let w := ConcreteCategory.hom (λ_ H).inv z
    have hf := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.tensorHom_fst
        (rawIdentity.{u, v} 0) (𝟙 H)) w
    have hs := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.tensorHom_snd
        (rawIdentity.{u, v} 0) (𝟙 H)) w
    simp only [ConcreteCategory.comp_apply, Category.comp_id] at hf hs
    have hws := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.leftUnitor_inv_snd H) z
    have hws' : CartesianMonoidalCategory.snd (𝟙_ CGWH.{u, v}) H w = z := by
      simpa only [w, ConcreteCategory.comp_apply,
        ConcreteCategory.id_apply] using hws
    rw [hf, hs, hws']
    rfl
  have rawLaw :
      (β_ (𝟙_ CGWH.{u, v}) H).hom ≫
            (leftTensorRaw ⊗ₘ aT) ≫
          rawComp.{u, v} (0 + i) (0 + i') i' =
        (aS ⊗ₘ 𝟙 H) ≫ rawComp.{u, v} (0 + i) i i' := by
    apply ConcreteCategory.hom_ext
    intro z
    let zH : H := CartesianMonoidalCategory.snd (𝟙_ CGWH.{u, v}) H z
    rcases hzH : zH with ⟨A⟩
    let preL : (H ⊗ 𝟙_ CGWH.{u, v} : CGWH.{u, v}) :=
      (β_ (𝟙_ CGWH.{u, v}) H).hom z
    let yL : (L ⊗ T : CGWH.{u, v}) := (leftTensorRaw ⊗ₘ aT) preL
    have hpreLf : CartesianMonoidalCategory.fst H (𝟙_ CGWH.{u, v}) preL =
        zH := by
      exact ConcreteCategory.congr_hom
        (CartesianMonoidalCategory.braiding_hom_fst
          (𝟙_ CGWH.{u, v}) H) z
    have hyLf : CartesianMonoidalCategory.fst L T yL =
        ULift.up (OrthogonalMatrixHom.blockSum (OrthogonalMatrixHom.id 0) A) := by
      calc
        _ = leftTensorRaw
            (CartesianMonoidalCategory.fst H (𝟙_ CGWH.{u, v}) preL) := by
              simpa only [ConcreteCategory.comp_apply] using
                ConcreteCategory.congr_hom
                  (CartesianMonoidalCategory.tensorHom_fst leftTensorRaw aT) preL
        _ = _ := by rw [hpreLf, hLeftValue, hzH]
    have hyLs : CartesianMonoidalCategory.snd L T yL =
        ULift.up (leftUnitorHom i') := by
      have hPointValue : CartesianMonoidalCategory.snd L T yL =
          aT (CartesianMonoidalCategory.snd H (𝟙_ CGWH.{u, v}) preL) := by
            simpa only [ConcreteCategory.comp_apply] using
              ConcreteCategory.congr_hom
                (CartesianMonoidalCategory.tensorHom_snd leftTensorRaw aT) preL
      exact hPointValue.trans (hRawPoint _ _)
    let yR : (S ⊗ H : CGWH.{u, v}) := (aS ⊗ₘ 𝟙 H) z
    have hyRf : CartesianMonoidalCategory.fst S H yR =
        ULift.up (leftUnitorHom i) := by
      have hPointValue : CartesianMonoidalCategory.fst S H yR =
          aS (CartesianMonoidalCategory.fst (𝟙_ CGWH.{u, v}) H z) := by
            simpa only [ConcreteCategory.comp_apply] using
              ConcreteCategory.congr_hom
                (CartesianMonoidalCategory.tensorHom_fst aS (𝟙 H)) z
      exact hPointValue.trans (hRawPoint _ _)
    have hyRs : CartesianMonoidalCategory.snd S H yR = ULift.up A := by
      have hPointValue : CartesianMonoidalCategory.snd S H yR = zH := by
        simpa only [ConcreteCategory.comp_apply,
          ConcreteCategory.id_apply] using
          ConcreteCategory.congr_hom
            (CartesianMonoidalCategory.tensorHom_snd aS (𝟙 H)) z
      exact hPointValue.trans hzH
    simp only [ConcreteCategory.comp_apply]
    change ULift.up (OrthogonalMatrixHom.comp
        (CartesianMonoidalCategory.fst L T yL).down
        (CartesianMonoidalCategory.snd L T yL).down) =
      ULift.up (OrthogonalMatrixHom.comp
        (CartesianMonoidalCategory.fst S H yR).down
        (CartesianMonoidalCategory.snd S H yR).down)
    rw [hyLf, hyLs, hyRf, hyRs]
    congr 1
    exact coordinateLaws.1
      (finCongr (Nat.zero_add i')) (finCongr (Nat.zero_add i))
      (OrthogonalMatrixHom.blockSum (OrthogonalMatrixHom.id 0) A) A
      (OrthogonalMatrixHom.blockSum_zero_left A)
  have eComp_eq (a b c : OrthogonalIndex) :
      @eComp PointedCGWH.{u, v} _ _ OrthogonalIndex
          (enrichedCategory.{u, v}) a b c =
        (core.μIso (rawHomCGWH.{u, v} a b)
            (rawHomCGWH.{u, v} b c)).hom ≫
          F.map (rawComp.{u, v} a b c) := by
    rfl
  have matrixPoint_eq {a b : OrthogonalIndex}
      (M : OrthogonalMatrixHom a b) :
      matrixPoint.{u, v} M = Functor.LaxMonoidal.ε F ≫
        F.map (rawPointFromUnit.{u, v} M) := by
    exact freePoint_eq_coreUnit_map.{u, v}
      (rawHomCGWH.{u, v} a b) (ULift.up M)
  have rawIdentityPoint :
      rawPointFromUnit.{u, v} (OrthogonalMatrixHom.id 0) =
        rawIdentity.{u, v} 0 := by
    apply ConcreteCategory.hom_ext
    intro x
    rw [hRawPoint]
    rfl
  have hLT :
      (λ_ (F.obj H)).inv ≫
            ((Functor.LaxMonoidal.ε F ≫ F.map (rawIdentity.{u, v} 0)) ⊗ₘ
              𝟙 (F.obj H)) ≫
          Functor.LaxMonoidal.μ F O H ≫
          F.map (rawBlockSum.{u, v} 0 0 i i') = F.map leftTensorRaw := by
    rw [← F.map_id H]
    rw [← Category.id_comp (F.map (𝟙 H))]
    rw [← tensorHom_comp_tensorHom]
    simp only [Category.assoc]
    rw [Functor.LaxMonoidal.μ_natural_assoc]
    rw [MonoidalCategory.tensorHom_id]
    rw [Functor.LaxMonoidal.left_unitality_inv_assoc]
    simp only [← F.map_comp]
    rfl
  simp only [tensorMap]
  rw [eComp_eq, eComp_eq, matrixPoint_eq, matrixPoint_eq, matrixPoint_eq]
  rw [rawIdentityPoint]
  change (β_ (𝟙_ PointedCGWH.{u, v}) (F.obj H)).hom ≫
        ((((λ_ (F.obj H)).inv ≫
              ((Functor.LaxMonoidal.ε F ≫
                  F.map (rawIdentity.{u, v} 0)) ⊗ₘ 𝟙 (F.obj H)) ≫
              Functor.LaxMonoidal.μ F O H ≫
              F.map (rawBlockSum.{u, v} 0 0 i i')) ⊗ₘ
          (Functor.LaxMonoidal.ε F ≫ F.map aT)) ≫
          Functor.LaxMonoidal.μ F L T ≫
          F.map (rawComp.{u, v} (0 + i) (0 + i') i')) =
      ((Functor.LaxMonoidal.ε F ≫ F.map aS) ⊗ₘ
        𝟙 (F.obj H)) ≫
        Functor.LaxMonoidal.μ F S H ≫
        F.map (rawComp.{u, v} (0 + i) i i')
  rw [hLT]
  rw [← Category.id_comp (F.map leftTensorRaw)]
  nth_rewrite 2 [← F.map_id H]
  rw [← Category.id_comp (F.map (𝟙 H))]
  rw [← tensorHom_comp_tensorHom, ← tensorHom_comp_tensorHom]
  simp only [Category.assoc]
  rw [← BraidedCategory.braiding_naturality_assoc]
  rw [← BraidedCategory.braiding_naturality_assoc]
  rw [← Functor.LaxBraided.braided_assoc]
  rw [Functor.LaxMonoidal.μ_natural_assoc,
    Functor.LaxMonoidal.μ_natural_assoc]
  simp only [← F.map_comp]
  have rawLaw' :
      (aT ⊗ₘ leftTensorRaw) ≫ (β_ T L).hom ≫
          rawComp.{u, v} (0 + i) (0 + i') i' =
        (aS ⊗ₘ 𝟙 H) ≫ rawComp.{u, v} (0 + i) i i' := by
    rw [BraidedCategory.braiding_naturality_assoc]
    exact rawLaw
  rw [rawLaw']

private theorem rightUnitor_naturality_law
    (i i' : OrthogonalIndex) :
    (β_ (𝟙_ PointedCGWH.{u, v}) (hom.{u, v} i i')).hom ≫
          (((ρ_ (hom.{u, v} i i')).inv ≫
                (𝟙 (hom.{u, v} i i') ⊗ₘ
                  matrixPoint.{u, v} (OrthogonalMatrixHom.id 0)) ≫
              tensorMap.{u, v} i i' 0 0) ⊗ₘ
            matrixPoint.{u, v} (rightUnitorHom i')) ≫
        @eComp PointedCGWH.{u, v} _ _ OrthogonalIndex
          (enrichedCategory.{u, v}) (i + 0) (i' + 0) i' =
      (matrixPoint.{u, v} (rightUnitorHom i) ⊗ₘ
          𝟙 (hom.{u, v} i i')) ≫
        @eComp PointedCGWH.{u, v} _ _ OrthogonalIndex
          (enrichedCategory.{u, v}) (i + 0) i i' := by
  let F := Under.costar CGWH.point.{u, v}
  let _ : EnrichedCategory CGWH.{u, v} OrthogonalIndex :=
    rawEnrichedCategory.{u, v}
  let _ : BraidedCategory CGWH.{u, v} :=
    BraidedCategory.ofCartesianMonoidalCategory
  let _ : SymmetricCategory CGWH.{u, v} := inferInstance
  let _ : MonoidalCategory PointedCGWH.{u, v} :=
    CategoryTheory.Pointed.smashMonoidalCategory
      CGWH.point.{u, v} CGWH.point_isTerminal
  let _ : SymmetricCategory PointedCGWH.{u, v} :=
    CategoryTheory.Pointed.smashSymmetricCategory
      CGWH.point.{u, v} CGWH.point_isTerminal
  let core := CategoryTheory.Pointed.costarCoreMonoidal
    CGWH.point.{u, v} CGWH.point_isTerminal
  let _ : F.Monoidal := core.toMonoidal
  let _ : F.LaxBraided := costarLaxBraided.{u, v}
  let _ : EnrichedCategory PointedCGWH.{u, v} OrthogonalIndex :=
    enrichedCategory.{u, v}
  let H := rawHomCGWH.{u, v} i i'
  let O := rawHomCGWH.{u, v} 0 0
  let L := rawHomCGWH.{u, v} (i + 0) (i' + 0)
  let T := rawHomCGWH.{u, v} (i' + 0) i'
  let S := rawHomCGWH.{u, v} (i + 0) i
  let Q := rawHomCGWH.{u, v} (i + 0) i'
  let rightTensorRaw : H ⟶ L :=
    (ρ_ H).inv ≫ (𝟙 H ⊗ₘ rawIdentity.{u, v} 0) ≫
      rawBlockSum.{u, v} i i' 0 0
  let aT := rawPointFromUnit.{u, v} (rightUnitorHom i')
  let aS := rawPointFromUnit.{u, v} (rightUnitorHom i)
  have hRawPoint {a b : OrthogonalIndex}
      (D : OrthogonalMatrixHom a b) (x : (𝟙_ CGWH.{u, v} : Type v)) :
      rawPointFromUnit.{u, v} D x = ULift.up D := by
    let R : CGWH.{u, v} := rawHomCGWH.{u, v} a b
    let d : R := ULift.up D
    let pUnit : CGWH.point.{u, v} ≅ 𝟙_ CGWH.{u, v} :=
      CGWH.point_isTerminal.uniqueUpToIso
        CartesianMonoidalCategory.isTerminalTensorUnit
    change (CGWH.pointHomEquiv R).symm d (pUnit.inv x) = d
    exact CGWH.pointHomEquiv_symm_apply_apply R d (pUnit.inv x)
  have hRightValue (z : H) : rightTensorRaw z =
      ULift.up (OrthogonalMatrixHom.blockSum z.down (OrthogonalMatrixHom.id 0)) := by
    dsimp only [rightTensorRaw]
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
      rawBlockSum_apply]
    let w := ConcreteCategory.hom (ρ_ H).inv z
    have hf := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.tensorHom_fst
        (𝟙 H) (rawIdentity.{u, v} 0)) w
    have hs := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.tensorHom_snd
        (𝟙 H) (rawIdentity.{u, v} 0)) w
    simp only [ConcreteCategory.comp_apply, Category.comp_id] at hf hs
    have hwf := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.rightUnitor_inv_fst H) z
    have hwf' : CartesianMonoidalCategory.fst H (𝟙_ CGWH.{u, v}) w = z := by
      simpa only [w, ConcreteCategory.comp_apply,
        ConcreteCategory.id_apply] using hwf
    rw [hf, hs, hwf']
    rfl
  have rawLaw :
      (β_ (𝟙_ CGWH.{u, v}) H).hom ≫
            (rightTensorRaw ⊗ₘ aT) ≫
          rawComp.{u, v} (i + 0) (i' + 0) i' =
        (aS ⊗ₘ 𝟙 H) ≫ rawComp.{u, v} (i + 0) i i' := by
    apply ConcreteCategory.hom_ext
    intro z
    let zH : H := CartesianMonoidalCategory.snd (𝟙_ CGWH.{u, v}) H z
    rcases hzH : zH with ⟨A⟩
    let preL : (H ⊗ 𝟙_ CGWH.{u, v} : CGWH.{u, v}) :=
      (β_ (𝟙_ CGWH.{u, v}) H).hom z
    let yL : (L ⊗ T : CGWH.{u, v}) := (rightTensorRaw ⊗ₘ aT) preL
    have hpreLf : CartesianMonoidalCategory.fst H (𝟙_ CGWH.{u, v}) preL =
        zH := by
      exact ConcreteCategory.congr_hom
        (CartesianMonoidalCategory.braiding_hom_fst
          (𝟙_ CGWH.{u, v}) H) z
    have hyLf : CartesianMonoidalCategory.fst L T yL =
        ULift.up (OrthogonalMatrixHom.blockSum A (OrthogonalMatrixHom.id 0)) := by
      calc
        _ = rightTensorRaw
            (CartesianMonoidalCategory.fst H (𝟙_ CGWH.{u, v}) preL) := by
              simpa only [ConcreteCategory.comp_apply] using
                ConcreteCategory.congr_hom
                  (CartesianMonoidalCategory.tensorHom_fst rightTensorRaw aT) preL
        _ = _ := by rw [hpreLf, hRightValue, hzH]
    have hyLs : CartesianMonoidalCategory.snd L T yL =
        ULift.up (rightUnitorHom i') := by
      have hPointValue : CartesianMonoidalCategory.snd L T yL =
          aT (CartesianMonoidalCategory.snd H (𝟙_ CGWH.{u, v}) preL) := by
            simpa only [ConcreteCategory.comp_apply] using
              ConcreteCategory.congr_hom
                (CartesianMonoidalCategory.tensorHom_snd rightTensorRaw aT) preL
      exact hPointValue.trans (hRawPoint _ _)
    let yR : (S ⊗ H : CGWH.{u, v}) := (aS ⊗ₘ 𝟙 H) z
    have hyRf : CartesianMonoidalCategory.fst S H yR =
        ULift.up (rightUnitorHom i) := by
      have hPointValue : CartesianMonoidalCategory.fst S H yR =
          aS (CartesianMonoidalCategory.fst (𝟙_ CGWH.{u, v}) H z) := by
            simpa only [ConcreteCategory.comp_apply] using
              ConcreteCategory.congr_hom
                (CartesianMonoidalCategory.tensorHom_fst aS (𝟙 H)) z
      exact hPointValue.trans (hRawPoint _ _)
    have hyRs : CartesianMonoidalCategory.snd S H yR = ULift.up A := by
      have hPointValue : CartesianMonoidalCategory.snd S H yR = zH := by
        simpa only [ConcreteCategory.comp_apply,
          ConcreteCategory.id_apply] using
          ConcreteCategory.congr_hom
            (CartesianMonoidalCategory.tensorHom_snd aS (𝟙 H)) z
      exact hPointValue.trans hzH
    simp only [ConcreteCategory.comp_apply]
    change ULift.up (OrthogonalMatrixHom.comp
        (CartesianMonoidalCategory.fst L T yL).down
        (CartesianMonoidalCategory.snd L T yL).down) =
      ULift.up (OrthogonalMatrixHom.comp
        (CartesianMonoidalCategory.fst S H yR).down
        (CartesianMonoidalCategory.snd S H yR).down)
    rw [hyLf, hyLs, hyRf, hyRs]
    congr 1
    exact coordinateLaws.1
      (finCongr (Nat.add_zero i')) (finCongr (Nat.add_zero i))
      (OrthogonalMatrixHom.blockSum A (OrthogonalMatrixHom.id 0)) A
      (OrthogonalMatrixHom.blockSum_zero_right A)
  have eComp_eq (a b c : OrthogonalIndex) :
      @eComp PointedCGWH.{u, v} _ _ OrthogonalIndex
          (enrichedCategory.{u, v}) a b c =
        (core.μIso (rawHomCGWH.{u, v} a b)
            (rawHomCGWH.{u, v} b c)).hom ≫
          F.map (rawComp.{u, v} a b c) := by
    rfl
  have matrixPoint_eq {a b : OrthogonalIndex}
      (M : OrthogonalMatrixHom a b) :
      matrixPoint.{u, v} M = Functor.LaxMonoidal.ε F ≫
        F.map (rawPointFromUnit.{u, v} M) := by
    exact freePoint_eq_coreUnit_map.{u, v}
      (rawHomCGWH.{u, v} a b) (ULift.up M)
  have rawIdentityPoint :
      rawPointFromUnit.{u, v} (OrthogonalMatrixHom.id 0) =
        rawIdentity.{u, v} 0 := by
    apply ConcreteCategory.hom_ext
    intro x
    rw [hRawPoint]
    rfl
  have hRT :
      (ρ_ (F.obj H)).inv ≫
            (𝟙 (F.obj H) ⊗ₘ
          (Functor.LaxMonoidal.ε F ≫ F.map (rawIdentity.{u, v} 0))) ≫
          Functor.LaxMonoidal.μ F H O ≫
          F.map (rawBlockSum.{u, v} i i' 0 0) = F.map rightTensorRaw := by
    rw [← F.map_id H]
    rw [← Category.id_comp (F.map (𝟙 H))]
    rw [← tensorHom_comp_tensorHom]
    simp only [Category.assoc]
    rw [Functor.LaxMonoidal.μ_natural_assoc]
    rw [MonoidalCategory.id_tensorHom]
    rw [Functor.LaxMonoidal.right_unitality_inv_assoc]
    simp only [← F.map_comp]
    rfl
  simp only [tensorMap]
  rw [eComp_eq, eComp_eq, matrixPoint_eq, matrixPoint_eq, matrixPoint_eq]
  rw [rawIdentityPoint]
  change (β_ (𝟙_ PointedCGWH.{u, v}) (F.obj H)).hom ≫
        ((((ρ_ (F.obj H)).inv ≫
              (𝟙 (F.obj H) ⊗ₘ
              (Functor.LaxMonoidal.ε F ≫
                F.map (rawIdentity.{u, v} 0))) ≫
              Functor.LaxMonoidal.μ F H O ≫
              F.map (rawBlockSum.{u, v} i i' 0 0)) ⊗ₘ
          (Functor.LaxMonoidal.ε F ≫ F.map aT)) ≫
          Functor.LaxMonoidal.μ F L T ≫
          F.map (rawComp.{u, v} (i + 0) (i' + 0) i')) =
      ((Functor.LaxMonoidal.ε F ≫ F.map aS) ⊗ₘ
        𝟙 (F.obj H)) ≫
        Functor.LaxMonoidal.μ F S H ≫
        F.map (rawComp.{u, v} (i + 0) i i')
  rw [hRT]
  rw [← Category.id_comp (F.map rightTensorRaw)]
  nth_rewrite 2 [← F.map_id H]
  rw [← Category.id_comp (F.map (𝟙 H))]
  rw [← tensorHom_comp_tensorHom, ← tensorHom_comp_tensorHom]
  simp only [Category.assoc]
  rw [← BraidedCategory.braiding_naturality_assoc]
  rw [← BraidedCategory.braiding_naturality_assoc]
  rw [← Functor.LaxBraided.braided_assoc]
  rw [Functor.LaxMonoidal.μ_natural_assoc,
    Functor.LaxMonoidal.μ_natural_assoc]
  simp only [← F.map_comp]
  have rawLaw' :
      (aT ⊗ₘ rightTensorRaw) ≫ (β_ T L).hom ≫
          rawComp.{u, v} (i + 0) (i' + 0) i' =
        (aS ⊗ₘ 𝟙 H) ≫ rawComp.{u, v} (i + 0) i i' := by
    rw [BraidedCategory.braiding_naturality_assoc]
    exact rawLaw
  rw [rawLaw']

/-- The selected direct-sum tensor as enriched monoidal data. -/
noncomputable def enrichedMonoidalData :
    letI : Category.{v} OrthogonalIndex := category.{u, v}
    letI : MonoidalCategory OrthogonalIndex := monoidalCategory.{u, v}
    letI : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
      enrichedOrdinaryCategory.{u, v}
    EnrichedMonoidalCategoryData PointedCGWH.{u, v} OrthogonalIndex := by
  let _ : Category.{v} OrthogonalIndex := category.{u, v}
  let _ : MonoidalCategory OrthogonalIndex := monoidalCategory.{u, v}
  let _ : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
    enrichedOrdinaryCategory.{u, v}
  let _ : EnrichedCategory PointedCGWH.{u, v}
      (OrthogonalIndex × OrthogonalIndex) :=
    Enriched.prodCategory PointedCGWH.{u, v} OrthogonalIndex OrthogonalIndex
  have rawBlockSum_id (m n : OrthogonalIndex) :
      OrthogonalMatrixHom.blockSum (OrthogonalMatrixHom.id m)
        (OrthogonalMatrixHom.id n) = OrthogonalMatrixHom.id (m + n) := by
    apply OrthogonalMatrixHom.ext
    simp [OrthogonalMatrixHom.blockSum, OrthogonalMatrixHom.id]
  have selectedTensor_eHomEquiv
      {m m' n n' : OrthogonalIndex} (f : m ⟶ m') (g : n ⟶ n') :
      (λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫
            (eHomEquiv PointedCGWH.{u, v} f ⊗ₘ
              eHomEquiv PointedCGWH.{u, v} g) ≫
          tensorMap.{u, v} m m' n n' =
        eHomEquiv PointedCGWH.{u, v} (f ⊗ₘ g) := by
    rfl
  have tensorMap_id_law (m n : OrthogonalIndex) :
      (Enriched.prodCategory PointedCGWH.{u, v}
          OrthogonalIndex OrthogonalIndex).id (m, n) ≫
        tensorMap.{u, v} m m n n =
          eId PointedCGWH.{u, v} (m + n) := by
    change (λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫
          (eId PointedCGWH.{u, v} m ⊗ₘ eId PointedCGWH.{u, v} n) ≫
        tensorMap.{u, v} m m n n = eId PointedCGWH.{u, v} (m + n)
    rw [enrichedCategory_id, enrichedCategory_id,
      enrichedCategory_id]
    change (λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫
      (matrixPoint.{u, v} (OrthogonalMatrixHom.id m) ⊗ₘ
        matrixPoint.{u, v} (OrthogonalMatrixHom.id n)) ≫ tensorMap.{u, v} m m n n =
      matrixPoint.{u, v} (OrthogonalMatrixHom.id (m + n))
    exact (tensorMap_blockSum.{u, v}
      (OrthogonalMatrixHom.id m) (OrthogonalMatrixHom.id n)).1.trans
      (congrArg matrixPoint.{u, v} (rawBlockSum_id m n))
  have tensorMap_comp_law
      (i i' i'' j j' j'' : OrthogonalIndex) :
      (Enriched.prodCategory PointedCGWH.{u, v}
            OrthogonalIndex OrthogonalIndex).comp
            (i, j) (i', j') (i'', j'') ≫
          tensorMap.{u, v} i i'' j j'' =
        (tensorMap.{u, v} i i' j j' ⊗ₘ
            tensorMap.{u, v} i' i'' j' j'') ≫
          @eComp PointedCGWH.{u, v} _ _ OrthogonalIndex
            (enrichedCategory.{u, v})
            (i + j) (i' + j') (i'' + j'') := by
    exact (by
      let F := Under.costar CGWH.point.{u, v}
      let _ : EnrichedCategory CGWH.{u, v} OrthogonalIndex :=
        rawEnrichedCategory.{u, v}
      let _ : BraidedCategory CGWH.{u, v} :=
        BraidedCategory.ofCartesianMonoidalCategory
      let _ : SymmetricCategory CGWH.{u, v} := inferInstance
      let _ : MonoidalCategory PointedCGWH.{u, v} :=
        CategoryTheory.Pointed.smashMonoidalCategory
          CGWH.point.{u, v} CGWH.point_isTerminal
      let _ : SymmetricCategory PointedCGWH.{u, v} :=
        CategoryTheory.Pointed.smashSymmetricCategory
          CGWH.point.{u, v} CGWH.point_isTerminal
      let core := CategoryTheory.Pointed.costarCoreMonoidal
        CGWH.point.{u, v} CGWH.point_isTerminal
      let _ : F.Monoidal := core.toMonoidal
      let _ : F.LaxBraided := costarLaxBraided.{u, v}
      let _ : EnrichedCategory CGWH.{u, v}
          (OrthogonalIndex × OrthogonalIndex) :=
        Enriched.prodCategory CGWH.{u, v} OrthogonalIndex OrthogonalIndex
      let _ : EnrichedCategory PointedCGWH.{u, v} OrthogonalIndex :=
        enrichedCategory.{u, v}
      let _ : EnrichedCategory PointedCGWH.{u, v}
          (OrthogonalIndex × OrthogonalIndex) :=
        Enriched.prodCategory PointedCGWH.{u, v} OrthogonalIndex OrthogonalIndex
      have rawMapComp (X Y Z : OrthogonalIndex × OrthogonalIndex) :
          (Enriched.prodCategory CGWH.{u, v}
                OrthogonalIndex OrthogonalIndex).comp X Y Z ≫
              rawBlockSum.{u, v} X.1 Z.1 X.2 Z.2 =
            (rawBlockSum.{u, v} X.1 Y.1 X.2 Y.2 ⊗ₘ
                rawBlockSum.{u, v} Y.1 Z.1 Y.2 Z.2) ≫
              rawComp.{u, v} (X.1 + X.2) (Y.1 + Y.2) (Z.1 + Z.2) := by
        change MonoidalCategory.tensorμ
              (rawHomCGWH.{u, v} X.1 Y.1)
              (rawHomCGWH.{u, v} X.2 Y.2)
              (rawHomCGWH.{u, v} Y.1 Z.1)
              (rawHomCGWH.{u, v} Y.2 Z.2) ≫
            (rawComp.{u, v} X.1 Y.1 Z.1 ⊗ₘ
              rawComp.{u, v} X.2 Y.2 Z.2) ≫
            rawBlockSum.{u, v} X.1 Z.1 X.2 Z.2 =
          (rawBlockSum.{u, v} X.1 Y.1 X.2 Y.2 ⊗ₘ
              rawBlockSum.{u, v} Y.1 Z.1 Y.2 Z.2) ≫
            rawComp.{u, v} (X.1 + X.2) (Y.1 + Y.2) (Z.1 + Z.2)
        apply ConcreteCategory.hom_ext
        intro z
        simp only [ConcreteCategory.comp_apply, rawBlockSum_apply,
          rawComp_apply]
        have hLf :
            MonoidalCategory.tensorμ
                  (rawHomCGWH.{u, v} X.1 Y.1)
                  (rawHomCGWH.{u, v} X.2 Y.2)
                  (rawHomCGWH.{u, v} Y.1 Z.1)
                  (rawHomCGWH.{u, v} Y.2 Z.2) ≫
                (rawComp.{u, v} X.1 Y.1 Z.1 ⊗ₘ
                  rawComp.{u, v} X.2 Y.2 Z.2) ≫
                CartesianMonoidalCategory.fst
                  (rawHomCGWH.{u, v} X.1 Z.1)
                  (rawHomCGWH.{u, v} X.2 Z.2) =
              (CartesianMonoidalCategory.fst
                  (rawHomCGWH.{u, v} X.1 Y.1)
                  (rawHomCGWH.{u, v} X.2 Y.2) ⊗ₘ
                CartesianMonoidalCategory.fst
                  (rawHomCGWH.{u, v} Y.1 Z.1)
                  (rawHomCGWH.{u, v} Y.2 Z.2)) ≫
                rawComp.{u, v} X.1 Y.1 Z.1 := by
          slice_lhs 2 3 =>
            rw [CartesianMonoidalCategory.tensorHom_fst]
          slice_lhs 1 2 =>
            rw [CartesianMonoidalCategory.tensorμ_fst]
        have hLs :
            MonoidalCategory.tensorμ
                  (rawHomCGWH.{u, v} X.1 Y.1)
                  (rawHomCGWH.{u, v} X.2 Y.2)
                  (rawHomCGWH.{u, v} Y.1 Z.1)
                  (rawHomCGWH.{u, v} Y.2 Z.2) ≫
                (rawComp.{u, v} X.1 Y.1 Z.1 ⊗ₘ
                  rawComp.{u, v} X.2 Y.2 Z.2) ≫
                CartesianMonoidalCategory.snd
                  (rawHomCGWH.{u, v} X.1 Z.1)
                  (rawHomCGWH.{u, v} X.2 Z.2) =
              (CartesianMonoidalCategory.snd
                  (rawHomCGWH.{u, v} X.1 Y.1)
                  (rawHomCGWH.{u, v} X.2 Y.2) ⊗ₘ
                CartesianMonoidalCategory.snd
                  (rawHomCGWH.{u, v} Y.1 Z.1)
                  (rawHomCGWH.{u, v} Y.2 Z.2)) ≫
                rawComp.{u, v} X.2 Y.2 Z.2 := by
          slice_lhs 2 3 =>
            rw [CartesianMonoidalCategory.tensorHom_snd]
          slice_lhs 1 2 =>
            rw [CartesianMonoidalCategory.tensorμ_snd]
        have hRf := CartesianMonoidalCategory.tensorHom_fst
          (rawBlockSum.{u, v} X.1 Y.1 X.2 Y.2)
          (rawBlockSum.{u, v} Y.1 Z.1 Y.2 Z.2)
        have hRs := CartesianMonoidalCategory.tensorHom_snd
          (rawBlockSum.{u, v} X.1 Y.1 X.2 Y.2)
          (rawBlockSum.{u, v} Y.1 Z.1 Y.2 Z.2)
        have hLfApp := ConcreteCategory.congr_hom hLf z
        have hLsApp := ConcreteCategory.congr_hom hLs z
        have hRfApp := ConcreteCategory.congr_hom hRf z
        have hRsApp := ConcreteCategory.congr_hom hRs z
        simp only [ConcreteCategory.comp_apply] at hLfApp hLsApp hRfApp hRsApp
        rw [hLfApp, hLsApp, hRfApp, hRsApp]
        simp only [rawComp_apply, rawBlockSum_apply]
        have hA := ConcreteCategory.congr_hom
          (CartesianMonoidalCategory.tensorHom_fst
            (CartesianMonoidalCategory.fst
              (rawHomCGWH.{u, v} X.1 Y.1)
              (rawHomCGWH.{u, v} X.2 Y.2))
            (CartesianMonoidalCategory.fst
              (rawHomCGWH.{u, v} Y.1 Z.1)
              (rawHomCGWH.{u, v} Y.2 Z.2))) z
        have hA' := ConcreteCategory.congr_hom
          (CartesianMonoidalCategory.tensorHom_snd
            (CartesianMonoidalCategory.fst
              (rawHomCGWH.{u, v} X.1 Y.1)
              (rawHomCGWH.{u, v} X.2 Y.2))
            (CartesianMonoidalCategory.fst
              (rawHomCGWH.{u, v} Y.1 Z.1)
              (rawHomCGWH.{u, v} Y.2 Z.2))) z
        have hB := ConcreteCategory.congr_hom
          (CartesianMonoidalCategory.tensorHom_fst
            (CartesianMonoidalCategory.snd
              (rawHomCGWH.{u, v} X.1 Y.1)
              (rawHomCGWH.{u, v} X.2 Y.2))
            (CartesianMonoidalCategory.snd
              (rawHomCGWH.{u, v} Y.1 Z.1)
              (rawHomCGWH.{u, v} Y.2 Z.2))) z
        have hB' := ConcreteCategory.congr_hom
          (CartesianMonoidalCategory.tensorHom_snd
            (CartesianMonoidalCategory.snd
              (rawHomCGWH.{u, v} X.1 Y.1)
              (rawHomCGWH.{u, v} X.2 Y.2))
            (CartesianMonoidalCategory.snd
              (rawHomCGWH.{u, v} Y.1 Z.1)
              (rawHomCGWH.{u, v} Y.2 Z.2))) z
        simp only [ConcreteCategory.comp_apply] at hA hA' hB hB'
        rw [hA, hA', hB, hB']
        congr 1
        exact OrthogonalMatrixHom.blockSum_comp _ _ _ _
      have eComp_eq (a b c : OrthogonalIndex) :
          @eComp PointedCGWH.{u, v} _ _ OrthogonalIndex
              (enrichedCategory.{u, v}) a b c =
            (core.μIso (rawHomCGWH.{u, v} a b)
                (rawHomCGWH.{u, v} b c)).hom ≫
              F.map (rawComp.{u, v} a b c) := by
        rfl
      simp only [Enriched.prodEComp, tensorMap]
      rw [eComp_eq, eComp_eq, eComp_eq]
      change MonoidalCategory.tensorμ
              (F.obj (rawHomCGWH.{u, v} i i'))
              (F.obj (rawHomCGWH.{u, v} j j'))
              (F.obj (rawHomCGWH.{u, v} i' i''))
              (F.obj (rawHomCGWH.{u, v} j' j'')) ≫
            ((Functor.LaxMonoidal.μ F
                  (rawHomCGWH.{u, v} i i')
                  (rawHomCGWH.{u, v} i' i'') ≫
                F.map (rawComp.{u, v} i i' i'')) ⊗ₘ
              (Functor.LaxMonoidal.μ F
                  (rawHomCGWH.{u, v} j j')
                  (rawHomCGWH.{u, v} j' j'') ≫
                F.map (rawComp.{u, v} j j' j''))) ≫
            Functor.LaxMonoidal.μ F
              (rawHomCGWH.{u, v} i i'')
              (rawHomCGWH.{u, v} j j'') ≫
            F.map (rawBlockSum.{u, v} i i'' j j'') =
          ((Functor.LaxMonoidal.μ F
                (rawHomCGWH.{u, v} i i')
                (rawHomCGWH.{u, v} j j') ≫
              F.map (rawBlockSum.{u, v} i i' j j')) ⊗ₘ
            (Functor.LaxMonoidal.μ F
                (rawHomCGWH.{u, v} i' i'')
                (rawHomCGWH.{u, v} j' j'') ≫
              F.map (rawBlockSum.{u, v} i' i'' j' j''))) ≫
            Functor.LaxMonoidal.μ F
              (rawHomCGWH.{u, v} (i + j) (i' + j'))
              (rawHomCGWH.{u, v} (i' + j') (i'' + j'')) ≫
            F.map (rawComp.{u, v}
              (i + j) (i' + j') (i'' + j''))
      rw [← tensorHom_comp_tensorHom, ← tensorHom_comp_tensorHom]
      simp only [Category.assoc]
      rw [Functor.LaxMonoidal.μ_natural_assoc,
        Functor.LaxMonoidal.μ_natural_assoc]
      rw [MonoidalCategory.tensorμ_comp_μ_tensorHom_μ_comp_μ_assoc]
      simp only [← F.map_comp]
      have hraw := rawMapComp (i, j) (i', j') (i'', j'')
      change MonoidalCategory.tensorμ
            (rawHomCGWH.{u, v} i i') (rawHomCGWH.{u, v} j j')
            (rawHomCGWH.{u, v} i' i'') (rawHomCGWH.{u, v} j' j'') ≫
          (rawComp.{u, v} i i' i'' ⊗ₘ rawComp.{u, v} j j' j'') ≫
          rawBlockSum.{u, v} i i'' j j'' =
        (rawBlockSum.{u, v} i i' j j' ⊗ₘ
          rawBlockSum.{u, v} i' i'' j' j'') ≫
          rawComp.{u, v} (i + j) (i' + j') (i'' + j'') at hraw
      rw [hraw]
    )
  let tensorEnrichedFunctor :
      EnrichedFunctor PointedCGWH.{u, v}
        (OrthogonalIndex × OrthogonalIndex) OrthogonalIndex :=
    { obj := fun X ↦ X.1 + X.2
      map := fun X Y ↦ tensorMap.{u, v} X.1 Y.1 X.2 Y.2
      map_id := fun X ↦ tensorMap_id_law X.1 X.2
      map_comp := fun X Y Z ↦
        tensorMap_comp_law X.1 Y.1 Z.1 X.2 Y.2 Z.2 }
  refine
    { tensorMap := tensorMap.{u, v}
      tensorMap_comp := ?_
      tensorMap_eHomEquiv := ?_
      associatorNaturality := ?_
      leftUnitorNaturality := ?_
      rightUnitorNaturality := ?_ }
  · intro i i' i'' j j' j''
    exact tensorEnrichedFunctor.map_comp
      (i, j) (i', j') (i'', j'')
  · intro i i' j j' f g
    exact selectedTensor_eHomEquiv f g
  · intro i i' j j' k k'
    exact (by exact associator_naturality_law.{u, v} i i' j j' k k')
  · intro i i'
    rw [enrichedCategory_id]
    exact (by exact leftUnitor_naturality_law.{u, v} i i')
  · intro i i'
    rw [enrichedCategory_id]
    exact (by exact rightUnitor_naturality_law.{u, v} i i')

private theorem braiding_naturality_law
    (i i' j j' : OrthogonalIndex) :
    (β_ (𝟙_ PointedCGWH.{u, v})
        (hom.{u, v} i i' ⊗ hom.{u, v} j j')).hom ≫
          (tensorMap.{u, v} i i' j j' ⊗ₘ
            matrixPoint.{u, v} (blockSwap i' j')) ≫
        @eComp PointedCGWH.{u, v} _ _ OrthogonalIndex
          (enrichedCategory.{u, v})
          (i + j) (i' + j') (j' + i') =
      (matrixPoint.{u, v} (blockSwap i j) ⊗ₘ
          ((β_ (hom.{u, v} i i') (hom.{u, v} j j')).hom ≫
            tensorMap.{u, v} j j' i i')) ≫
        @eComp PointedCGWH.{u, v} _ _ OrthogonalIndex
          (enrichedCategory.{u, v})
          (i + j) (j + i) (j' + i') := by
  let F := Under.costar CGWH.point.{u, v}
  let _ : EnrichedCategory CGWH.{u, v} OrthogonalIndex :=
    rawEnrichedCategory.{u, v}
  let _ : BraidedCategory CGWH.{u, v} :=
    BraidedCategory.ofCartesianMonoidalCategory
  let _ : SymmetricCategory CGWH.{u, v} := inferInstance
  let _ : MonoidalCategory PointedCGWH.{u, v} :=
    CategoryTheory.Pointed.smashMonoidalCategory
      CGWH.point.{u, v} CGWH.point_isTerminal
  let _ : SymmetricCategory PointedCGWH.{u, v} :=
    CategoryTheory.Pointed.smashSymmetricCategory
      CGWH.point.{u, v} CGWH.point_isTerminal
  let core := CategoryTheory.Pointed.costarCoreMonoidal
    CGWH.point.{u, v} CGWH.point_isTerminal
  let _ : F.Monoidal := core.toMonoidal
  let _ : F.LaxBraided := costarLaxBraided.{u, v}
  let _ : EnrichedCategory PointedCGWH.{u, v} OrthogonalIndex :=
    enrichedCategory.{u, v}
  let A := rawHomCGWH.{u, v} i i'
  let B := rawHomCGWH.{u, v} j j'
  let H := A ⊗ B
  let L := rawHomCGWH.{u, v} (i + j) (i' + j')
  let T := rawHomCGWH.{u, v} (i' + j') (j' + i')
  let S := rawHomCGWH.{u, v} (i + j) (j + i)
  let R := rawHomCGWH.{u, v} (j + i) (j' + i')
  let Q := rawHomCGWH.{u, v} (i + j) (j' + i')
  let tAB : H ⟶ L := rawBlockSum.{u, v} i i' j j'
  let tBA : B ⊗ A ⟶ R := rawBlockSum.{u, v} j j' i i'
  let r : H ⟶ R := (β_ A B).hom ≫ tBA
  let aT := rawPointFromUnit.{u, v} (blockSwap i' j')
  let aS := rawPointFromUnit.{u, v} (blockSwap i j)
  have hRawPoint {a b : OrthogonalIndex}
      (D : OrthogonalMatrixHom a b) (x : (𝟙_ CGWH.{u, v} : Type v)) :
      rawPointFromUnit.{u, v} D x = ULift.up D := by
    let R : CGWH.{u, v} := rawHomCGWH.{u, v} a b
    let d : R := ULift.up D
    let pUnit : CGWH.point.{u, v} ≅ 𝟙_ CGWH.{u, v} :=
      CGWH.point_isTerminal.uniqueUpToIso
        CartesianMonoidalCategory.isTerminalTensorUnit
    change (CGWH.pointHomEquiv R).symm d (pUnit.inv x) = d
    exact CGWH.pointHomEquiv_symm_apply_apply R d (pUnit.inv x)
  have hRValue (z : H) : r z =
      ULift.up (OrthogonalMatrixHom.blockSum
        (CartesianMonoidalCategory.snd A B z).down
        (CartesianMonoidalCategory.fst A B z).down) := by
    dsimp only [r, tBA]
    rw [ConcreteCategory.comp_apply, rawBlockSum_apply]
    have hf := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.braiding_hom_fst A B) z
    have hs := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.braiding_hom_snd A B) z
    simp only [ConcreteCategory.comp_apply] at hf hs
    rw [hf, hs]
  have rawLaw :
      (β_ (𝟙_ CGWH.{u, v}) H).hom ≫
            (tAB ⊗ₘ aT) ≫
          rawComp.{u, v} (i + j) (i' + j') (j' + i') =
        (aS ⊗ₘ r) ≫
          rawComp.{u, v} (i + j) (j + i) (j' + i') := by
    apply ConcreteCategory.hom_ext
    intro z
    let zH : H := CartesianMonoidalCategory.snd (𝟙_ CGWH.{u, v}) H z
    let zA : A := CartesianMonoidalCategory.fst A B zH
    let zB : B := CartesianMonoidalCategory.snd A B zH
    rcases hzA : zA with ⟨X⟩
    rcases hzB : zB with ⟨Y⟩
    let preL : (H ⊗ 𝟙_ CGWH.{u, v} : CGWH.{u, v}) :=
      (β_ (𝟙_ CGWH.{u, v}) H).hom z
    let yL : (L ⊗ T : CGWH.{u, v}) := (tAB ⊗ₘ aT) preL
    have hpreLf : CartesianMonoidalCategory.fst H (𝟙_ CGWH.{u, v}) preL =
        zH := by
      exact ConcreteCategory.congr_hom
        (CartesianMonoidalCategory.braiding_hom_fst
          (𝟙_ CGWH.{u, v}) H) z
    have hyLf : CartesianMonoidalCategory.fst L T yL =
        ULift.up (OrthogonalMatrixHom.blockSum X Y) := by
      calc
        _ = tAB
            (CartesianMonoidalCategory.fst H (𝟙_ CGWH.{u, v}) preL) := by
              simpa only [ConcreteCategory.comp_apply] using
                ConcreteCategory.congr_hom
                  (CartesianMonoidalCategory.tensorHom_fst tAB aT) preL
        _ = tAB zH := by rw [hpreLf]
        _ = _ := by
          dsimp only [tAB]
          rw [rawBlockSum_apply]
          change ULift.up (OrthogonalMatrixHom.blockSum zA.down zB.down) = _
          rw [hzA, hzB]
    have hyLs : CartesianMonoidalCategory.snd L T yL =
        ULift.up (blockSwap i' j') := by
      have hPointValue : CartesianMonoidalCategory.snd L T yL =
          aT (CartesianMonoidalCategory.snd H (𝟙_ CGWH.{u, v}) preL) := by
            simpa only [ConcreteCategory.comp_apply] using
              ConcreteCategory.congr_hom
                (CartesianMonoidalCategory.tensorHom_snd tAB aT) preL
      exact hPointValue.trans (hRawPoint _ _)
    let yR : (S ⊗ R : CGWH.{u, v}) := (aS ⊗ₘ r) z
    have hyRf : CartesianMonoidalCategory.fst S R yR =
        ULift.up (blockSwap i j) := by
      have hPointValue : CartesianMonoidalCategory.fst S R yR = aS
            (CartesianMonoidalCategory.fst (𝟙_ CGWH.{u, v}) H z) := by
            simpa only [ConcreteCategory.comp_apply] using
              ConcreteCategory.congr_hom
                (CartesianMonoidalCategory.tensorHom_fst aS r) z
      exact hPointValue.trans (hRawPoint _ _)
    have hyRs : CartesianMonoidalCategory.snd S R yR =
        ULift.up (OrthogonalMatrixHom.blockSum Y X) := by
      have hPointValue : CartesianMonoidalCategory.snd S R yR = r zH := by
        simpa only [ConcreteCategory.comp_apply] using
          ConcreteCategory.congr_hom (CartesianMonoidalCategory.tensorHom_snd aS r) z
      have hMatrixValue : r zH = ULift.up (OrthogonalMatrixHom.blockSum Y X) := by
        rw [hRValue]
        change ULift.up (OrthogonalMatrixHom.blockSum zB.down zA.down) = _
        rw [hzA, hzB]
      exact hPointValue.trans hMatrixValue
    simp only [ConcreteCategory.comp_apply]
    change ULift.up (OrthogonalMatrixHom.comp
        (CartesianMonoidalCategory.fst L T yL).down
        (CartesianMonoidalCategory.snd L T yL).down) =
      ULift.up (OrthogonalMatrixHom.comp
        (CartesianMonoidalCategory.fst S R yR).down
        (CartesianMonoidalCategory.snd S R yR).down)
    rw [hyLf, hyLs, hyRf, hyRs]
    congr 1
    exact coordinateLaws.1
      (finAddFlip : Fin (i' + j') ≃ Fin (j' + i'))
      (finAddFlip : Fin (i + j) ≃ Fin (j + i))
      (OrthogonalMatrixHom.blockSum X Y)
      (OrthogonalMatrixHom.blockSum Y X)
      (OrthogonalMatrixHom.blockSum_swap X Y)
  have eComp_eq (a b c : OrthogonalIndex) :
      @eComp PointedCGWH.{u, v} _ _ OrthogonalIndex
          (enrichedCategory.{u, v}) a b c =
        (core.μIso (rawHomCGWH.{u, v} a b)
            (rawHomCGWH.{u, v} b c)).hom ≫
          F.map (rawComp.{u, v} a b c) := by
    rfl
  have matrixPoint_eq {a b : OrthogonalIndex}
      (M : OrthogonalMatrixHom a b) :
      matrixPoint.{u, v} M = Functor.LaxMonoidal.ε F ≫
        F.map (rawPointFromUnit.{u, v} M) := by
    exact freePoint_eq_coreUnit_map.{u, v}
      (rawHomCGWH.{u, v} a b) (ULift.up M)
  have hBRT :
      (β_ (F.obj A) (F.obj B)).hom ≫
            Functor.LaxMonoidal.μ F B A ≫
          F.map tBA =
        Functor.LaxMonoidal.μ F A B ≫ F.map r := by
    rw [← Functor.LaxBraided.braided_assoc]
    simp only [← F.map_comp]
    rfl
  simp only [tensorMap]
  rw [eComp_eq, eComp_eq, matrixPoint_eq, matrixPoint_eq]
  change (β_ (𝟙_ PointedCGWH.{u, v})
          (F.obj A ⊗ F.obj B)).hom ≫
        ((Functor.LaxMonoidal.μ F A B ≫ F.map tAB) ⊗ₘ
          (Functor.LaxMonoidal.ε F ≫ F.map aT)) ≫
        Functor.LaxMonoidal.μ F L T ≫
        F.map (rawComp.{u, v} (i + j) (i' + j') (j' + i')) =
      ((Functor.LaxMonoidal.ε F ≫ F.map aS) ⊗ₘ
        ((β_ (F.obj A) (F.obj B)).hom ≫
          Functor.LaxMonoidal.μ F B A ≫ F.map tBA)) ≫
        Functor.LaxMonoidal.μ F S R ≫
        F.map (rawComp.{u, v} (i + j) (j + i) (j' + i'))
  rw [hBRT]
  rw [← tensorHom_comp_tensorHom, ← tensorHom_comp_tensorHom]
  simp only [Category.assoc]
  rw [← BraidedCategory.braiding_naturality_assoc]
  rw [← BraidedCategory.braiding_naturality_assoc]
  rw [← Functor.LaxBraided.braided_assoc]
  rw [Functor.LaxMonoidal.μ_natural_assoc,
    Functor.LaxMonoidal.μ_natural_assoc]
  simp only [← F.map_comp]
  have rawLaw' :
      (aT ⊗ₘ tAB) ≫ (β_ T L).hom ≫
          rawComp.{u, v} (i + j) (i' + j') (j' + i') =
        (aS ⊗ₘ r) ≫
          rawComp.{u, v} (i + j) (j + i) (j' + i') := by
    rw [BraidedCategory.braiding_naturality_assoc]
    exact rawLaw
  rw [rawLaw']

/-- The selected block-swap braiding as enriched symmetric monoidal data. -/
theorem enrichedSymmetricData :
    letI : Category.{v} OrthogonalIndex := category.{u, v}
    letI : MonoidalCategory OrthogonalIndex := monoidalCategory.{u, v}
    letI : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
      enrichedOrdinaryCategory.{u, v}
    letI : SymmetricCategory OrthogonalIndex := symmetricCategory.{u, v}
    EnrichedSymmetricMonoidalCategoryData
      PointedCGWH.{u, v} OrthogonalIndex
      (enrichedMonoidalData.{u, v}) := by
  let _ : Category.{v} OrthogonalIndex := category.{u, v}
  let _ : MonoidalCategory OrthogonalIndex := monoidalCategory.{u, v}
  let _ : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
    enrichedOrdinaryCategory.{u, v}
  let _ : SymmetricCategory OrthogonalIndex := symmetricCategory.{u, v}
  refine { braidingNaturality := ?_ }
  intro i i' j j'
  exact braiding_naturality_law.{u, v} i i' j j'


/-!
Public zero and matrix-point interfaces for the selected native index.
-/

/-- Every unit point of a native hom object is its basepoint or a matrix point. -/
theorem homPoint_cases {m n : OrthogonalIndex}
    (f : 𝟙_ PointedCGWH.{u, v} ⟶ hom.{u, v} m n) :
    f = 0 ∨ ∃ A : OrthogonalMatrixHom m n, f = matrixPoint.{u, v} A := by
  rcases freePoint_cases.{u, v} (rawHomCGWH.{u, v} m n) f with h | ⟨z, h⟩
  · exact Or.inl h
  · change ULift.{v, 0} (OrthogonalMatrixHom m n) at z
    rcases z with ⟨A⟩
    exact Or.inr ⟨A, h⟩

/-- The actual matrix-to-unit-point map is injective. -/
theorem matrixPoint_injective {m n : OrthogonalIndex} :
    Function.Injective (matrixPoint.{u, v} (m := m) (n := n)) := by
  intro A B h
  let Z : CGWH.{u, v} := rawHomCGWH.{u, v} m n
  let pA : CGWH.point.{u, v} ⟶ Z :=
    (CGWH.pointHomEquiv Z).symm (ULift.up A)
  let pB : CGWH.point.{u, v} ⟶ Z :=
    (CGWH.pointHomEquiv Z).symm (ULift.up B)
  have hmap : coprod.map (𝟙 CGWH.point.{u, v}) pA =
      coprod.map (𝟙 CGWH.point.{u, v}) pB :=
    congrArg Under.Hom.right h
  have hpre : pA ≫ (coprod.inr : Z ⟶ CGWH.point.{u, v} ⨿ Z) =
      pB ≫ (coprod.inr : Z ⟶ CGWH.point.{u, v} ⨿ Z) := by
    calc
      _ = (coprod.inr : CGWH.point.{u, v} ⟶
          CGWH.point.{u, v} ⨿ CGWH.point.{u, v}) ≫
            coprod.map (𝟙 CGWH.point.{u, v}) pA := (coprod.inr_map _ _).symm
      _ = (coprod.inr : CGWH.point.{u, v} ⟶
          CGWH.point.{u, v} ⨿ CGWH.point.{u, v}) ≫
            coprod.map (𝟙 CGWH.point.{u, v}) pB := congrArg (fun f =>
              (coprod.inr : CGWH.point.{u, v} ⟶
                CGWH.point.{u, v} ⨿ CGWH.point.{u, v}) ≫ f) hmap
      _ = _ := coprod.inr_map _ _
  have hp : pA = pB := by
    have ht := congrArg (fun f => f ≫ coprod.desc pA (𝟙 Z)) hpre
    simpa only [Category.assoc, coprod.inr_desc, Category.comp_id] using ht
  have hz : (ULift.up A : ULift.{v, 0} (OrthogonalMatrixHom m n)) =
      ULift.up B := by
    let t : CGWH.point.{u, v} := PUnit.unit
    have ht : pA t = pB t := ConcreteCategory.congr_hom hp t
    have hA : pA t = (ULift.up A : ULift.{v, 0} (OrthogonalMatrixHom m n)) :=
      CGWH.pointHomEquiv_symm_apply_apply.{u, v} Z (ULift.up A) t
    have hB : pB t = (ULift.up B : ULift.{v, 0} (OrthogonalMatrixHom m n)) :=
      CGWH.pointHomEquiv_symm_apply_apply.{u, v} Z (ULift.up B) t
    exact hA.symm.trans (ht.trans hB)
  exact congrArg ULift.down hz

/-- A matrix point never equals the freely adjoined basepoint. -/
theorem matrixPoint_ne_zero {m n : OrthogonalIndex}
    (A : OrthogonalMatrixHom m n) : matrixPoint.{u, v} A ≠ 0 := by
  intro h
  let Z : CGWH.{u, v} := rawHomCGWH.{u, v} m n
  let H : PointedCGWH.{u, v} := (Under.costar CGWH.point.{u, v}).obj Z
  let freeGenerator : CGWH.point.{u, v} ⟶
      (𝟙_ PointedCGWH.{u, v}).right := coprod.inr
  let pA : CGWH.point.{u, v} ⟶ Z :=
    (CGWH.pointHomEquiv Z).symm (ULift.up A)
  have zeroRightIsTerminal : IsTerminal
      ((0 : PointedCGWH.{u, v}).right) := by
    let pointZero : PointedCGWH.{u, v} := Under.mk (𝟙 CGWH.point.{u, v})
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
    let zeroRightIso : (0 : PointedCGWH.{u, v}).right ≅ CGWH.point.{u, v} :=
      { hom := zeroPointedIso.hom.right
        inv := zeroPointedIso.inv.right
        hom_inv_id := congrArg (fun g ↦ g.right) zeroPointedIso.hom_inv_id
        inv_hom_id := congrArg (fun g ↦ g.right) zeroPointedIso.inv_hom_id }
    exact IsTerminal.ofIso CGWH.point_isTerminal zeroRightIso.symm
  have hzero : freeGenerator ≫
      (0 : 𝟙_ PointedCGWH.{u, v} ⟶ H).right = H.hom := by
    change freeGenerator ≫
      ((default : 𝟙_ PointedCGWH.{u, v} ⟶
        (0 : PointedCGWH.{u, v})).right ≫
      (default : (0 : PointedCGWH.{u, v}) ⟶ H).right) = _
    rw [← Category.assoc]
    have hfirst : freeGenerator ≫
        (default : 𝟙_ PointedCGWH.{u, v} ⟶
          (0 : PointedCGWH.{u, v})).right =
        (0 : PointedCGWH.{u, v}).hom := zeroRightIsTerminal.hom_ext _ _
    rw [hfirst]
    exact Under.w (default : (0 : PointedCGWH.{u, v}) ⟶ H)
  have hmatrix : freeGenerator ≫ (matrixPoint.{u, v} A).right =
      pA ≫ (coprod.inr : Z ⟶ CGWH.point.{u, v} ⨿ Z) := by
    change (coprod.inr : CGWH.point.{u, v} ⟶
        CGWH.point.{u, v} ⨿ CGWH.point.{u, v}) ≫
      coprod.map (𝟙 CGWH.point.{u, v}) pA = _
    exact coprod.inr_map _ _
  have hbase : H.hom =
      (coprod.inl : CGWH.point.{u, v} ⟶ CGWH.point.{u, v} ⨿ Z) :=
    (Under.costar_obj_hom CGWH.point.{u, v} Z).trans (coprod.inl_desc _ _)
  have hright : freeGenerator ≫ (matrixPoint.{u, v} A).right =
      freeGenerator ≫ (0 : 𝟙_ PointedCGWH.{u, v} ⟶ H).right :=
    congrArg (fun f => freeGenerator ≫ f.right) h
  have hbranches : pA ≫ (coprod.inr : Z ⟶ CGWH.point.{u, v} ⨿ Z) =
      (coprod.inl : CGWH.point.{u, v} ⟶ CGWH.point.{u, v} ⨿ Z) :=
    hmatrix.symm.trans (hright.trans (hzero.trans hbase))
  let R : CGWH.{u, v} := CGWH.of.{u, v} (ULift.{v, 0} ℝ)
  let p0 : CGWH.point.{u, v} ⟶ R :=
    (CGWH.pointHomEquiv R).symm (ULift.up (0 : ℝ))
  let p1 : CGWH.point.{u, v} ⟶ R :=
    (CGWH.pointHomEquiv R).symm (ULift.up (1 : ℝ))
  let r : Z ⟶ R := CGWH.point_isTerminal.from Z ≫ p1
  have hseparate : pA ≫ r = p0 := by
    have ht := congrArg (fun f => f ≫ coprod.desc p0 r) hbranches
    simpa only [Category.assoc, coprod.inr_desc, coprod.inl_desc] using ht
  let t : CGWH.point.{u, v} := PUnit.unit
  have heval : r (pA t) = p0 t := by
    simpa only [ConcreteCategory.comp_apply] using
      ConcreteCategory.congr_hom hseparate t
  have h1 : r (pA t) = (ULift.up (1 : ℝ) : R) := by
    change (CGWH.pointHomEquiv R).symm (ULift.up (1 : ℝ))
      ((CGWH.point_isTerminal.from Z) (pA t)) = _
    exact CGWH.pointHomEquiv_symm_apply_apply.{u, v} R _ _
  have h0 : p0 t = (ULift.up (0 : ℝ) : R) :=
    CGWH.pointHomEquiv_symm_apply_apply.{u, v} R _ _
  have hscalar : (ULift.up (1 : ℝ) : ULift.{v, 0} ℝ) =
      ULift.up (0 : ℝ) := h1.symm.trans (heval.trans h0)
  exact one_ne_zero (congrArg ULift.down hscalar)

end OrthogonalIndex
end CategoryTheory.Spectra
