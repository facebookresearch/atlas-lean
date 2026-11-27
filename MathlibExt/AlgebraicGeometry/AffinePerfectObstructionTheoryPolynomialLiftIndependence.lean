/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.AffinePerfectObstructionTheory
import Mathlib.Algebra.Homology.ComplexShape
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.Embedding.Extend
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.RingTheory.Extension.Cotangent.Basic

/-!
# Independence of the obstruction class from the polynomial lift

For a fixed perfect obstruction theory and square-zero extension, the obstruction
classes attached to two polynomial lifts with normalized cocycles agree. The
difference of the lifts is a derivation into the conormal module, so the two
cocycles are homotopic and induce the same map in the derived category.

Reference: Behrend--Fantechi, *The intrinsic normal cone*, §4,
https://arxiv.org/abs/alg-geom/9601010.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.AffinePerfectObstructionTheoryWanted

open _root_.CategoryTheory
open MathlibExt.AlgebraicGeometry.GeometricCotangentComplex
open MathlibExt.AlgebraicGeometry.AffinePerfectObstructionTheory
open Opposite Simplicial

attribute [local instance] HasDerivedCategory.standard

/-- The degree-zero term of the resolution as an extension of `B` along the augmentation. -/
private abbrev degreeZeroExtension {k B : Type} [Field k] [CommRing B] [Algebra k B]
    (R : PolynomialResolution k B) : Algebra.Extension.{0} k B :=
  Algebra.Extension.ofSurjective (R.augmentation.app (op ⦋0⦌)).hom (R.surjective (op ⦋0⦌))

/-- A polynomial lift as a morphism of extensions out of the degree-zero term. -/
private def liftHom {k B : Type} [Field k] [CommRing B] [Algebra k B]
    (R : PolynomialResolution k B) (Q : Algebra.Extension.{0} k B) (L : PolynomialLift R Q) :
    (degreeZeroExtension R).Hom Q :=
  Algebra.Extension.Hom.ofAlgHom L.hom
    (AlgHom.ext fun t => congrArg (fun f : R.algebra.obj (op ⦋0⦌) →ₐ[k] B => f t) L.over)

/-- The difference map of two lifts on `1 ⊗ ω`, over the degree-zero term. -/
private def homotopyAdjoint {k B : Type} [Field k] [CommRing B] [Algebra k B]
    (R : PolynomialResolution k B) (Q : Algebra.Extension.{0} k B)
    (L L' : PolynomialLift R Q) :
    ModuleCat.of (degreeZeroExtension R).Ring Ω[(degreeZeroExtension R).Ring⁄k] ⟶
      (ModuleCat.restrictScalars (algebraMap (degreeZeroExtension R).Ring B)).obj
        (ModuleCat.of B Q.Cotangent) :=
  ModuleCat.ofHom
    { toFun := fun ω => (liftHom R Q L).sub (liftHom R Q L') (1 ⊗ₜ ω)
      map_add' := fun x y => by
        change (liftHom R Q L).sub (liftHom R Q L') (1 ⊗ₜ (x + y)) =
          (liftHom R Q L).sub (liftHom R Q L') (1 ⊗ₜ x) +
            (liftHom R Q L).sub (liftHom R Q L') (1 ⊗ₜ y)
        rw [TensorProduct.tmul_add, map_add]
      map_smul' := fun a x => by
        change (liftHom R Q L).sub (liftHom R Q L') (1 ⊗ₜ (a • x)) =
          algebraMap (degreeZeroExtension R).Ring B a •
            (liftHom R Q L).sub (liftHom R Q L') (1 ⊗ₜ x)
        rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one, ← map_smul,
          TensorProduct.smul_tmul', smul_eq_mul, mul_one] }

/-- The `B`-linear homotopy map out of the degree-zero cotangent term. -/
private def homotopyMap' {k B : Type} [Field k] [CommRing B] [Algebra k B]
    (R : PolynomialResolution k B) (Q : Algebra.Extension.{0} k B)
    (L L' : PolynomialLift R Q) :
    CommAlgCat.resolutionCotangentTerm k (CommAlgCat.of k B) R.algebra R.augmentation
        (op ⦋0⦌) ⟶ ModuleCat.of B Q.Cotangent :=
  ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    (CommAlgCat.resolutionAugmentationHom k (CommAlgCat.of k B) R.algebra R.augmentation
      (op ⦋0⦌))
    (homotopyAdjoint R Q L L')

/-- The homotopy map on a pure differential is the difference of the lifts. -/
private theorem homotopyMap'_pure {k B : Type} [Field k] [CommRing B] [Algebra k B]
    (R : PolynomialResolution k B) (Q : Algebra.Extension.{0} k B)
    (L L' : PolynomialLift R Q) (t : R.algebra.obj (op ⦋0⦌)) :
    homotopyMap' R Q L L'
        (CommAlgCat.resolutionCotangentTermDifferential k (CommAlgCat.of k B) R.algebra
          R.augmentation (op ⦋0⦌) t)
      = Algebra.Extension.Cotangent.mk ((liftHom R Q L).subToKer (liftHom R Q L') t) := by
  refine (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_tmul _ _ _ _).trans ?_
  rw [one_smul]
  exact Algebra.Extension.Hom.sub_one_tmul (liftHom R Q L) (liftHom R Q L') t

open AlgebraicTopology in
/-- Read through `affineDegreeIso`, the differential of the affine complex is the
alternating sum of the face maps. -/
private theorem affineComplex_d {k B : Type} [Field k] [CommRing B] [Algebra k B]
    (R : PolynomialResolution k B) (n : ℕ) :
    (affineComplex R).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) =
      (affineDegreeIso R (n + 1)).hom ≫
        AlternatingFaceMapComplex.objD (CommAlgCat.resolutionCotangentSimplicialModule k
          (CommAlgCat.of k B) R.algebra R.augmentation).object n ≫
        (affineDegreeIso R n).inv := by
  rw [← alternatingFaceMapComplex_obj_d]
  exact HomologicalComplex.extend_d_eq _ (ComplexShape.embeddingUpIntLE 0) (by simp) (by simp)

/-- A face map sends `1 ⊗ d p` to `1 ⊗ d (δᵢ p)`. -/
private theorem face_differential {k B : Type} [Field k] [CommRing B] [Algebra k B]
    (R : PolynomialResolution k B) (i : Fin 2) (p : R.algebra.obj (op ⦋1⦌)) :
    (CommAlgCat.resolutionCotangentSimplicialModule k (CommAlgCat.of k B) R.algebra
        R.augmentation).object.δ i
        (CommAlgCat.resolutionCotangentTermDifferential k (CommAlgCat.of k B) R.algebra
          R.augmentation (op ⦋1⦌) p) =
      CommAlgCat.resolutionCotangentTermDifferential k (CommAlgCat.of k B) R.algebra
        R.augmentation (op ⦋0⦌) (R.algebra.δ i p) :=
  CommAlgCat.resolutionCotangentMap_D k (CommAlgCat.of k B) R.algebra R.augmentation
    (SimplexCategory.δ i).op p

open AlgebraicTopology in
/-- The alternating sum in degree zero is `δ₀ - δ₁`. -/
private theorem objD_zero {k B : Type} [Field k] [CommRing B] [Algebra k B]
    (R : PolynomialResolution k B) :
    AlternatingFaceMapComplex.objD
        (CommAlgCat.resolutionCotangentSimplicialModule k (CommAlgCat.of k B) R.algebra
          R.augmentation).object 0
      = (CommAlgCat.resolutionCotangentSimplicialModule k (CommAlgCat.of k B) R.algebra
          R.augmentation).object.δ 0
        - (CommAlgCat.resolutionCotangentSimplicialModule k (CommAlgCat.of k B) R.algebra
          R.augmentation).object.δ 1 := by
  simp [AlternatingFaceMapComplex.objD, Fin.sum_univ_two, sub_eq_add_neg]

open AlgebraicTopology in
/-- Through the degree isomorphisms, the differential sends `1 ⊗ d p` to the face
difference. -/
private theorem faceDiffEq {k B : Type} [Field k] [CommRing B] [Algebra k B]
    (R : PolynomialResolution k B) (p : R.algebra.obj (op ⦋1⦌)) :
    (affineDegreeIso R 0).hom
        ((affineComplex R).d (-1) 0 ((affineDegreeIso R 1).inv
          (CommAlgCat.resolutionCotangentTermDifferential k (CommAlgCat.of k B) R.algebra
            R.augmentation (op ⦋1⦌) p)))
      = CommAlgCat.resolutionCotangentTermDifferential k (CommAlgCat.of k B) R.algebra
          R.augmentation (op ⦋0⦌) (R.algebra.δ 0 p)
        - CommAlgCat.resolutionCotangentTermDifferential k (CommAlgCat.of k B) R.algebra
          R.augmentation (op ⦋0⦌) (R.algebra.δ 1 p) := by
  have hd : (affineComplex R).d (-1) 0 = (affineDegreeIso R 1).hom ≫
      AlternatingFaceMapComplex.objD
        (CommAlgCat.resolutionCotangentSimplicialModule k (CommAlgCat.of k B) R.algebra
          R.augmentation).object 0 ≫ (affineDegreeIso R 0).inv :=
    affineComplex_d R 0
  rw [hd]
  change (affineDegreeIso R 0).hom ((affineDegreeIso R 0).inv
      (AlternatingFaceMapComplex.objD
        (CommAlgCat.resolutionCotangentSimplicialModule k (CommAlgCat.of k B) R.algebra
          R.augmentation).object 0 ((affineDegreeIso R 1).hom
        ((affineDegreeIso R 1).inv (CommAlgCat.resolutionCotangentTermDifferential k
          (CommAlgCat.of k B) R.algebra R.augmentation (op ⦋1⦌) p)))))
    = CommAlgCat.resolutionCotangentTermDifferential k (CommAlgCat.of k B) R.algebra
        R.augmentation (op ⦋0⦌) (R.algebra.δ 0 p)
      - CommAlgCat.resolutionCotangentTermDifferential k (CommAlgCat.of k B) R.algebra
        R.augmentation (op ⦋0⦌) (R.algebra.δ 1 p)
  have he1app : (affineDegreeIso R 1).hom ((affineDegreeIso R 1).inv
      (CommAlgCat.resolutionCotangentTermDifferential k (CommAlgCat.of k B) R.algebra
        R.augmentation (op ⦋1⦌) p))
      = CommAlgCat.resolutionCotangentTermDifferential k (CommAlgCat.of k B) R.algebra
        R.augmentation (op ⦋1⦌) p :=
    Iso.inv_hom_id_apply _ _
  rw [he1app]
  have he0app : (affineDegreeIso R 0).hom ((affineDegreeIso R 0).inv
      (AlternatingFaceMapComplex.objD
        (CommAlgCat.resolutionCotangentSimplicialModule k (CommAlgCat.of k B) R.algebra
          R.augmentation).object 0
        (CommAlgCat.resolutionCotangentTermDifferential k (CommAlgCat.of k B) R.algebra
          R.augmentation (op ⦋1⦌) p)))
      = AlternatingFaceMapComplex.objD
        (CommAlgCat.resolutionCotangentSimplicialModule k (CommAlgCat.of k B) R.algebra
          R.augmentation).object 0
        (CommAlgCat.resolutionCotangentTermDifferential k (CommAlgCat.of k B) R.algebra
          R.augmentation (op ⦋1⦌) p) :=
    Iso.inv_hom_id_apply _ _
  rw [he0app, objD_zero]
  change (CommAlgCat.resolutionCotangentSimplicialModule k (CommAlgCat.of k B) R.algebra
        R.augmentation).object.δ 0
        (CommAlgCat.resolutionCotangentTermDifferential k (CommAlgCat.of k B) R.algebra
          R.augmentation (op ⦋1⦌) p)
      - (CommAlgCat.resolutionCotangentSimplicialModule k (CommAlgCat.of k B) R.algebra
        R.augmentation).object.δ 1
        (CommAlgCat.resolutionCotangentTermDifferential k (CommAlgCat.of k B) R.algebra
          R.augmentation (op ⦋1⦌) p)
    = CommAlgCat.resolutionCotangentTermDifferential k (CommAlgCat.of k B) R.algebra
        R.augmentation (op ⦋0⦌) (R.algebra.δ 0 p)
      - CommAlgCat.resolutionCotangentTermDifferential k (CommAlgCat.of k B) R.algebra
        R.augmentation (op ⦋0⦌) (R.algebra.δ 1 p)
  rw [face_differential R 0 p, face_differential R 1 p]
  rfl

/-- The homotopy component from degree zero to degree minus one. -/
private def homotopyMap0 {k B : Type} [Field k] [CommRing B] [Algebra k B]
    (R : PolynomialResolution k B) (Q : Algebra.Extension.{0} k B)
    (L L' : PolynomialLift R Q) :
    (affineComplex R).X 0 ⟶ (coefficientComplex Q).X (-1) :=
  (affineDegreeIso R 0).hom ≫ homotopyMap' R Q L L' ≫
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-1)
      (ModuleCat.of B Q.Cotangent)).inv

/-- The homotopy data between the two normalized cocycles, supported in degree zero to
minus one. -/
private def homotopyHom {k B : Type} [Field k] [CommRing B] [Algebra k B]
    (R : PolynomialResolution k B) (Q : Algebra.Extension.{0} k B)
    (L L' : PolynomialLift R Q) :
    ∀ i j : ℤ, (affineComplex R).X i ⟶ (coefficientComplex Q).X j :=
  fun i j => if h : i = 0 ∧ j = -1 then h.1.symm ▸ h.2.symm ▸ homotopyMap0 R Q L L'
    else 0

/-- The homotopy family agrees with the homotopy map in degree zero to minus one. -/
private theorem homotopyHom_zero {k B : Type} [Field k] [CommRing B] [Algebra k B]
    (R : PolynomialResolution k B) (Q : Algebra.Extension.{0} k B)
    (L L' : PolynomialLift R Q) :
    homotopyHom R Q L L' 0 (-1) = homotopyMap0 R Q L L' := by
  unfold homotopyHom
  rw [dite_eq_left ⟨rfl, rfl⟩]

/-- The homotopy family vanishes away from degree zero to minus one. -/
private theorem homotopyHom_ne {k B : Type} [Field k] [CommRing B] [Algebra k B]
    (R : PolynomialResolution k B) (Q : Algebra.Extension.{0} k B)
    (L L' : PolynomialLift R Q) (i j : ℤ) (h : ¬(i = 0 ∧ j = -1)) :
    homotopyHom R Q L L' i j = 0 := by
  unfold homotopyHom
  rw [dite_eq_right h]

/-- Away from degree minus one, the `dNext` part of the homotopy vanishes. -/
private theorem dNext_homotopyHom_ne {k B : Type} [Field k] [CommRing B] [Algebra k B]
    (R : PolynomialResolution k B) (Q : Algebra.Extension.{0} k B)
    (L L' : PolynomialLift R Q) (i : ℤ) (hi : i ≠ -1) :
    dNext i (homotopyHom R Q L L') = 0 := by
  have hnext : (ComplexShape.up ℤ).next i = i + 1 :=
    ComplexShape.next_eq' _ (ComplexShape.up_mk i (i + 1) rfl)
  have hw : (ComplexShape.up ℤ).Rel i ((ComplexShape.up ℤ).next i) := by
    rw [hnext]
    exact ComplexShape.up_mk _ _ rfl
  rw [dNext_eq _ hw,
    homotopyHom_ne R Q L L' ((ComplexShape.up ℤ).next i) i (fun h => hi h.2),
    Limits.comp_zero]

/-- Away from degree zero, the `prevD` part of the homotopy vanishes. -/
private theorem prevD_homotopyHom_ne {k B : Type} [Field k] [CommRing B] [Algebra k B]
    (R : PolynomialResolution k B) (Q : Algebra.Extension.{0} k B)
    (L L' : PolynomialLift R Q) (i : ℤ) (hi : i ≠ 0) :
    prevD i (homotopyHom R Q L L') = 0 := by
  have hprev : (ComplexShape.up ℤ).prev i = i - 1 :=
    ComplexShape.prev_eq' _ (ComplexShape.up_mk (i - 1) i (sub_add_cancel i 1))
  have hw : (ComplexShape.up ℤ).Rel ((ComplexShape.up ℤ).prev i) i := by
    rw [hprev]
    exact ComplexShape.up_mk _ _ (sub_add_cancel _ _)
  rw [prevD_eq _ hw,
    homotopyHom_ne R Q L L' i ((ComplexShape.up ℤ).prev i) (fun h => hi h.1),
    Limits.zero_comp]

/-- In degree minus one, the `dNext` part is the differential followed by the homotopy
map. -/
private theorem dNext_homotopyHom_neg_one {k B : Type} [Field k] [CommRing B] [Algebra k B]
    (R : PolynomialResolution k B) (Q : Algebra.Extension.{0} k B)
    (L L' : PolynomialLift R Q) :
    dNext (-1) (homotopyHom R Q L L')
      = (affineComplex R).d (-1) 0 ≫ homotopyMap0 R Q L L' := by
  have hw : (ComplexShape.up ℤ).Rel (-1) 0 :=
    ComplexShape.up_mk _ _ (by norm_num)
  rw [dNext_eq _ hw, homotopyHom_zero R Q L L']

/-- In degree minus one, the `prevD` part vanishes. -/
private theorem prevD_homotopyHom_neg_one {k B : Type} [Field k] [CommRing B] [Algebra k B]
    (R : PolynomialResolution k B) (Q : Algebra.Extension.{0} k B)
    (L L' : PolynomialLift R Q) :
    prevD (-1) (homotopyHom R Q L L') = 0 := by
  have hprev : (ComplexShape.up ℤ).prev (-1) = -1 - 1 :=
    ComplexShape.prev_eq' _ (ComplexShape.up_mk (-1 - 1) (-1) (sub_add_cancel _ _))
  have hw : (ComplexShape.up ℤ).Rel ((ComplexShape.up ℤ).prev (-1)) (-1) := by
    rw [hprev]
    exact ComplexShape.up_mk _ _ (sub_add_cancel _ _)
  rw [prevD_eq _ hw,
    homotopyHom_ne R Q L L' (-1) ((ComplexShape.up ℤ).prev (-1))
      (fun h => absurd h.1 (by norm_num)),
    Limits.zero_comp]

/-- In degree zero, the `prevD` part vanishes since the target differential is zero. -/
private theorem prevD_homotopyHom_zero {k B : Type} [Field k] [CommRing B] [Algebra k B]
    (R : PolynomialResolution k B) (Q : Algebra.Extension.{0} k B)
    (L L' : PolynomialLift R Q) :
    prevD 0 (homotopyHom R Q L L') = 0 := by
  have hprev : (ComplexShape.up ℤ).prev 0 = -1 :=
    ComplexShape.prev_eq' _ (ComplexShape.up_mk _ _ (by norm_num))
  have hw : (ComplexShape.up ℤ).Rel ((ComplexShape.up ℤ).prev 0) 0 := by
    rw [hprev]
    exact ComplexShape.up_mk _ _ (by norm_num)
  rw [prevD_eq _ hw, hprev, homotopyHom_zero R Q L L',
    CochainComplex.singleFunctor_obj_d, Limits.comp_zero]

/-- The lift difference on faces recovers the difference of lift errors. -/
private theorem liftDiff_faceError {k B : Type} [Field k] [CommRing B] [Algebra k B]
    (R : PolynomialResolution k B) (Q : Algebra.Extension.{0} k B)
    (L L' : PolynomialLift R Q) (p : R.algebra.obj (op ⦋1⦌)) :
    Algebra.Extension.Cotangent.mk
          ((liftHom R Q L).subToKer (liftHom R Q L') (R.algebra.δ 0 p))
        - Algebra.Extension.Cotangent.mk
          ((liftHom R Q L).subToKer (liftHom R Q L') (R.algebra.δ 1 p))
      = liftError R Q L p - liftError R Q L' p := by
  unfold liftError
  rw [← map_sub, ← map_sub]
  congr 1
  ext
  change (L.hom (R.algebra.δ 0 p) - L'.hom (R.algebra.δ 0 p))
      - (L.hom (R.algebra.δ 1 p) - L'.hom (R.algebra.δ 1 p))
    = (L.hom (R.algebra.δ 0 p) - L.hom (R.algebra.δ 1 p))
      - (L'.hom (R.algebra.δ 0 p) - L'.hom (R.algebra.δ 1 p))
  ring

/-- The single isomorphism cancels the homotopy map's tail. -/
private theorem homotopyMap0_cancel {k B : Type} [Field k] [CommRing B] [Algebra k B]
    (R : PolynomialResolution k B) (Q : Algebra.Extension.{0} k B)
    (L L' : PolynomialLift R Q) (y : (affineComplex R).X 0) :
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-1)
        (ModuleCat.of B Q.Cotangent)).hom
        (homotopyMap0 R Q L L' y)
      = homotopyMap' R Q L L' ((affineDegreeIso R 0).hom y) := by
  change (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-1)
      (ModuleCat.of B Q.Cotangent)).hom
      ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-1)
        (ModuleCat.of B Q.Cotangent)).inv
        (homotopyMap' R Q L L' ((affineDegreeIso R 0).hom y)))
    = homotopyMap' R Q L L' ((affineDegreeIso R 0).hom y)
  exact Iso.inv_hom_id_apply _ _

/-- The homotopy boundary on a pure differential is the difference of lift errors. -/
private theorem homotopyBoundary_pure {k B : Type} [Field k] [CommRing B] [Algebra k B]
    (R : PolynomialResolution k B) (Q : Algebra.Extension.{0} k B)
    (L L' : PolynomialLift R Q) (p : R.algebra.obj (op ⦋1⦌)) :
    ((affineDegreeIso R 1).inv ≫ (((affineComplex R).d (-1) 0 ≫ homotopyMap0 R Q L L') ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-1)
        (ModuleCat.of B Q.Cotangent)).hom))
      (CommAlgCat.resolutionCotangentTermDifferential k (CommAlgCat.of k B) R.algebra
        R.augmentation (op ⦋1⦌) p)
    = liftError R Q L p - liftError R Q L' p := by
  calc ((affineDegreeIso R 1).inv ≫ (((affineComplex R).d (-1) 0 ≫ homotopyMap0 R Q L L') ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-1)
            (ModuleCat.of B Q.Cotangent)).hom))
          (CommAlgCat.resolutionCotangentTermDifferential k (CommAlgCat.of k B) R.algebra
            R.augmentation (op ⦋1⦌) p)
        = (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-1)
          (ModuleCat.of B Q.Cotangent)).hom
          (homotopyMap0 R Q L L' ((affineComplex R).d (-1) 0
            ((affineDegreeIso R 1).inv
              (CommAlgCat.resolutionCotangentTermDifferential k (CommAlgCat.of k B) R.algebra
                R.augmentation (op ⦋1⦌) p)))) := rfl
      _ = homotopyMap' R Q L L' ((affineDegreeIso R 0).hom
          ((affineComplex R).d (-1) 0 ((affineDegreeIso R 1).inv
            (CommAlgCat.resolutionCotangentTermDifferential k (CommAlgCat.of k B) R.algebra
              R.augmentation (op ⦋1⦌) p)))) :=
          homotopyMap0_cancel R Q L L' ((affineComplex R).d (-1) 0
            ((affineDegreeIso R 1).inv
              (CommAlgCat.resolutionCotangentTermDifferential k (CommAlgCat.of k B) R.algebra
                R.augmentation (op ⦋1⦌) p)))
      _ = homotopyMap' R Q L L'
          (CommAlgCat.resolutionCotangentTermDifferential k (CommAlgCat.of k B) R.algebra
            R.augmentation (op ⦋0⦌) (R.algebra.δ 0 p)
          - CommAlgCat.resolutionCotangentTermDifferential k (CommAlgCat.of k B) R.algebra
            R.augmentation (op ⦋0⦌) (R.algebra.δ 1 p)) :=
          congrArg (homotopyMap' R Q L L') (faceDiffEq R p)
      _ = homotopyMap' R Q L L'
            (CommAlgCat.resolutionCotangentTermDifferential k (CommAlgCat.of k B) R.algebra
              R.augmentation (op ⦋0⦌) (R.algebra.δ 0 p))
          - homotopyMap' R Q L L'
            (CommAlgCat.resolutionCotangentTermDifferential k (CommAlgCat.of k B) R.algebra
              R.augmentation (op ⦋0⦌) (R.algebra.δ 1 p)) :=
          map_sub _ _ _
      _ = Algebra.Extension.Cotangent.mk
            ((liftHom R Q L).subToKer (liftHom R Q L') (R.algebra.δ 0 p))
          - Algebra.Extension.Cotangent.mk
            ((liftHom R Q L).subToKer (liftHom R Q L') (R.algebra.δ 1 p)) := by
          rw [homotopyMap'_pure, homotopyMap'_pure]
      _ = liftError R Q L p - liftError R Q L' p :=
          liftDiff_faceError R Q L L' p

/-- Application distributes over sums of maps out of the degree-one term. -/
private theorem homAdd_apply {k B : Type} [Field k] [CommRing B] [Algebra k B]
    (R : PolynomialResolution k B) (Q : Algebra.Extension.{0} k B)
    (f g : CommAlgCat.resolutionCotangentTerm k (CommAlgCat.of k B) R.algebra R.augmentation
      (op ⦋1⦌) ⟶ ModuleCat.of B Q.Cotangent)
    (x : CommAlgCat.resolutionCotangentTerm k (CommAlgCat.of k B) R.algebra R.augmentation
      (op ⦋1⦌)) :
    (f + g) x = f x + g x := rfl

/-- In degree minus one, the two cocycles differ by the homotopy boundary. -/
private theorem cocycle_homotopy_neg_one {k B : Type} [Field k] [CommRing B] [Algebra k B]
    (R : PolynomialResolution k B) (Q : Algebra.Extension.{0} k B)
    (L L' : PolynomialLift R Q)
    (C : CotangentExtensionCocycle R Q L) (C' : CotangentExtensionCocycle R Q L') :
    C.morphism.f (-1)
      = (affineComplex R).d (-1) 0 ≫ homotopyMap0 R Q L L' + C'.morphism.f (-1) := by
  apply (cancel_mono (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-1)
    (ModuleCat.of B Q.Cotangent)).hom).mp
  apply (cancel_epi (affineDegreeIso R 1).inv).mp
  apply CommAlgCat.resolutionCotangentTerm_hom_ext k (CommAlgCat.of k B) R.algebra
    R.augmentation (op ⦋1⦌)
  intro p
  have hβ : (affineDegreeIso R 1).inv ≫
        (((affineComplex R).d (-1) 0 ≫ homotopyMap0 R Q L L') + C'.morphism.f (-1)) ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-1)
          (ModuleCat.of B Q.Cotangent)).hom
      = ((affineDegreeIso R 1).inv ≫ (((affineComplex R).d (-1) 0 ≫ homotopyMap0 R Q L L') ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-1)
          (ModuleCat.of B Q.Cotangent)).hom))
        + ((affineDegreeIso R 1).inv ≫ (C'.morphism.f (-1) ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-1)
          (ModuleCat.of B Q.Cotangent)).hom)) := by
    simp only [Preadditive.add_comp, Preadditive.comp_add]
  rw [hβ, homAdd_apply]
  have hC : ((affineDegreeIso R 1).inv ≫ (C.morphism.f (-1) ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-1)
        (ModuleCat.of B Q.Cotangent)).hom))
      (CommAlgCat.resolutionCotangentTermDifferential k (CommAlgCat.of k B) R.algebra
        R.augmentation (op ⦋1⦌) p) = liftError R Q L p :=
    C.normalization p
  have hC' : ((affineDegreeIso R 1).inv ≫ (C'.morphism.f (-1) ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-1)
        (ModuleCat.of B Q.Cotangent)).hom))
      (CommAlgCat.resolutionCotangentTermDifferential k (CommAlgCat.of k B) R.algebra
        R.augmentation (op ⦋1⦌) p) = liftError R Q L' p :=
    C'.normalization p
  rw [hC, hC', homotopyBoundary_pure R Q L L' p]
  exact (sub_add_cancel _ _).symm

/-- The two normalized cocycles are homotopic. -/
private def cocycleHomotopy {k B : Type} [Field k] [CommRing B] [Algebra k B]
    (R : PolynomialResolution k B) (Q : Algebra.Extension.{0} k B)
    (L L' : PolynomialLift R Q)
    (C : CotangentExtensionCocycle R Q L) (C' : CotangentExtensionCocycle R Q L') :
    Homotopy C.morphism C'.morphism where
  hom := homotopyHom R Q L L'
  zero := by
    intro i j hrel
    apply homotopyHom_ne
    intro h
    apply hrel
    rw [h.2, h.1]
    exact ComplexShape.up_mk _ _ (by norm_num)
  comm := by
    intro i
    by_cases hi : i = -1
    · subst hi
      rw [dNext_homotopyHom_neg_one R Q L L', prevD_homotopyHom_neg_one R Q L L',
        add_zero]
      exact cocycle_homotopy_neg_one R Q L L' C C'
    · by_cases hi0 : i = 0
      · subst hi0
        rw [dNext_homotopyHom_ne R Q L L' 0 hi, prevD_homotopyHom_zero R Q L L']
        have hC : C.morphism.f 0 = C'.morphism.f 0 :=
          (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (-1)
            (ModuleCat.of B Q.Cotangent) 0 hi).eq_of_tgt _ _
        rw [hC, add_zero, zero_add]
      · rw [dNext_homotopyHom_ne R Q L L' i hi, prevD_homotopyHom_ne R Q L L' i hi0]
        have hC : C.morphism.f i = C'.morphism.f i :=
          (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (-1)
            (ModuleCat.of B Q.Cotangent) i hi).eq_of_tgt _ _
        rw [hC, add_zero, zero_add]

/-- The class in the actual derived obstruction group is independent of the
chosen polynomial lift, with the explicit cocycle normalization retained. -/
public theorem polynomial_lift_independence
    {k B : Type} [Field k] [CommRing B] [Algebra k B]
    (R : PolynomialResolution k B) (T : PerfectObstructionTheory R)
    (Q : Algebra.Extension.{0} k B) (_squareZero : Q.ker ^ 2 = ⊥)
    (L L' : PolynomialLift R Q)
    (C : CotangentExtensionCocycle R Q L) (C' : CotangentExtensionCocycle R Q L') :
    obstructionClass T C = obstructionClass T C' := by
  unfold obstructionClass
  rw [DerivedCategory.Q_map_eq_of_homotopy _ (cocycleHomotopy R Q L L' C C')]

end WantedExt.AlgebraicGeometry.AffinePerfectObstructionTheoryWanted
