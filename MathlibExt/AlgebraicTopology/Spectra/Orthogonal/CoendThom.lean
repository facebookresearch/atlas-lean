/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.ComplementBundle
import MathlibExt.Topology.Category.PointedCGWH.Points
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.NativeOperatorIndex
import MathlibExt.CategoryTheory.Enriched.Limits.WeightedCoendPoint
import MathlibExt.CategoryTheory.Enriched.FreeEvaluation

/-!
# The original orthogonal weighted coend and the inherited complement Thom space

All coefficient degrees and full native hom-object balancing maps are retained.
The forward is the original weighted-coend descent of the actual proper
matrix/vector legs. The inverse descends the original coend generators through
the proved proper frame quotient. Its continuity follows from that quotient
topology, without a continuous choice of orthogonal completion.

The bare index, original sphere operator, source right module, Day coefficient,
and spectrum model dictionaries remain distinct. No cofibrancy or model law is
an input to the comparison.
-/

set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory BraidedCategory Opposite
open CategoryTheory.Spectra Filter TopologicalSpace Topology
open scoped MonoidalClosed ZeroObject

attribute [local instance] HasZeroObject.zeroMorphismsOfZeroObject

namespace CategoryTheory.Spectra.OrthogonalCoendThom

open CategoryTheory.Spectra.OrthogonalComplementBundle
open PointedCGWH

attribute [local instance] OrthogonalIndex.enrichedCategory

/-- The original full weight action, retyped on its actual native matrix Hom objects. -/
def weightAction (n k a b : ℕ) :
    OrthogonalIndex.hom.{u, v} (b + n) k ⊗ OrthogonalIndex.hom.{u, v} a b ⟶
      OrthogonalIndex.hom.{u, v} (a + n) k :=
  MonoidalClosed.uncurry ((OrthogonalOperatorIndex.weight.{u, v} n k).map (op b) (op a))

/-- The original sphere transpose, retyped on the actual representation-sphere objects. -/
def sphereUncurry (a b : ℕ) :
    PointedCGWH.orthogonalSphere.{u, v} a ⊗ OrthogonalIndex.hom.{u, v} a b ⟶
      PointedCGWH.orthogonalSphere.{u, v} b :=
  MonoidalClosed.uncurry (orthogonalSphereFunctor.{u, v}.map a b)

theorem sphereUncurry_eq (a b : ℕ) :
    sphereUncurry.{u, v} a b =
      (β_ (PointedCGWH.orthogonalSphere.{u, v} a) (OrthogonalIndex.hom.{u, v} a b)).hom ≫
        PointedCGWH.orthogonalSphereAction.{u, v} a b :=
  orthogonalSphereFunctor_uncurry.{u, v} a b

/-- The original representation-sphere generalized point at a finite vector. -/
def spherePoint (a : ℕ) (x : Euclidean a) :
    𝟙_ PointedCGWH.{u, v} ⟶ PointedCGWH.orthogonalSphere.{u, v} a :=
  pointAt (PointedCGWH.orthogonalSphere a)
    ((ULift.up x : LiftedEuclidean.{v} a) : OnePoint (LiftedEuclidean.{v} a))

@[simp]
theorem spherePoint_value (a : ℕ) (x : Euclidean a) :
    pointValue (spherePoint.{u, v} a x) =
      ((ULift.up x : LiftedEuclidean.{v} a) : OnePoint (LiftedEuclidean.{v} a)) :=
  pointAt_value _ _

/-- Every original sphere point is its infinity basepoint or an actual finite Euclidean vector. -/
theorem spherePoint_cases (a : ℕ)
    (p : 𝟙_ PointedCGWH.{u, v} ⟶ PointedCGWH.orthogonalSphere.{u, v} a) :
    p = 0 ∨ ∃ x : Euclidean a, p = spherePoint a x := by
  generalize hp : pointValue p = x
  induction x using OnePoint.rec with
  | infty =>
      left
      apply pointValue_injective _
      exact hp.trans (pointValue_zero (PointedCGWH.orthogonalSphere.{u, v} a)).symm
  | coe x =>
      rcases x with ⟨x⟩
      right
      refine ⟨x, ?_⟩
      apply pointValue_injective _
      exact hp.trans (spherePoint_value a x).symm

/-- The exact matrix/sphere tensor point is the original finite integrand generator value. -/
theorem matrixSpherePoint_value (n k a : ℕ) (g : Frame n k a) (x : Euclidean a) :
    pointValue (pointPair (OrthogonalIndex.matrixPoint.{u, v} g) (spherePoint.{u, v} a x)) =
      finiteGeneratorInput.{u, v} n k a g x := by
  rw [pointPair_value, spherePoint_value]
  rfl

/-- All original finite integrand points have the actual inherited Thom formula. -/
theorem generatorThomLeg_matrixSpherePoint (n k a : ℕ) (g : Frame n k a) (x : Euclidean a) :
    pointValue (pointPair (OrthogonalIndex.matrixPoint.{u, v} g) (spherePoint.{u, v} a x) ≫
      generatorThomLeg.{u, v} n k a) =
      ((ULift.up (rawMap n k a (g, x)) : LiftedBundle.{v} n k) :
        OnePoint (LiftedBundle.{v} n k)) := by
  rw [pointValue_comp, matrixSpherePoint_value]
  exact generatorThomLeg_coe n k a g x

private theorem weight_matrixPoint (n k a b : ℕ) (g : Frame n k b)
    (r : OrthogonalMatrixHom a b) :
    pointPair (OrthogonalIndex.matrixPoint.{u, v} g) (OrthogonalIndex.matrixPoint.{u, v} r) ≫
        weightAction.{u, v} n k a b =
      OrthogonalIndex.matrixPoint.{u, v} (changeCoefficientAcross g r) := by
  let _ : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
  let _ : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
  let _ : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
    OrthogonalIndex.enrichedOrdinaryCategory.{u, v}
  let rr : a ⟶ b := OrthogonalIndex.matrixPoint.{u, v} r
  let gg : (b + n) ⟶ k := OrthogonalIndex.matrixPoint.{u, v} g
  let rn : (a + n) ⟶ (b + n) := rr ⊗ₘ 𝟙 n
  have hpre := Enriched.SphereOperator.weight_point_pre
    OrthogonalIndex.enrichedMonoidalData.{u, v} n k a b rr
  have hrn : rn = OrthogonalIndex.matrixPoint.{u, v}
      (OrthogonalMatrixHom.blockSum r (OrthogonalMatrixHom.id n)) := by
    change (λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫
      (OrthogonalIndex.matrixPoint.{u, v} r ⊗ₘ eId PointedCGWH.{u, v} n) ≫
        OrthogonalIndex.tensorMap.{u, v} a b n n = _
    rw [OrthogonalIndex.enrichedCategory_id]
    exact (OrthogonalIndex.tensorMap_blockSum.{u, v} r (OrthogonalMatrixHom.id n)).1
  have hcomp : rn ≫ gg = OrthogonalIndex.matrixPoint.{u, v} (changeCoefficientAcross g r) := by
    rw [hrn]
    exact (OrthogonalIndex.enrichedCategory_comp.{u, v}
      (OrthogonalMatrixHom.blockSum r (OrthogonalMatrixHom.id n)) g).1
  have hpoint : OrthogonalIndex.matrixPoint.{u, v} g ≫
      eHomWhiskerRight PointedCGWH.{u, v} rn k =
      OrthogonalIndex.matrixPoint.{u, v} (changeCoefficientAcross g r) := by
    have h := eHomEquiv_comp_eHomWhiskerRight
      (V := PointedCGWH.{u, v}) (C := OrthogonalIndex) rn gg
    exact h.trans (congrArg (eHomEquiv PointedCGWH.{u, v}) hcomp)
  rw [pointPair_factor_right]
  change (OrthogonalIndex.matrixPoint.{u, v} g ≫
      (ρ_ (OrthogonalIndex.hom.{u, v} (b + n) k)).inv ≫
      OrthogonalIndex.hom.{u, v} (b + n) k ◁ OrthogonalIndex.matrixPoint.{u, v} r) ≫
      weightAction.{u, v} n k a b = _
  have hp : (ρ_ (OrthogonalIndex.hom.{u, v} (b + n) k)).inv ≫
      OrthogonalIndex.hom.{u, v} (b + n) k ◁ OrthogonalIndex.matrixPoint.{u, v} r ≫
      weightAction.{u, v} n k a b = eHomWhiskerRight PointedCGWH.{u, v} rn k := hpre
  rw [Category.assoc, Category.assoc, hp]
  exact hpoint

private theorem sphereAction_matrixPoint (a b : ℕ) (r : OrthogonalMatrixHom a b)
    (x : Euclidean a) :
    pointPair (OrthogonalIndex.matrixPoint.{u, v} r) (spherePoint.{u, v} a x) ≫
        PointedCGWH.orthogonalSphereAction.{u, v} a b =
      spherePoint.{u, v} b (matrixLinear r.1 x) := by
  apply pointValue_injective _
  rw [pointValue_comp, pointPair_value, spherePoint_value, spherePoint_value]
  let H := OrthogonalIndex.hom.{u, v} a b
  let S := PointedCGWH.orthogonalSphere.{u, v} a
  let pg : H.right := pointValue (OrthogonalIndex.matrixPoint.{u, v} r)
  let x' : S.right := ((ULift.up x : LiftedEuclidean.{v} a) : OnePoint (LiftedEuclidean.{v} a))
  let q : H.right ⊗ S.right ⟶ (H ⊗ S).right :=
    (CategoryTheory.Pointed.smashPresentation CGWH.point CGWH.point_isTerminal H S).2.1.inl
  let c := Classical.choose ((CGWH.prodComparisonToTop_bijective H.right S.right).2 (pg, x'))
  let c' := (CGWH.tensorEquivProd H.right S.right).symm (pg, x')
  have hc : c = c' := canonicalProduct_choose H.right S.right pg x'
  have hAction : (PointedCGWH.orthogonalSphereAction.{u, v} a b).right (q c) =
      ((ULift.up (matrixLinear r.1 x) : LiftedEuclidean.{v} b) :
        OnePoint (LiftedEuclidean.{v} b)) :=
    PointedCGWH.orthogonalSphereAction_coe.{u, v} r x
  exact (congrArg (fun z : (H.right ⊗ S.right : CGWH.{u, v}) =>
    (PointedCGWH.orthogonalSphereAction.{u, v} a b).right (q z)) hc.symm).trans hAction

/-- Normalize the full original balancing face on all independent native point parameters. -/
private theorem balancing_weight_point {n k a b : ℕ} {T : PointedCGWH.{u, v}}
    (legs : ∀ c, OrthogonalIndex.hom.{u, v} (c + n) k ⊗
      PointedCGWH.orthogonalSphere.{u, v} c ⟶ T)
    (pg : 𝟙_ PointedCGWH.{u, v} ⟶ OrthogonalIndex.hom.{u, v} (b + n) k)
    (pr : 𝟙_ PointedCGWH.{u, v} ⟶ OrthogonalIndex.hom.{u, v} a b)
    (px : 𝟙_ PointedCGWH.{u, v} ⟶ PointedCGWH.orthogonalSphere.{u, v} a) :
    pointPair pg (pointPair pr px) ≫
        (α_ (OrthogonalIndex.hom.{u, v} (b + n) k)
          (OrthogonalIndex.hom.{u, v} a b) (PointedCGWH.orthogonalSphere.{u, v} a)).inv ≫
        (weightAction.{u, v} n k a b ⊗ₘ
            𝟙 (PointedCGWH.orthogonalSphere.{u, v} a)) ≫ legs a =
      pointPair (pointPair pg pr ≫ weightAction.{u, v} n k a b) px ≫ legs a := by
  rw [← Category.assoc (pointPair pg (pointPair pr px))]
  rw [pointPair_associator_inv]
  rw [← Category.assoc, pointPairNatural, Category.comp_id]

private theorem balancing_sphere_point {n k a b : ℕ} {T : PointedCGWH.{u, v}}
    (legs : ∀ c, OrthogonalIndex.hom.{u, v} (c + n) k ⊗
      PointedCGWH.orthogonalSphere.{u, v} c ⟶ T)
    (pg : 𝟙_ PointedCGWH.{u, v} ⟶ OrthogonalIndex.hom.{u, v} (b + n) k)
    (pr : 𝟙_ PointedCGWH.{u, v} ⟶ OrthogonalIndex.hom.{u, v} a b)
    (px : 𝟙_ PointedCGWH.{u, v} ⟶ PointedCGWH.orthogonalSphere.{u, v} a) :
    pointPair pg (pointPair pr px) ≫
        OrthogonalIndex.hom.{u, v} (b + n) k ◁
          PointedCGWH.orthogonalSphereAction.{u, v} a b ≫ legs b =
      pointPair pg (pointPair pr px ≫ PointedCGWH.orthogonalSphereAction.{u, v} a b) ≫
        legs b := by
  rw [← id_tensorHom, ← Category.assoc, pointPairNatural, Category.comp_id]

/-- The proper matrix-complement legs satisfy every full original continuous balancing map. -/
theorem generatorThomLeg_balanced (n k : ℕ) (a b : ℕ) :
    (α_ ((OrthogonalOperatorIndex.weight.{u, v} n k).obj (op b))
      (OrthogonalIndex.hom.{u, v} a b) (PointedCGWH.orthogonalSphere.{u, v} a)).inv ≫
        (MonoidalClosed.uncurry
          ((OrthogonalOperatorIndex.weight.{u, v} n k).map (op b) (op a)) ⊗ₘ
            𝟙 (PointedCGWH.orthogonalSphere.{u, v} a)) ≫ generatorThomLeg.{u, v} n k a =
      (OrthogonalOperatorIndex.weight.{u, v} n k).obj (op b) ◁
        PointedCGWH.orthogonalSphereAction.{u, v} a b ≫ generatorThomLeg.{u, v} n k b := by
  change (α_ (OrthogonalIndex.hom.{u, v} (b + n) k)
      (OrthogonalIndex.hom.{u, v} a b) (PointedCGWH.orthogonalSphere.{u, v} a)).inv ≫
    (weightAction.{u, v} n k a b ⊗ₘ 𝟙 (PointedCGWH.orthogonalSphere.{u, v} a)) ≫
      generatorThomLeg.{u, v} n k a =
    OrthogonalIndex.hom.{u, v} (b + n) k ◁ PointedCGWH.orthogonalSphereAction.{u, v} a b ≫
      generatorThomLeg.{u, v} n k b
  apply tensorTriplePoint_hom_ext
  intro pg pr px
  rw [balancing_weight_point, balancing_sphere_point]
  rcases OrthogonalIndex.homPoint_cases pg with rfl | ⟨g, rfl⟩
  · simp only [pointPair_zero_left, zero_comp]
  rcases OrthogonalIndex.homPoint_cases pr with rfl | ⟨r, rfl⟩
  · simp only [pointPair_zero_left, pointPair_zero_right, zero_comp]
  rcases spherePoint_cases a px with rfl | ⟨x, rfl⟩
  · simp only [pointPair_zero_right, zero_comp]
  rw [weight_matrixPoint, sphereAction_matrixPoint]
  apply pointValue_injective _
  rw [generatorThomLeg_matrixSpherePoint, generatorThomLeg_matrixSpherePoint]
  exact congrArg (fun p : ComplementBundle n k =>
    ((ULift.up p : LiftedBundle.{v} n k) : OnePoint (LiftedBundle.{v} n k)))
    (rawMap_allGrade_balanced n k a b g r x)

/-- The full native Hom remains the actual original weighted coend. -/
abbrev nativeHom (n k : ℕ) : PointedCGWH.{u, v} := OrthogonalOperatorIndex.hom.{u, v} n k

/-- The forward comparison is the actual full original weighted-coend descent. -/
def nativeToThom (n k : ℕ) : nativeHom.{u, v} n k ⟶ thom.{u, v} n k :=
  Enriched.weightedCoend.desc (OrthogonalOperatorIndex.weight.{u, v} n k)
    orthogonalSphereFunctor.{u, v} (fun a => generatorThomLeg n k a) (by
      intro a b
      have h := generatorThomLeg_balanced.{u, v} n k a b
      change ((α_ (OrthogonalIndex.hom.{u, v} (b + n) k)
        (OrthogonalIndex.hom.{u, v} a b) (PointedCGWH.orthogonalSphere.{u, v} a)).inv ≫
        (weightAction.{u, v} n k a b ⊗ₘ 𝟙 (PointedCGWH.orthogonalSphere.{u, v} a))) ≫
        generatorThomLeg n k a =
        (OrthogonalIndex.hom.{u, v} (b + n) k ◁
          ((β_ (OrthogonalIndex.hom.{u, v} a b) (PointedCGWH.orthogonalSphere.{u, v} a)).hom ≫
            sphereUncurry.{u, v} a b)) ≫
          generatorThomLeg n k b
      have hAction :
          (β_ (OrthogonalIndex.hom.{u, v} a b) (PointedCGWH.orthogonalSphere.{u, v} a)).hom ≫
            sphereUncurry.{u, v} a b =
          PointedCGWH.orthogonalSphereAction.{u, v} a b := by
        rw [sphereUncurry_eq, ← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]
      rw [hAction]
      exact h)

/-- The actual forward retains every full original integrand inclusion. -/
theorem nativeToThom_generator (n k a : ℕ) :
    OrthogonalOperatorIndex.ι.{u, v} n k a ≫ nativeToThom.{u, v} n k =
      generatorThomLeg.{u, v} n k a :=
  Enriched.weightedCoend.ι_desc (OrthogonalOperatorIndex.weight.{u, v} n k)
    orthogonalSphereFunctor.{u, v} _ _ a

/-- The forward's finite formula uses the original actual coend generator. -/
theorem nativeToThom_finite (n k a : ℕ) (g : Frame n k a) (x : Euclidean a) :
    (nativeToThom.{u, v} n k).right
        ((OrthogonalOperatorIndex.ι.{u, v} n k a).right
          (finiteGeneratorInput.{u, v} n k a g x)) =
      ((ULift.up (rawMap n k a (g, x)) : LiftedBundle.{v} n k) :
        OnePoint (LiftedBundle.{v} n k)) := by
  have h := ConcreteCategory.congr_hom
    (congrArg Under.Hom.right (nativeToThom_generator.{u, v} n k a))
    (finiteGeneratorInput.{u, v} n k a g x)
  exact h.trans (generatorThomLeg_coe.{u, v} n k a g x)

/-- The full original coend itself balances every finite first-block matrix change. -/
theorem nativeGenerator_balanced (n k a b : ℕ) (g : Frame n k b)
    (r : OrthogonalMatrixHom a b) (x : Euclidean a) :
    pointPair (OrthogonalIndex.matrixPoint.{u, v} (changeCoefficientAcross g r))
        (spherePoint.{u, v} a x) ≫ OrthogonalOperatorIndex.ι.{u, v} n k a =
      pointPair (OrthogonalIndex.matrixPoint.{u, v} g)
        (spherePoint.{u, v} b (matrixLinear r.1 x)) ≫ OrthogonalOperatorIndex.ι.{u, v} n k b := by
  have h := congrArg
    (fun f => pointPair (OrthogonalIndex.matrixPoint.{u, v} g)
      (pointPair (OrthogonalIndex.matrixPoint.{u, v} r) (spherePoint.{u, v} a x)) ≫ f)
    (OrthogonalOperatorIndex.balance.{u, v} n k a b)
  change pointPair (OrthogonalIndex.matrixPoint.{u, v} g)
      (pointPair (OrthogonalIndex.matrixPoint.{u, v} r) (spherePoint.{u, v} a x)) ≫
      (α_ (OrthogonalIndex.hom.{u, v} (b + n) k) (OrthogonalIndex.hom.{u, v} a b)
        (PointedCGWH.orthogonalSphere.{u, v} a)).inv ≫
        (weightAction.{u, v} n k a b ⊗ₘ 𝟙 (PointedCGWH.orthogonalSphere.{u, v} a)) ≫
          OrthogonalOperatorIndex.ι.{u, v} n k a =
      pointPair (OrthogonalIndex.matrixPoint.{u, v} g)
        (pointPair (OrthogonalIndex.matrixPoint.{u, v} r) (spherePoint.{u, v} a x)) ≫
        OrthogonalIndex.hom.{u, v} (b + n) k ◁ PointedCGWH.orthogonalSphereAction.{u, v} a b ≫
          OrthogonalOperatorIndex.ι.{u, v} n k b at h
  rw [balancing_weight_point, balancing_sphere_point, weight_matrixPoint,
    sphereAction_matrixPoint] at h
  exact h

/-- The original finite native coend value. -/
def nativeFiniteValue (n k a : ℕ) (g : Frame n k a) (x : Euclidean a) :
    (nativeHom.{u, v} n k).right :=
  (OrthogonalOperatorIndex.ι.{u, v} n k a).right (finiteGeneratorInput.{u, v} n k a g x)

/-- All original coefficient-degree balancing preserves the actual finite native coend value. -/
theorem nativeFiniteValue_balanced (n k a b : ℕ) (g : Frame n k b)
    (r : OrthogonalMatrixHom a b) (x : Euclidean a) :
    nativeFiniteValue.{u, v} n k a (changeCoefficientAcross g r) x =
      nativeFiniteValue.{u, v} n k b g (matrixLinear r.1 x) := by
  have h := congrArg pointValue (nativeGenerator_balanced.{u, v} n k a b g r x)
  simpa only [pointValue_comp, matrixSpherePoint_value, nativeFiniteValue] using h

/-- The native finite value is independent of all actual frame/vector representatives. -/
theorem nativeFiniteValue_choice_independent (n k a : ℕ) (g h : Frame n k a)
    (x y : Euclidean a) (hp : rawMap n k a (g, x) = rawMap n k a (h, y)) :
    nativeFiniteValue.{u, v} n k a g x = nativeFiniteValue.{u, v} n k a h y := by
  obtain ⟨r, hr, hx⟩ := (rawMap_eq_iff n k a g h x y).mp hp
  rw [hr, hx]
  exact (nativeFiniteValue_balanced.{u, v} n k a a g r y).symm

/-- The full original integrand/product isomorphism retains its finite matrix/vector generator. -/
theorem frameSphereProductIso_finite (n k a : ℕ) (g : Frame n k a) (x : Euclidean a) :
    (frameSphereProductIso.{u, v} n k a).hom.right (finiteGeneratorInput.{u, v} n k a g x) =
      (((ULift.up g : LiftedFrame.{v} n k a), (ULift.up x : LiftedEuclidean.{v} a)) :
        OnePoint (LiftedFrame.{v} n k a × LiftedEuclidean.{v} a)) := by
  let _ : BraidedCategory CGWH.{u, v} := BraidedCategory.ofCartesianMonoidalCategory
  let _ : SymmetricCategory CGWH.{u, v} := inferInstance
  let H := OrthogonalIndex.hom.{u, v} (a + n) k
  let S := PointedCGWH.orthogonalSphere.{u, v} a
  let K := LiftedFrame.{v} n k a
  let E := LiftedEuclidean.{v} a
  let I := frameHomOnePointIso.{u, v} n k a
  let μ := PointedCGWH.onePointProdSmashIso.{u, v} K E
    (liftedFrameOnePoint_generated n k a) (liftedEuclideanOnePoint_generated a)
  let pg : H.right := pointValue (OrthogonalIndex.matrixPoint.{u, v} g)
  let q : H.right ⊗ S.right ⟶ (H ⊗ S).right :=
    (CategoryTheory.Pointed.smashPresentation CGWH.point CGWH.point_isTerminal H S).2.1.inl
  let q' : (PointedCGWH.onePointOf.{u, v} K).right ⊗ S.right ⟶
      (PointedCGWH.onePointOf.{u, v} K ⊗ S).right :=
    (CategoryTheory.Pointed.smashPresentation CGWH.point CGWH.point_isTerminal
      (PointedCGWH.onePointOf.{u, v} K) S).2.1.inl
  let c := (CGWH.tensorEquivProd H.right S.right).symm
    (pg, ((ULift.up x : E) : OnePoint E))
  let c' := (CGWH.tensorEquivProd (PointedCGWH.onePointOf.{u, v} K).right S.right).symm
    (((ULift.up g : K) : OnePoint K), ((ULift.up x : E) : OnePoint E))
  have hn := ConcreteCategory.congr_hom
    (CategoryTheory.Pointed.smashQuotient_naturality
      CGWH.point CGWH.point_isTerminal I.hom (𝟙 S)) c
  change (I.hom ⊗ₘ 𝟙 S).right (q c) = q' ((I.hom.right ⊗ₘ 𝟙 S.right) c) at hn
  have hg : I.hom.right pg = ((ULift.up g : K) : OnePoint K) :=
    frameHomOnePointIso_matrixPoint.{u, v} n k a g
  have hc : (I.hom.right ⊗ₘ 𝟙 S.right) c = c' := by
    have h := CGWH.tensorEquivProd_symm_map I.hom.right (𝟙 S.right) pg
      (((ULift.up x : E) : OnePoint E))
    rw [hg] at h
    exact h
  have hμ : μ.hom.right (((ULift.up g : K), (ULift.up x : E)) : OnePoint (K × E)) = q' c' :=
    PointedCGWH.onePointProdSmashIso_coe K E _ _ (ULift.up g) (ULift.up x)
  have hcancel := ConcreteCategory.congr_hom
    (congrArg Under.Hom.right μ.hom_inv_id)
    (((ULift.up g : K), (ULift.up x : E)) : OnePoint (K × E))
  simp only [Under.comp_right, Under.id_right] at hcancel
  change μ.inv.right ((I.hom ⊗ₘ 𝟙 S).right (q c)) = _
  rw [hn, hc, ← hμ]
  exact hcancel

/-- The inverse product isomorphism returns the exact original finite integrand generator. -/
theorem frameSphereProductIso_inv_finite (n k a : ℕ) (g : Frame n k a) (x : Euclidean a) :
    (frameSphereProductIso.{u, v} n k a).inv.right
        ((((ULift.up g : LiftedFrame.{v} n k a), (ULift.up x : LiftedEuclidean.{v} a)) :
          OnePoint (LiftedFrame.{v} n k a × LiftedEuclidean.{v} a))) =
      finiteGeneratorInput.{u, v} n k a g x := by
  have h := frameSphereProductIso_finite.{u, v} n k a g x
  have hi := ConcreteCategory.congr_hom
    (congrArg Under.Hom.right (frameSphereProductIso.{u, v} n k a).hom_inv_id)
    (finiteGeneratorInput.{u, v} n k a g x)
  exact (congrArg (frameSphereProductIso.{u, v} n k a).inv.right h).symm.trans hi

/-- The original coend generator as an arrow from the actual product compactification. -/
def nativeOnePointArrow (n k a : ℕ) :
    PointedCGWH.onePointOf.{u, v} (LiftedFrame.{v} n k a × LiftedEuclidean.{v} a) ⟶
      nativeHom.{u, v} n k :=
  (frameSphereProductIso n k a).inv ≫ OrthogonalOperatorIndex.ι n k a

/-- The entire compactified original generator composes to the actual proper Thom comparison. -/
theorem nativeOnePointArrow_forward (n k a : ℕ) :
    nativeOnePointArrow.{u, v} n k a ≫ nativeToThom.{u, v} n k =
      liftedOnePointComparison.{u, v} n k a := by
  rw [nativeOnePointArrow, Category.assoc, nativeToThom_generator, generatorThomLeg]
  rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The original product-compactification arrow retains each finite native coend generator. -/
theorem nativeOnePointArrow_finite (n k a : ℕ) (g : Frame n k a) (x : Euclidean a) :
    (nativeOnePointArrow.{u, v} n k a).right
        ((((ULift.up g : LiftedFrame.{v} n k a), (ULift.up x : LiftedEuclidean.{v} a)) :
          OnePoint (LiftedFrame.{v} n k a × LiftedEuclidean.{v} a))) =
      nativeFiniteValue.{u, v} n k a g x := by
  change (OrthogonalOperatorIndex.ι.{u, v} n k a).right
      ((frameSphereProductIso.{u, v} n k a).inv.right _) = _
  rw [frameSphereProductIso_inv_finite]
  rfl

/-- Infinity of the entire product compactification is the original native Hom basepoint. -/
theorem nativeOnePointArrow_infty (n k a : ℕ) :
    (nativeOnePointArrow.{u, v} n k a).right OnePoint.infty =
      (nativeHom.{u, v} n k).hom PUnit.unit :=
  mapOnePoint_infty (nativeOnePointArrow.{u, v} n k a)

/-- The original compactified generator, continuous for the genuine raw one-point topology. -/
def nativeRawOnePoint (n k a : ℕ) :
    C(OnePoint (LiftedFrame.{v} n k a × LiftedEuclidean.{v} a),
      (nativeHom.{u, v} n k).right) := by
  let _ : UCompactlyGeneratedSpace.{u}
      (OnePoint (LiftedFrame.{v} n k a × LiftedEuclidean.{v} a)) :=
    liftedFrameProductOnePoint_generated n k a
  let c := CompactlyGenerated.coreflectionCounitHomeoData.{u, v}
    (OnePoint (LiftedFrame.{v} n k a × LiftedEuclidean.{v} a))
  exact ⟨fun p => (nativeOnePointArrow n k a).right (c.1.symm p),
    (ConcreteCategory.hom (nativeOnePointArrow n k a).right).continuous.comp c.1.symm.continuous⟩

/-- The raw and native source compactifications use the same actual points. -/
theorem nativeRawOnePoint_eq_arrow (n k a : ℕ)
    (p : OnePoint (LiftedFrame.{v} n k a × LiftedEuclidean.{v} a)) :
    nativeRawOnePoint.{u, v} n k a p = (nativeOnePointArrow.{u, v} n k a).right p := by
  let _ : UCompactlyGeneratedSpace.{u}
      (OnePoint (LiftedFrame.{v} n k a × LiftedEuclidean.{v} a)) :=
    liftedFrameProductOnePoint_generated n k a
  let c := CompactlyGenerated.coreflectionCounitHomeoData.{u, v}
    (OnePoint (LiftedFrame.{v} n k a × LiftedEuclidean.{v} a))
  have hc : c.1.symm p = p :=
    (c.2 (c.1.symm p)).symm.trans (c.1.apply_symm_apply p)
  exact congrArg (nativeOnePointArrow.{u, v} n k a).right hc

theorem nativeRawOnePoint_infty (n k a : ℕ) :
    nativeRawOnePoint.{u, v} n k a OnePoint.infty = (nativeHom.{u, v} n k).hom PUnit.unit := by
  rw [nativeRawOnePoint_eq_arrow]
  exact nativeOnePointArrow_infty n k a

/-- The raw continuous source function retains every original finite coend generator. -/
theorem nativeRawOnePoint_finite (n k a : ℕ) (g : Frame n k a) (x : Euclidean a) :
    nativeRawOnePoint.{u, v} n k a
        ((((ULift.up g : LiftedFrame.{v} n k a), (ULift.up x : LiftedEuclidean.{v} a)) :
          OnePoint (LiftedFrame.{v} n k a × LiftedEuclidean.{v} a))) =
      nativeFiniteValue.{u, v} n k a g x := by
  rw [nativeRawOnePoint_eq_arrow]
  exact nativeOnePointArrow_finite n k a g x

/-- The actual native coend function is constant along all proved Thom
comparison fibers. -/
theorem nativeRawOnePoint_respects_kernel (n k a : ℕ)
    (p q : OnePoint (LiftedFrame.{v} n k a × LiftedEuclidean.{v} a))
    (hpq : liftedRawOnePointMap.{v} n k a p = liftedRawOnePointMap.{v} n k a q) :
    nativeRawOnePoint.{u, v} n k a p = nativeRawOnePoint.{u, v} n k a q := by
  induction p using OnePoint.rec with
  | infty =>
      induction q using OnePoint.rec with
      | infty => rfl
      | coe q => exact False.elim (OnePoint.infty_ne_coe _ hpq)
  | coe p =>
      induction q using OnePoint.rec with
      | infty => exact False.elim (OnePoint.coe_ne_infty _ hpq)
      | coe q =>
          rcases p with ⟨⟨g⟩, ⟨x⟩⟩
          rcases q with ⟨⟨h⟩, ⟨y⟩⟩
          rw [nativeRawOnePoint_finite, nativeRawOnePoint_finite]
          apply nativeFiniteValue_choice_independent
          exact congrArg ULift.down (OnePoint.coe_injective hpq)

/-- The exact lifted proper-comparison kernel quotient. -/
def liftedKernel (n k a : ℕ) : Setoid
    (OnePoint (LiftedFrame.{v} n k a × LiftedEuclidean.{v} a)) :=
  Setoid.ker (liftedRawOnePointMap n k a)

/-- The actual lifted quotient-to-Thom function induced by the proper map. -/
def liftedQuotientToThom (n k a : ℕ) :
    Quotient (liftedKernel.{v} n k a) → OnePoint (LiftedBundle.{v} n k) :=
  Quotient.lift (liftedRawOnePointMap n k a) (fun _ _ h => h)

/-- The lifted proper kernel quotient is homeomorphic to the original Thom compactification. -/
def liftedKernelThomHomeomorph (n k a : ℕ) (ha : a + n = k) :
    Quotient (liftedKernel.{v} n k a) ≃ₜ OnePoint (LiftedBundle.{v} n k) := by
  have hc : Continuous (liftedQuotientToThom.{v} n k a) :=
    Continuous.quotient_lift (liftedRawOnePointMap_continuous n k a) (fun _ _ h => h)
  have hb : Function.Bijective (liftedQuotientToThom.{v} n k a) := by
    constructor
    · intro p q h
      induction p using Quotient.inductionOn with
      | _ p =>
          induction q using Quotient.inductionOn with
          | _ q => exact Quotient.sound h
    · intro p
      obtain ⟨q, hq⟩ := liftedRawOnePointMap_surjective n k a ha p
      exact ⟨Quotient.mk (liftedKernel n k a) q, hq⟩
  exact Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective
    (liftedQuotientToThom n k a) hb) hc

/-- The raw continuous inverse descends the original coend generator
through the actual proper quotient. -/
def rawThomToNative (n k a : ℕ) (ha : a + n = k) :
    C(OnePoint (LiftedBundle.{v} n k), (nativeHom.{u, v} n k).right) := by
  let f : Quotient (liftedKernel.{v} n k a) → (nativeHom.{u, v} n k).right :=
    Quotient.lift (nativeRawOnePoint n k a) (nativeRawOnePoint_respects_kernel n k a)
  have hf : Continuous f := Continuous.quotient_lift
    (nativeRawOnePoint n k a).continuous (nativeRawOnePoint_respects_kernel n k a)
  let e := liftedKernelThomHomeomorph.{v} n k a ha
  exact ⟨f ∘ e.symm, hf.comp e.symm.continuous⟩

/-- The raw inverse retains every original compactified frame/vector generator. -/
theorem rawThomToNative_generator (n k a : ℕ) (ha : a + n = k)
    (p : OnePoint (LiftedFrame.{v} n k a × LiftedEuclidean.{v} a)) :
    rawThomToNative.{u, v} n k a ha (liftedRawOnePointMap n k a p) =
      nativeRawOnePoint.{u, v} n k a p := by
  let e := liftedKernelThomHomeomorph.{v} n k a ha
  have h : e (Quotient.mk (liftedKernel n k a) p) = liftedRawOnePointMap n k a p := rfl
  have hi : e.symm (liftedRawOnePointMap n k a p) = Quotient.mk (liftedKernel n k a) p := by
    rw [← h, e.symm_apply_apply]
  change (Quotient.lift (nativeRawOnePoint n k a)
    (nativeRawOnePoint_respects_kernel n k a)) (e.symm (liftedRawOnePointMap n k a p)) = _
  rw [hi]
  rfl

/-- The raw inverse fixes the original native Hom basepoint. -/
theorem rawThomToNative_infty (n k a : ℕ) (ha : a + n = k) :
    rawThomToNative.{u, v} n k a ha OnePoint.infty = (nativeHom.{u, v} n k).hom PUnit.unit := by
  have h := rawThomToNative_generator.{u, v} n k a ha OnePoint.infty
  exact h.trans (nativeRawOnePoint_infty n k a)

/-- The genuine pointed inverse for any actual residual-grade witness. -/
def partialThomToNative (n k a : ℕ) (ha : a + n = k) :
    thom.{u, v} n k ⟶ nativeHom.{u, v} n k := by
  let _ : UCompactlyGeneratedSpace.{u} (OnePoint (LiftedBundle.{v} n k)) :=
    liftedBundleOnePoint_generated n k
  let c := CompactlyGenerated.coreflectionCounitHomeoData.{u, v}
    (OnePoint (LiftedBundle.{v} n k))
  let f := rawThomToNative.{u, v} n k a ha
  let m : (thom.{u, v} n k).right ⟶ (nativeHom.{u, v} n k).right :=
    ConcreteCategory.ofHom ⟨f ∘ c.1, f.continuous.comp c.1.continuous⟩
  exact Under.homMk m (by
    apply ConcreteCategory.hom_ext
    intro t
    change f (c.1 OnePoint.infty) = (nativeHom.{u, v} n k).hom t
    rw [c.2 OnePoint.infty, rawThomToNative_infty]
    congr 1)

/-- The pointed inverse uses the actual raw continuous inverse on every original Thom point. -/
theorem partialThomToNative_eq_raw (n k a : ℕ) (ha : a + n = k)
    (p : OnePoint (LiftedBundle.{v} n k)) :
    (partialThomToNative.{u, v} n k a ha).right p = rawThomToNative.{u, v} n k a ha p := by
  let _ : UCompactlyGeneratedSpace.{u} (OnePoint (LiftedBundle.{v} n k)) :=
    liftedBundleOnePoint_generated n k
  let c := CompactlyGenerated.coreflectionCounitHomeoData.{u, v}
    (OnePoint (LiftedBundle.{v} n k))
  exact congrArg (rawThomToNative.{u, v} n k a ha) (c.2 p)

/-- All original finite generator values are recovered by the genuine continuous pointed inverse. -/
theorem partialThomToNative_finite (n k a : ℕ) (ha : a + n = k)
    (g : Frame n k a) (x : Euclidean a) :
    (partialThomToNative.{u, v} n k a ha).right
        (((ULift.up (rawMap n k a (g, x)) : LiftedBundle.{v} n k) :
          OnePoint (LiftedBundle.{v} n k))) = nativeFiniteValue.{u, v} n k a g x := by
  rw [partialThomToNative_eq_raw]
  have h := rawThomToNative_generator.{u, v} n k a ha
    ((((ULift.up g : LiftedFrame.{v} n k a), (ULift.up x : LiftedEuclidean.{v} a)) :
      OnePoint (LiftedFrame.{v} n k a × LiftedEuclidean.{v} a)))
  exact h.trans (nativeRawOnePoint_finite n k a g x)

/-- Maps from the actual original coend are determined by all original
finite matrix/sphere generators. -/
theorem nativeHom_hom_ext_finite {n k : ℕ} {T : PointedCGWH.{u, v}}
    {f g : nativeHom.{u, v} n k ⟶ T}
    (h : ∀ (a : ℕ) (r : Frame n k a) (x : Euclidean a),
      f.right (nativeFiniteValue.{u, v} n k a r x) =
        g.right (nativeFiniteValue.{u, v} n k a r x)) : f = g := by
  apply Enriched.weightedCoend.hom_ext (OrthogonalOperatorIndex.weight.{u, v} n k)
    orthogonalSphereFunctor.{u, v}
  intro a
  change OrthogonalOperatorIndex.ι.{u, v} n k a ≫ f =
    OrthogonalOperatorIndex.ι.{u, v} n k a ≫ g
  apply tensorPoint_hom_ext
  intro pr px
  rcases OrthogonalIndex.homPoint_cases pr with rfl | ⟨r, rfl⟩
  · simp only [pointPair_zero_left, zero_comp]
  rcases spherePoint_cases a px with rfl | ⟨x, rfl⟩
  · simp only [pointPair_zero_right, zero_comp]
  apply pointValue_injective T
  change f.right ((OrthogonalOperatorIndex.ι.{u, v} n k a).right
      (pointValue (pointPair (OrthogonalIndex.matrixPoint.{u, v} r) (spherePoint.{u, v} a x)))) =
    g.right ((OrthogonalOperatorIndex.ι.{u, v} n k a).right
      (pointValue (pointPair (OrthogonalIndex.matrixPoint.{u, v} r) (spherePoint.{u, v} a x))))
  rw [matrixSpherePoint_value]
  exact h a r x

/-- The inverse-after-forward law holds on the entire actual original weighted coend. -/
theorem nativeToThom_partial_inverse (n k a : ℕ) (ha : a + n = k) :
    nativeToThom.{u, v} n k ≫ partialThomToNative.{u, v} n k a ha = 𝟙 (nativeHom.{u, v} n k) := by
  apply nativeHom_hom_ext_finite
  intro b g x
  have hb : b = a := by have h := frame_dimension g; omega
  subst b
  change (partialThomToNative.{u, v} n k a ha).right
      ((nativeToThom.{u, v} n k).right (nativeFiniteValue n k a g x)) = _
  rw [nativeFiniteValue]
  rw [nativeToThom_finite, partialThomToNative_finite]
  rfl

/-- The forward on the entire original raw product compactification
is the actual lifted proper map. -/
theorem nativeToThom_nativeRawOnePoint (n k a : ℕ)
    (p : OnePoint (LiftedFrame.{v} n k a × LiftedEuclidean.{v} a)) :
    (nativeToThom.{u, v} n k).right (nativeRawOnePoint.{u, v} n k a p) =
      liftedRawOnePointMap.{v} n k a p := by
  rw [nativeRawOnePoint_eq_arrow]
  have h := ConcreteCategory.congr_hom
    (congrArg Under.Hom.right (nativeOnePointArrow_forward.{u, v} n k a)) p
  exact h

/-- The forward-after-inverse law is proved on every original Thom point
through the actual quotient. -/
theorem partial_inverse_nativeToThom (n k a : ℕ) (ha : a + n = k) :
    partialThomToNative.{u, v} n k a ha ≫ nativeToThom.{u, v} n k = 𝟙 (thom.{u, v} n k) := by
  apply Under.UnderMorphism.ext
  apply ConcreteCategory.hom_ext
  intro p
  change OnePoint (LiftedBundle.{v} n k) at p
  obtain ⟨q, hq⟩ := liftedRawOnePointMap_surjective.{v} n k a ha p
  change (nativeToThom.{u, v} n k).right ((partialThomToNative.{u, v} n k a ha).right p) = p
  rw [partialThomToNative_eq_raw, ← hq, rawThomToNative_generator,
    nativeToThom_nativeRawOnePoint]

/-- The original native coend is genuinely initial below the source dimension. -/
def nativeHomInitialBelow (n k : ℕ) (h : k < n) : IsInitial (nativeHom.{u, v} n k) :=
  IsInitial.ofUniqueHom (fun _ => 0) (fun T f => by
    apply nativeHom_hom_ext_finite
    intro a g x
    have hd := frame_dimension g
    omega)

/-- The actual empty complement-bundle Thom carrier is genuinely initial below the source. -/
def thomInitialBelow (n k : ℕ) (h : k < n) : IsInitial (thom.{u, v} n k) := by
  let _ : IsEmpty (ComplementBundle n k) := complementBundle_empty h
  let _ : IsEmpty (LiftedBundle.{v} n k) := inferInstance
  let _ : Subsingleton (OnePoint (LiftedBundle.{v} n k)) := inferInstance
  let _ : Subsingleton ((thom.{u, v} n k).right : Type v) := by
    change Subsingleton (OnePoint (LiftedBundle.{v} n k))
    infer_instance
  apply IsInitial.ofUniqueHom (fun _ => 0)
  intro T f
  apply Under.UnderMorphism.ext
  apply ConcreteCategory.hom_ext
  intro p
  have hp : p = (thom.{u, v} n k).hom PUnit.unit := Subsingleton.elim _ _
  rw [hp]
  exact (ConcreteCategory.congr_hom (Under.w f) PUnit.unit).trans
    (ConcreteCategory.congr_hom (Under.w (0 : thom.{u, v} n k ⟶ T)) PUnit.unit).symm

/-- The canonical genuine inverse uses the actual residual coefficient, and the true empty case. -/
def thomToNative (n k : ℕ) : thom.{u, v} n k ⟶ nativeHom.{u, v} n k :=
  if h : n ≤ k then partialThomToNative n k (k - n) (Nat.sub_add_cancel h) else 0

/-- Both original coend reconstruction laws hold with the actual residual-degree inverse. -/
theorem nativeToThom_inverse (n k : ℕ) :
    nativeToThom.{u, v} n k ≫ thomToNative.{u, v} n k = 𝟙 (nativeHom.{u, v} n k) := by
  by_cases h : n ≤ k
  · rw [thomToNative, dite_eq_left h]
    exact nativeToThom_partial_inverse n k (k - n) (Nat.sub_add_cancel h)
  · exact (nativeHomInitialBelow n k (Nat.lt_of_not_ge h)).hom_ext _ _

/-- The canonical inverse also reconstructs every point of the original inherited Thom carrier. -/
theorem thomToNative_inverse (n k : ℕ) :
    thomToNative.{u, v} n k ≫ nativeToThom.{u, v} n k = 𝟙 (thom.{u, v} n k) := by
  by_cases h : n ≤ k
  · rw [thomToNative, dite_eq_left h]
    exact partial_inverse_nativeToThom n k (k - n) (Nat.sub_add_cancel h)
  · exact (thomInitialBelow n k (Nat.lt_of_not_ge h)).hom_ext _ _

/-- The entire actual original weighted coend is the inherited matrix
complement-bundle Thom space. -/
def nativeCoendThomIso (n k : ℕ) : nativeHom.{u, v} n k ≅ thom.{u, v} n k where
  hom := nativeToThom n k
  inv := thomToNative n k
  hom_inv_id := nativeToThom_inverse n k
  inv_hom_id := thomToNative_inverse n k

/-- The two actual native comparison arrows are continuous for their original CGWH topologies. -/
theorem nativeCoendThom_both_continuous (n k : ℕ) :
    Continuous (ConcreteCategory.hom (nativeCoendThomIso.{u, v} n k).hom.right) ∧
      Continuous (ConcreteCategory.hom (nativeCoendThomIso.{u, v} n k).inv.right) :=
  ⟨(ConcreteCategory.hom (nativeCoendThomIso n k).hom.right).continuous,
    (ConcreteCategory.hom (nativeCoendThomIso n k).inv.right).continuous⟩

/-- All residual-grade choices give the same genuine continuous inverse arrow. -/
theorem partial_inverse_choice_independent (n k a b : ℕ) (ha : a + n = k) (hb : b + n = k) :
    partialThomToNative.{u, v} n k a ha = partialThomToNative.{u, v} n k b hb := by
  apply (cancel_mono (nativeCoendThomIso.{u, v} n k).hom).1
  change partialThomToNative.{u, v} n k a ha ≫ nativeToThom.{u, v} n k =
    partialThomToNative.{u, v} n k b hb ≫ nativeToThom.{u, v} n k
  rw [partial_inverse_nativeToThom, partial_inverse_nativeToThom]

/-- Any actual orthogonal completion recovers the same original coend element. -/
theorem thomToNative_completion (n k : ℕ) (h : n ≤ k) (p : ComplementBundle n k)
    (g : Frame n k (k - n)) (hg : finalPart g = p.1.1) :
    (thomToNative.{u, v} n k).right
        ((ULift.up p : LiftedBundle.{v} n k) : OnePoint (LiftedBundle.{v} n k)) =
      nativeFiniteValue.{u, v} n k (k - n) g (recover n k (k - n) (g, p)) := by
  rw [thomToNative, dite_eq_left h]
  have hp := rawMap_recover n k (k - n) g p hg
  have hi := partialThomToNative_finite.{u, v} n k (k - n) (Nat.sub_add_cancel h)
    g (recover n k (k - n) (g, p))
  have hinput := congrArg (fun q : ComplementBundle n k =>
    (partialThomToNative.{u, v} n k (k - n) (Nat.sub_add_cancel h)).right
      ((ULift.up q : LiftedBundle.{v} n k) : OnePoint (LiftedBundle.{v} n k))) hp
  exact hinput.symm.trans hi

/-- The full original raw-Hom balancing predicate, with both actual continuous faces. -/
abbrev FullBalanced (n k : ℕ) {T : PointedCGWH.{u, v}}
    (legs : ∀ a, OrthogonalIndex.hom.{u, v} (a + n) k ⊗
      PointedCGWH.orthogonalSphere.{u, v} a ⟶ T) : Prop :=
  ∀ a b, (α_ (OrthogonalIndex.hom.{u, v} (b + n) k) (OrthogonalIndex.hom.{u, v} a b)
    (PointedCGWH.orthogonalSphere.{u, v} a)).inv ≫
      (weightAction.{u, v} n k a b ⊗ₘ 𝟙 (PointedCGWH.orthogonalSphere.{u, v} a)) ≫ legs a =
    OrthogonalIndex.hom.{u, v} (b + n) k ◁ PointedCGWH.orthogonalSphereAction.{u, v} a b ≫ legs b

/-- Descend an actually proved balanced raw-Hom family through the original weighted coend. -/
def originalDesc (n k : ℕ) {T : PointedCGWH.{u, v}}
    (legs : ∀ a, OrthogonalIndex.hom.{u, v} (a + n) k ⊗
      PointedCGWH.orthogonalSphere.{u, v} a ⟶ T)
    (h : FullBalanced n k legs) : nativeHom.{u, v} n k ⟶ T :=
  Enriched.weightedCoend.desc (OrthogonalOperatorIndex.weight.{u, v} n k)
    orthogonalSphereFunctor.{u, v} legs (by
      intro a b
      change ((α_ (OrthogonalIndex.hom.{u, v} (b + n) k) (OrthogonalIndex.hom.{u, v} a b)
          (PointedCGWH.orthogonalSphere.{u, v} a)).inv ≫
        (weightAction.{u, v} n k a b ⊗ₘ 𝟙 (PointedCGWH.orthogonalSphere.{u, v} a))) ≫ legs a =
        (OrthogonalIndex.hom.{u, v} (b + n) k ◁
          ((β_ (OrthogonalIndex.hom.{u, v} a b) (PointedCGWH.orthogonalSphere.{u, v} a)).hom ≫
            sphereUncurry.{u, v} a b)) ≫ legs b
      rw [sphereUncurry_eq, ← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]
      exact h a b)

/-- The universal native descent retains every entire original characteristic map. -/
theorem originalDesc_generator (n k : ℕ) {T : PointedCGWH.{u, v}}
    (legs : ∀ a, OrthogonalIndex.hom.{u, v} (a + n) k ⊗
      PointedCGWH.orthogonalSphere.{u, v} a ⟶ T)
    (h : FullBalanced n k legs) (a : ℕ) :
    OrthogonalOperatorIndex.ι.{u, v} n k a ≫ originalDesc n k legs h = legs a :=
  Enriched.weightedCoend.ι_desc (OrthogonalOperatorIndex.weight.{u, v} n k)
    orthogonalSphereFunctor.{u, v} legs _ a

/-- Target postcomposition is the actual original full enriched-Hom whiskering map. -/
def bareTargetMap (m k l : ℕ) (t : OrthogonalMatrixHom k l) :
    OrthogonalIndex.hom.{u, v} m k ⟶ OrthogonalIndex.hom.{u, v} m l := by
  let _ : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
  let _ : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
    OrthogonalIndex.enrichedOrdinaryCategory.{u, v}
  exact eHomWhiskerLeft PointedCGWH.{u, v} m (show k ⟶ l from OrthogonalIndex.matrixPoint t)

/-- Source precomposition is the actual original full enriched-Hom whiskering map. -/
def bareSourceMap (m n k : ℕ) (s : OrthogonalMatrixHom m n) :
    OrthogonalIndex.hom.{u, v} n k ⟶ OrthogonalIndex.hom.{u, v} m k := by
  let _ : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
  let _ : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
    OrthogonalIndex.enrichedOrdinaryCategory.{u, v}
  exact eHomWhiskerRight PointedCGWH.{u, v} (show m ⟶ n from OrthogonalIndex.matrixPoint s) k

theorem bareTargetMap_matrixPoint (m k l : ℕ) (t : OrthogonalMatrixHom k l)
    (g : OrthogonalMatrixHom m k) :
    OrthogonalIndex.matrixPoint.{u, v} g ≫ bareTargetMap.{u, v} m k l t =
      OrthogonalIndex.matrixPoint.{u, v} (OrthogonalMatrixHom.comp g t) := by
  let _ : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
  let _ : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
    OrthogonalIndex.enrichedOrdinaryCategory.{u, v}
  let gg : m ⟶ k := OrthogonalIndex.matrixPoint.{u, v} g
  let tt : k ⟶ l := OrthogonalIndex.matrixPoint.{u, v} t
  have h := eHomEquiv_comp_eHomWhiskerLeft
    (V := PointedCGWH.{u, v}) (C := OrthogonalIndex) gg tt
  have hc : gg ≫ tt = OrthogonalIndex.matrixPoint.{u, v} (OrthogonalMatrixHom.comp g t) :=
    (OrthogonalIndex.enrichedCategory_comp g t).1
  exact h.trans (congrArg (eHomEquiv PointedCGWH.{u, v}) hc)

theorem bareSourceMap_matrixPoint (m n k : ℕ) (s : OrthogonalMatrixHom m n)
    (g : OrthogonalMatrixHom n k) :
    OrthogonalIndex.matrixPoint.{u, v} g ≫ bareSourceMap.{u, v} m n k s =
      OrthogonalIndex.matrixPoint.{u, v} (OrthogonalMatrixHom.comp s g) := by
  let _ : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
  let _ : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
    OrthogonalIndex.enrichedOrdinaryCategory.{u, v}
  let ss : m ⟶ n := OrthogonalIndex.matrixPoint.{u, v} s
  let gg : n ⟶ k := OrthogonalIndex.matrixPoint.{u, v} g
  have h := eHomEquiv_comp_eHomWhiskerRight
    (V := PointedCGWH.{u, v}) (C := OrthogonalIndex) ss gg
  have hc : ss ≫ gg = OrthogonalIndex.matrixPoint.{u, v} (OrthogonalMatrixHom.comp s g) :=
    (OrthogonalIndex.enrichedCategory_comp s g).1
  exact h.trans (congrArg (eHomEquiv PointedCGWH.{u, v}) hc)

/-- The original target-variable characteristic family on all coefficient objects. -/
def nativeTargetLeg (n k l a : ℕ) (t : OrthogonalMatrixHom k l) :
    OrthogonalIndex.hom.{u, v} (a + n) k ⊗ PointedCGWH.orthogonalSphere.{u, v} a ⟶
      nativeHom.{u, v} n l :=
  (bareTargetMap (a + n) k l t ▷ PointedCGWH.orthogonalSphere a) ≫
    OrthogonalOperatorIndex.ι n l a

/-- The original source-variable family precomposes the fixed source block only. -/
def nativeSourceLeg (m n k a : ℕ) (s : OrthogonalMatrixHom m n) :
    OrthogonalIndex.hom.{u, v} (a + n) k ⊗ PointedCGWH.orthogonalSphere.{u, v} a ⟶
      nativeHom.{u, v} m k :=
  (bareSourceMap (a + m) (a + n) k
    (OrthogonalMatrixHom.blockSum (OrthogonalMatrixHom.id a) s) ▷
      PointedCGWH.orthogonalSphere a) ≫ OrthogonalOperatorIndex.ι m k a

theorem nativeTargetLeg_matrixPoint (n k l a : ℕ) (t : OrthogonalMatrixHom k l)
    (g : Frame n k a) (x : Euclidean a) :
    pointPair (OrthogonalIndex.matrixPoint.{u, v} g) (spherePoint.{u, v} a x) ≫
        nativeTargetLeg.{u, v} n k l a t =
      pointPair (OrthogonalIndex.matrixPoint.{u, v} (targetFrame t g)) (spherePoint.{u, v} a x) ≫
        OrthogonalOperatorIndex.ι.{u, v} n l a := by
  rw [nativeTargetLeg, ← tensorHom_id, ← Category.assoc, pointPairNatural,
    Category.comp_id, bareTargetMap_matrixPoint]
  rfl

theorem nativeSourceLeg_matrixPoint (m n k a : ℕ) (s : OrthogonalMatrixHom m n)
    (g : Frame n k a) (x : Euclidean a) :
    pointPair (OrthogonalIndex.matrixPoint.{u, v} g) (spherePoint.{u, v} a x) ≫
        nativeSourceLeg.{u, v} m n k a s =
      pointPair (OrthogonalIndex.matrixPoint.{u, v} (sourceFrame s g)) (spherePoint.{u, v} a x) ≫
        OrthogonalOperatorIndex.ι.{u, v} m k a := by
  rw [nativeSourceLeg, ← tensorHom_id, ← Category.assoc, pointPairNatural,
    Category.comp_id, bareSourceMap_matrixPoint]
  rfl

theorem targetFrame_changeCoefficientAcross {n k l a b : ℕ} (t : OrthogonalMatrixHom k l)
    (g : Frame n k b) (r : OrthogonalMatrixHom a b) :
    targetFrame t (changeCoefficientAcross g r) =
      changeCoefficientAcross (targetFrame t g) r :=
  OrthogonalMatrixHom.comp_assoc (OrthogonalMatrixHom.blockSum r (OrthogonalMatrixHom.id n)) g t

theorem sourceFrame_changeCoefficientAcross {m n k a b : ℕ} (s : OrthogonalMatrixHom m n)
    (g : Frame n k b) (r : OrthogonalMatrixHom a b) :
    sourceFrame s (changeCoefficientAcross g r) =
      changeCoefficientAcross (sourceFrame s g) r := by
  apply frame_ext_parts
  · rw [sourceFrame_coefficientPart, changeCoefficientAcross_coefficientPart,
      changeCoefficientAcross_coefficientPart, sourceFrame_coefficientPart]
  · rw [sourceFrame_finalPart, changeCoefficientAcross_finalPart,
      changeCoefficientAcross_finalPart, sourceFrame_finalPart]

/-- Target postcomposition respects every original full continuous
coefficient balancing relation. -/
theorem nativeTargetLeg_balanced (n k l : ℕ) (t : OrthogonalMatrixHom k l) :
    FullBalanced n k (fun a => nativeTargetLeg.{u, v} n k l a t) := by
  intro a b
  apply tensorTriplePoint_hom_ext
  intro pg pr px
  dsimp only
  rw [balancing_weight_point (n := n) (k := k) (a := a) (b := b)
      (T := nativeHom.{u, v} n l) (fun c => nativeTargetLeg.{u, v} n k l c t) pg pr px,
    balancing_sphere_point (n := n) (k := k) (a := a) (b := b)
      (T := nativeHom.{u, v} n l) (fun c => nativeTargetLeg.{u, v} n k l c t) pg pr px]
  rcases OrthogonalIndex.homPoint_cases pg with rfl | ⟨g, rfl⟩
  · simp only [pointPair_zero_left, zero_comp]
  rcases OrthogonalIndex.homPoint_cases pr with rfl | ⟨r, rfl⟩
  · simp only [pointPair_zero_right, pointPair_zero_left, zero_comp]
  rcases spherePoint_cases a px with rfl | ⟨x, rfl⟩
  · simp only [pointPair_zero_right, zero_comp]
  rw [weight_matrixPoint, sphereAction_matrixPoint, nativeTargetLeg_matrixPoint,
    nativeTargetLeg_matrixPoint, targetFrame_changeCoefficientAcross]
  exact nativeGenerator_balanced n l a b (targetFrame t g) r x

/-- Source precomposition respects every full original continuous coefficient balancing relation. -/
theorem nativeSourceLeg_balanced (m n k : ℕ) (s : OrthogonalMatrixHom m n) :
    FullBalanced n k (fun a => nativeSourceLeg.{u, v} m n k a s) := by
  intro a b
  apply tensorTriplePoint_hom_ext
  intro pg pr px
  dsimp only
  rw [balancing_weight_point (n := n) (k := k) (a := a) (b := b)
      (T := nativeHom.{u, v} m k) (fun c => nativeSourceLeg.{u, v} m n k c s) pg pr px,
    balancing_sphere_point (n := n) (k := k) (a := a) (b := b)
      (T := nativeHom.{u, v} m k) (fun c => nativeSourceLeg.{u, v} m n k c s) pg pr px]
  rcases OrthogonalIndex.homPoint_cases pg with rfl | ⟨g, rfl⟩
  · simp only [pointPair_zero_left, zero_comp]
  rcases OrthogonalIndex.homPoint_cases pr with rfl | ⟨r, rfl⟩
  · simp only [pointPair_zero_right, pointPair_zero_left, zero_comp]
  rcases spherePoint_cases a px with rfl | ⟨x, rfl⟩
  · simp only [pointPair_zero_right, zero_comp]
  rw [weight_matrixPoint, sphereAction_matrixPoint, nativeSourceLeg_matrixPoint,
    nativeSourceLeg_matrixPoint, sourceFrame_changeCoefficientAcross]
  exact nativeGenerator_balanced m k a b (sourceFrame s g) r x

/-- The inherited Thom target homeomorphism is the original proper one-point transport. -/
def thomTargetIso (n k l : ℕ) (t : OrthogonalMatrixHom k l) :
    thom.{u, v} n k ≅ thom.{u, v} n l :=
  PointedCGWH.onePointHomeomorphOfHomeomorph
    ((Homeomorph.ulift (X := ComplementBundle n k)).trans
      ((targetHomeomorph t).trans (Homeomorph.ulift (X := ComplementBundle n l)).symm))

/-- The inherited Thom source homeomorphism is the original contravariant one-point transport. -/
def thomSourceIso (m n k : ℕ) (s : OrthogonalMatrixHom m n) :
    thom.{u, v} n k ≅ thom.{u, v} m k :=
  PointedCGWH.onePointHomeomorphOfHomeomorph
    ((Homeomorph.ulift (X := ComplementBundle n k)).trans
      ((sourceHomeomorph s).trans (Homeomorph.ulift (X := ComplementBundle m k)).symm))

theorem thomTargetIso_finite (n k l : ℕ) (t : OrthogonalMatrixHom k l)
    (p : ComplementBundle n k) :
    (thomTargetIso.{u, v} n k l t).hom.right
        ((ULift.up p : LiftedBundle.{v} n k) : OnePoint (LiftedBundle.{v} n k)) =
      ((ULift.up (targetMap t p) : LiftedBundle.{v} n l) : OnePoint (LiftedBundle.{v} n l)) := rfl

theorem thomSourceIso_finite (m n k : ℕ) (s : OrthogonalMatrixHom m n)
    (p : ComplementBundle n k) :
    (thomSourceIso.{u, v} m n k s).hom.right
        ((ULift.up p : LiftedBundle.{v} n k) : OnePoint (LiftedBundle.{v} n k)) =
      ((ULift.up (sourceMap s p) : LiftedBundle.{v} m k) : OnePoint (LiftedBundle.{v} m k)) := rfl

/-- The forward retains the exact original finite coend-value definition. -/
theorem nativeToThom_nativeFiniteValue (n k a : ℕ) (g : Frame n k a) (x : Euclidean a) :
    (nativeToThom.{u, v} n k).right (nativeFiniteValue.{u, v} n k a g x) =
      ((ULift.up (rawMap n k a (g, x)) : LiftedBundle.{v} n k) :
        OnePoint (LiftedBundle.{v} n k)) :=
  nativeToThom_finite.{u, v} n k a g x

/-- Any actual residual-grade inverse is the canonical proved inverse arrow. -/
theorem partial_inverse_eq_canonical (n k a : ℕ) (ha : a + n = k) :
    partialThomToNative.{u, v} n k a ha = thomToNative.{u, v} n k := by
  apply (cancel_mono (nativeCoendThomIso.{u, v} n k).hom).1
  change partialThomToNative.{u, v} n k a ha ≫ nativeToThom.{u, v} n k =
    thomToNative.{u, v} n k ≫ nativeToThom.{u, v} n k
  rw [partial_inverse_nativeToThom, thomToNative_inverse]

/-- The canonical inverse retains every original finite frame, in its actual coefficient degree. -/
theorem thomToNative_finite_frame (n k a : ℕ) (g : Frame n k a) (x : Euclidean a) :
    (thomToNative.{u, v} n k).right
        (((ULift.up (rawMap n k a (g, x)) : LiftedBundle.{v} n k) :
          OnePoint (LiftedBundle.{v} n k))) = nativeFiniteValue.{u, v} n k a g x := by
  have ha := frame_dimension g
  have h := congrArg (fun f : thom.{u, v} n k ⟶ nativeHom.{u, v} n k =>
    f.right ((ULift.up (rawMap n k a (g, x)) : LiftedBundle.{v} n k) :
      OnePoint (LiftedBundle.{v} n k))) (partial_inverse_eq_canonical.{u, v} n k a ha)
  exact h.symm.trans (partialThomToNative_finite n k a ha g x)

/-- The canonical target map through the proved native Thom comparison.
Its entire original postcomposition family is proved below, so its meaning
does not depend on a chosen presentation or completion. -/
def nativeTargetMap (n k l : ℕ) (t : OrthogonalMatrixHom k l) :
    nativeHom.{u, v} n k ⟶ nativeHom.{u, v} n l :=
  nativeToThom n k ≫ (thomTargetIso n k l t).hom ≫ thomToNative n l

/-- The canonical source map through the proved comparison, retaining
the original coefficient-first source family in the theorem below. -/
def nativeSourceMap (m n k : ℕ) (s : OrthogonalMatrixHom m n) :
    nativeHom.{u, v} n k ⟶ nativeHom.{u, v} m k :=
  nativeToThom n k ≫ (thomSourceIso m n k s).hom ≫ thomToNative m k

theorem nativeTargetMap_finite (n k l a : ℕ) (t : OrthogonalMatrixHom k l)
    (g : Frame n k a) (x : Euclidean a) :
    (nativeTargetMap.{u, v} n k l t).right (nativeFiniteValue.{u, v} n k a g x) =
      nativeFiniteValue.{u, v} n l a (targetFrame t g) x := by
  change (thomToNative.{u, v} n l).right
    ((thomTargetIso.{u, v} n k l t).hom.right
      ((nativeToThom.{u, v} n k).right (nativeFiniteValue.{u, v} n k a g x))) = _
  have h1 := congrArg (fun p : (thom.{u, v} n k).right =>
    (thomToNative.{u, v} n l).right ((thomTargetIso.{u, v} n k l t).hom.right p))
      (nativeToThom_nativeFiniteValue.{u, v} n k a g x)
  have h2 := congrArg (thomToNative.{u, v} n l).right
    (thomTargetIso_finite.{u, v} n k l t (rawMap n k a (g, x)))
  have h3 := congrArg (fun p : ComplementBundle n l => (thomToNative.{u, v} n l).right
    ((ULift.up p : LiftedBundle.{v} n l) : OnePoint (LiftedBundle.{v} n l)))
      (rawMap_target_naturality t g x).symm
  exact h1.trans (h2.trans (h3.trans (thomToNative_finite_frame n l a (targetFrame t g) x)))

theorem nativeSourceMap_finite (m n k a : ℕ) (s : OrthogonalMatrixHom m n)
    (g : Frame n k a) (x : Euclidean a) :
    (nativeSourceMap.{u, v} m n k s).right (nativeFiniteValue.{u, v} n k a g x) =
      nativeFiniteValue.{u, v} m k a (sourceFrame s g) x := by
  change (thomToNative.{u, v} m k).right
    ((thomSourceIso.{u, v} m n k s).hom.right
      ((nativeToThom.{u, v} n k).right (nativeFiniteValue.{u, v} n k a g x))) = _
  have h1 := congrArg (fun p : (thom.{u, v} n k).right =>
    (thomToNative.{u, v} m k).right ((thomSourceIso.{u, v} m n k s).hom.right p))
      (nativeToThom_nativeFiniteValue.{u, v} n k a g x)
  have h2 := congrArg (thomToNative.{u, v} m k).right
    (thomSourceIso_finite.{u, v} m n k s (rawMap n k a (g, x)))
  have h3 := congrArg (fun p : ComplementBundle m k => (thomToNative.{u, v} m k).right
    ((ULift.up p : LiftedBundle.{v} m k) : OnePoint (LiftedBundle.{v} m k)))
      (rawMap_source_naturality s g x).symm
  exact h1.trans (h2.trans (h3.trans (thomToNative_finite_frame m k a (sourceFrame s g) x)))

/-- The entire target characteristic family is the original full-Hom postcomposition family. -/
theorem nativeTargetMap_generator (n k l a : ℕ) (t : OrthogonalMatrixHom k l) :
    OrthogonalOperatorIndex.ι.{u, v} n k a ≫ nativeTargetMap.{u, v} n k l t =
      nativeTargetLeg.{u, v} n k l a t := by
  apply tensorPoint_hom_ext
  intro pg px
  rcases OrthogonalIndex.homPoint_cases pg with rfl | ⟨g, rfl⟩
  · simp only [pointPair_zero_left, zero_comp]
  rcases spherePoint_cases a px with rfl | ⟨x, rfl⟩
  · simp only [pointPair_zero_right, zero_comp]
  apply pointValue_injective _
  have h := congrArg pointValue (nativeTargetLeg_matrixPoint.{u, v} n k l a t g x)
  rw [pointValue_comp, pointValue_comp, matrixSpherePoint_value,
    matrixSpherePoint_value] at h
  rw [pointValue_comp, pointValue_comp]
  change (nativeTargetMap.{u, v} n k l t).right
      ((OrthogonalOperatorIndex.ι.{u, v} n k a).right
        (pointValue (pointPair (OrthogonalIndex.matrixPoint.{u, v} g)
          (spherePoint.{u, v} a x)))) =
    (nativeTargetLeg.{u, v} n k l a t).right
      (pointValue (pointPair (OrthogonalIndex.matrixPoint.{u, v} g) (spherePoint.{u, v} a x)))
  rw [matrixSpherePoint_value]
  exact (nativeTargetMap_finite.{u, v} n k l a t g x).trans h.symm

/-- The entire source family is actual precomposition by the original fixed source block. -/
theorem nativeSourceMap_generator (m n k a : ℕ) (s : OrthogonalMatrixHom m n) :
    OrthogonalOperatorIndex.ι.{u, v} n k a ≫ nativeSourceMap.{u, v} m n k s =
      nativeSourceLeg.{u, v} m n k a s := by
  apply tensorPoint_hom_ext
  intro pg px
  rcases OrthogonalIndex.homPoint_cases pg with rfl | ⟨g, rfl⟩
  · simp only [pointPair_zero_left, zero_comp]
  rcases spherePoint_cases a px with rfl | ⟨x, rfl⟩
  · simp only [pointPair_zero_right, zero_comp]
  apply pointValue_injective _
  have h := congrArg pointValue (nativeSourceLeg_matrixPoint.{u, v} m n k a s g x)
  rw [pointValue_comp, pointValue_comp, matrixSpherePoint_value,
    matrixSpherePoint_value] at h
  rw [pointValue_comp, pointValue_comp]
  change (nativeSourceMap.{u, v} m n k s).right
      ((OrthogonalOperatorIndex.ι.{u, v} n k a).right
        (pointValue (pointPair (OrthogonalIndex.matrixPoint.{u, v} g)
          (spherePoint.{u, v} a x)))) =
    (nativeSourceLeg.{u, v} m n k a s).right
      (pointValue (pointPair (OrthogonalIndex.matrixPoint.{u, v} g) (spherePoint.{u, v} a x)))
  rw [matrixSpherePoint_value]
  exact (nativeSourceMap_finite.{u, v} m n k a s g x).trans h.symm

/-- The full original target-generator family determines the native target map uniquely. -/
theorem nativeTargetMap_unique (n k l : ℕ) (t : OrthogonalMatrixHom k l)
    (f : nativeHom.{u, v} n k ⟶ nativeHom.{u, v} n l)
    (h : ∀ a, OrthogonalOperatorIndex.ι.{u, v} n k a ≫ f = nativeTargetLeg n k l a t) :
    f = nativeTargetMap n k l t := by
  apply nativeHom_hom_ext_finite
  intro a g x
  have hf := ConcreteCategory.congr_hom (congrArg Under.Hom.right (h a))
    (finiteGeneratorInput.{u, v} n k a g x)
  have hn := ConcreteCategory.congr_hom
    (congrArg Under.Hom.right (nativeTargetMap_generator.{u, v} n k l a t))
    (finiteGeneratorInput.{u, v} n k a g x)
  exact hf.trans hn.symm

/-- The complete original coefficient-first source family determines the source map uniquely. -/
theorem nativeSourceMap_unique (m n k : ℕ) (s : OrthogonalMatrixHom m n)
    (f : nativeHom.{u, v} n k ⟶ nativeHom.{u, v} m k)
    (h : ∀ a, OrthogonalOperatorIndex.ι.{u, v} n k a ≫ f = nativeSourceLeg m n k a s) :
    f = nativeSourceMap m n k s := by
  apply nativeHom_hom_ext_finite
  intro a g x
  have hf := ConcreteCategory.congr_hom (congrArg Under.Hom.right (h a))
    (finiteGeneratorInput.{u, v} n k a g x)
  have hn := ConcreteCategory.congr_hom
    (congrArg Under.Hom.right (nativeSourceMap_generator.{u, v} m n k a s))
    (finiteGeneratorInput.{u, v} n k a g x)
  exact hf.trans hn.symm

/-- Naturality in the target holds as equality of entire original native coend arrows. -/
theorem nativeCoendThom_target_naturality (n k l : ℕ) (t : OrthogonalMatrixHom k l) :
    nativeTargetMap.{u, v} n k l t ≫ nativeToThom.{u, v} n l =
      nativeToThom.{u, v} n k ≫ (thomTargetIso.{u, v} n k l t).hom := by
  apply nativeHom_hom_ext_finite
  intro a g x
  change (nativeToThom.{u, v} n l).right
      ((nativeTargetMap.{u, v} n k l t).right (nativeFiniteValue n k a g x)) =
    (thomTargetIso.{u, v} n k l t).hom.right
      ((nativeToThom.{u, v} n k).right (nativeFiniteValue n k a g x))
  have h1 := congrArg (nativeToThom.{u, v} n l).right
    (nativeTargetMap_finite.{u, v} n k l a t g x)
  have h2 := nativeToThom_nativeFiniteValue.{u, v} n l a (targetFrame t g) x
  have h3 := congrArg (fun p : ComplementBundle n l =>
    ((ULift.up p : LiftedBundle.{v} n l) : OnePoint (LiftedBundle.{v} n l)))
      (rawMap_target_naturality t g x)
  have h4 := (thomTargetIso_finite.{u, v} n k l t (rawMap n k a (g, x))).symm
  have h5 := congrArg (thomTargetIso.{u, v} n k l t).hom.right
    (nativeToThom_nativeFiniteValue.{u, v} n k a g x).symm
  exact h1.trans (h2.trans (h3.trans (h4.trans h5)))

/-- Naturality in the source retains the original inverse-precomposition variance. -/
theorem nativeCoendThom_source_naturality (m n k : ℕ) (s : OrthogonalMatrixHom m n) :
    nativeSourceMap.{u, v} m n k s ≫ nativeToThom.{u, v} m k =
      nativeToThom.{u, v} n k ≫ (thomSourceIso.{u, v} m n k s).hom := by
  apply nativeHom_hom_ext_finite
  intro a g x
  change (nativeToThom.{u, v} m k).right
      ((nativeSourceMap.{u, v} m n k s).right (nativeFiniteValue n k a g x)) =
    (thomSourceIso.{u, v} m n k s).hom.right
      ((nativeToThom.{u, v} n k).right (nativeFiniteValue n k a g x))
  have h1 := congrArg (nativeToThom.{u, v} m k).right
    (nativeSourceMap_finite.{u, v} m n k a s g x)
  have h2 := nativeToThom_nativeFiniteValue.{u, v} m k a (sourceFrame s g) x
  have h3 := congrArg (fun p : ComplementBundle m k =>
    ((ULift.up p : LiftedBundle.{v} m k) : OnePoint (LiftedBundle.{v} m k)))
      (rawMap_source_naturality s g x)
  have h4 := (thomSourceIso_finite.{u, v} m n k s (rawMap n k a (g, x))).symm
  have h5 := congrArg (thomSourceIso.{u, v} m n k s).hom.right
    (nativeToThom_nativeFiniteValue.{u, v} n k a g x).symm
  exact h1.trans (h2.trans (h3.trans (h4.trans h5)))

/-- The genuine continuous inverse is natural for actual target postcomposition. -/
theorem nativeCoendThom_inverse_target_naturality (n k l : ℕ) (t : OrthogonalMatrixHom k l) :
    (thomTargetIso.{u, v} n k l t).hom ≫ thomToNative.{u, v} n l =
      thomToNative.{u, v} n k ≫ nativeTargetMap.{u, v} n k l t := by
  apply (cancel_mono (nativeCoendThomIso.{u, v} n l).hom).1
  change ((thomTargetIso.{u, v} n k l t).hom ≫ thomToNative.{u, v} n l) ≫
      nativeToThom.{u, v} n l =
    (thomToNative.{u, v} n k ≫ nativeTargetMap.{u, v} n k l t) ≫ nativeToThom.{u, v} n l
  rw [Category.assoc, thomToNative_inverse, Category.comp_id, Category.assoc,
    nativeCoendThom_target_naturality, ← Category.assoc, thomToNative_inverse, Category.id_comp]

/-- The genuine inverse is natural for actual source precomposition on the original coend. -/
theorem nativeCoendThom_inverse_source_naturality (m n k : ℕ) (s : OrthogonalMatrixHom m n) :
    (thomSourceIso.{u, v} m n k s).hom ≫ thomToNative.{u, v} m k =
      thomToNative.{u, v} n k ≫ nativeSourceMap.{u, v} m n k s := by
  apply (cancel_mono (nativeCoendThomIso.{u, v} m k).hom).1
  change ((thomSourceIso.{u, v} m n k s).hom ≫ thomToNative.{u, v} m k) ≫
      nativeToThom.{u, v} m k =
    (thomToNative.{u, v} n k ≫ nativeSourceMap.{u, v} m n k s) ≫ nativeToThom.{u, v} m k
  rw [Category.assoc, thomToNative_inverse, Category.comp_id, Category.assoc,
    nativeCoendThom_source_naturality, ← Category.assoc, thomToNative_inverse, Category.id_comp]

/-- The actual positive block crossing in the original right sphere inclusion is retained. -/
theorem nu_spherePoint (n a : ℕ) (x : Euclidean a) :
    spherePoint.{u, v} a x ≫ OrthogonalOperatorIndex.nu.{u, v} n a =
      pointPair (OrthogonalIndex.matrixPoint.{u, v} (OrthogonalIndex.blockSwap a n))
        (spherePoint.{u, v} a x) ≫ OrthogonalOperatorIndex.ι.{u, v} n (n + a) a := by
  let _ : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
  let _ : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
  let _ : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
    OrthogonalIndex.enrichedOrdinaryCategory.{u, v}
  let _ : SymmetricCategory OrthogonalIndex := OrthogonalIndex.symmetricCategory.{u, v}
  change spherePoint.{u, v} a x ≫ (λ_ (PointedCGWH.orthogonalSphere.{u, v} a)).inv ≫
    (OrthogonalIndex.matrixPoint.{u, v} (OrthogonalIndex.blockSwap a n) ⊗ₘ
      𝟙 (PointedCGWH.orthogonalSphere.{u, v} a)) ≫
        OrthogonalOperatorIndex.ι.{u, v} n (n + a) a = _
  rw [pointPair_factor_left]
  simp only [Category.assoc]

/-- The actual original right inclusion has the positive-crossing Thom finite-point formula. -/
theorem nativeCoendThom_nu_finite (n a : ℕ) (x : Euclidean a) :
    (nativeToThom.{u, v} n (n + a)).right
        ((OrthogonalOperatorIndex.nu.{u, v} n a).right
          (((ULift.up x : LiftedEuclidean.{v} a) : OnePoint (LiftedEuclidean.{v} a)))) =
      ((ULift.up (rawMap n (n + a) a (OrthogonalIndex.blockSwap a n, x)) :
        LiftedBundle.{v} n (n + a)) : OnePoint (LiftedBundle.{v} n (n + a))) := by
  have h := congrArg pointValue (nu_spherePoint.{u, v} n a x)
  rw [pointValue_comp, spherePoint_value, pointValue_comp, matrixSpherePoint_value] at h
  have hv : (OrthogonalOperatorIndex.nu.{u, v} n a).right
      (((ULift.up x : LiftedEuclidean.{v} a) : OnePoint (LiftedEuclidean.{v} a))) =
      nativeFiniteValue.{u, v} n (n + a) a (OrthogonalIndex.blockSwap a n) x := h
  exact (congrArg (nativeToThom.{u, v} n (n + a)).right hv).trans
    (nativeToThom_nativeFiniteValue n (n + a) a (OrthogonalIndex.blockSwap a n) x)

/-- The actual original right-oriented native free enriched functor. -/
abbrev nativeFree (n : ℕ) (X : PointedCGWH.{u, v}) :
    EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v} :=
  EnrichedFunctorCat.Free.object (V := PointedCGWH.{u, v})
    (OrthogonalOperatorIndex.ofIndex.{u, v} n) X

/-- The complete actual evaluated free component, with coefficient `X` first. -/
abbrev nativeFreeValue (n k : ℕ) (X : PointedCGWH.{u, v}) : PointedCGWH.{u, v} :=
  (nativeFree n X).toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex k)

/-- The actual original free/evaluation component is the coefficient-first Thom tensor. -/
def nativeFreeThomComponentIso (n k : ℕ) (X : PointedCGWH.{u, v}) :
    nativeFreeValue.{u, v} n k X ≅ X ⊗ thom.{u, v} n k :=
  tensorIso (Iso.refl X) (nativeCoendThomIso n k)

/-- The actual Free component comparison is the original coefficient-first whiskering. -/
theorem nativeFreeThomComponentIso_hom (n k : ℕ) (X : PointedCGWH.{u, v}) :
    (nativeFreeThomComponentIso.{u, v} n k X).hom = X ◁ nativeToThom.{u, v} n k := by
  rw [nativeFreeThomComponentIso, tensorIso_hom]
  exact id_tensorHom X (nativeToThom n k)

/-- The original full coefficient inclusion into the actual native Free component. -/
def nativeFreeCoefficientInclusion (n k a : ℕ) (X : PointedCGWH.{u, v}) :
    X ⊗ (OrthogonalIndex.hom.{u, v} (a + n) k ⊗ PointedCGWH.orthogonalSphere.{u, v} a) ⟶
      nativeFreeValue.{u, v} n k X :=
  X ◁ OrthogonalOperatorIndex.ι n k a

/-- The corresponding genuine proper Thom inclusion keeps every continuous frame coefficient. -/
def thomFreeCoefficientInclusion (n k a : ℕ) (X : PointedCGWH.{u, v}) :
    X ⊗ (OrthogonalIndex.hom.{u, v} (a + n) k ⊗ PointedCGWH.orthogonalSphere.{u, v} a) ⟶
      X ⊗ thom.{u, v} n k :=
  X ◁ generatorThomLeg n k a

/-- The comparison preserves the entire original coefficient inclusion function. -/
theorem nativeFreeThom_coefficient_inclusion (n k a : ℕ) (X : PointedCGWH.{u, v}) :
    nativeFreeCoefficientInclusion.{u, v} n k a X ≫ (nativeFreeThomComponentIso n k X).hom =
      thomFreeCoefficientInclusion.{u, v} n k a X := by
  rw [nativeFreeThomComponentIso_hom]
  change (X ◁ OrthogonalOperatorIndex.ι.{u, v} n k a) ≫
    (X ◁ nativeToThom.{u, v} n k) = X ◁ generatorThomLeg.{u, v} n k a
  rw [← whiskerLeft_comp, nativeToThom_generator]

/-- Both reconstructed Free components use the actual native comparison arrows. -/
theorem nativeFreeThom_inverse_laws (n k : ℕ) (X : PointedCGWH.{u, v}) :
    (nativeFreeThomComponentIso.{u, v} n k X).hom ≫
        (nativeFreeThomComponentIso n k X).inv = 𝟙 (nativeFreeValue n k X) ∧
      (nativeFreeThomComponentIso n k X).inv ≫
        (nativeFreeThomComponentIso n k X).hom = 𝟙 (X ⊗ thom n k) :=
  ⟨(nativeFreeThomComponentIso n k X).hom_inv_id,
    (nativeFreeThomComponentIso n k X).inv_hom_id⟩

/-- The component comparison is natural for the actual original free coefficient morphism. -/
theorem nativeFreeThom_coefficient_naturality (n k : ℕ)
    {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    EnrichedFunctorCat.component
        (EnrichedFunctorCat.Free.coefficientMap (OrthogonalOperatorIndex.ofIndex.{u, v} n) f)
        (OrthogonalOperatorIndex.ofIndex k) ≫ (nativeFreeThomComponentIso n k Y).hom =
      (nativeFreeThomComponentIso n k X).hom ≫ (f ▷ thom n k) := by
  rw [EnrichedFunctorCat.Free.coefficientMap_component]
  rw [nativeFreeThomComponentIso_hom, nativeFreeThomComponentIso_hom]
  change (f ▷ nativeHom.{u, v} n k) ≫ (Y ◁ nativeToThom.{u, v} n k) =
    (X ◁ nativeToThom.{u, v} n k) ≫ (f ▷ thom.{u, v} n k)
  exact (whisker_exchange f (nativeToThom n k)).symm

/-- The right tensor value comparison, natural in every original coefficient object. -/
def tensorThomValueIso (n k : ℕ) :
    tensorRight (nativeHom.{u, v} n k) ≅ tensorRight (thom.{u, v} n k) :=
  (tensoringRight PointedCGWH.{u, v}).mapIso (nativeCoendThomIso n k)

/-- The actual original Free factory/evaluation composite, as a whole coefficient functor. -/
def nativeFreeThomValueIso (n k : ℕ) :
    EnrichedFunctorCat.Free.functor (V := PointedCGWH.{u, v})
        (OrthogonalOperatorIndex.ofIndex.{u, v} n) ⋙
      EnrichedFunctorCat.evaluation (OrthogonalOperatorIndex.ofIndex.{u, v} k) ≅
        tensorRight (thom.{u, v} n k) :=
  EnrichedFunctorCat.Free.ValueFunctor.freeValueIso
    (OrthogonalOperatorIndex.ofIndex.{u, v} n) (OrthogonalOperatorIndex.ofIndex.{u, v} k) ≪≫
      tensorThomValueIso n k

/-- The original operator identity determines the actual Thom unit point. -/
def thomUnitPoint (n : ℕ) : 𝟙_ PointedCGWH.{u, v} ⟶ thom.{u, v} n n :=
  eId PointedCGWH.{u, v} (OrthogonalOperatorIndex.ofIndex.{u, v} n) ≫ nativeToThom n n

/-- The original native Free coefficient-unit inclusion. -/
def nativeFreeUnit (n : ℕ) (X : PointedCGWH.{u, v}) : X ⟶ nativeFreeValue.{u, v} n n X :=
  (ρ_ X).inv ≫ X ◁ eId PointedCGWH.{u, v} (OrthogonalOperatorIndex.ofIndex.{u, v} n)

/-- The genuine Thom coefficient unit is derived from that same original operator identity. -/
def thomFreeUnit (n : ℕ) (X : PointedCGWH.{u, v}) : X ⟶ X ⊗ thom.{u, v} n n :=
  (ρ_ X).inv ≫ X ◁ thomUnitPoint n

/-- The actual native Free unit and Thom unit commute with the complete component comparison. -/
theorem nativeFreeThom_unit_square (n : ℕ) (X : PointedCGWH.{u, v}) :
    nativeFreeUnit.{u, v} n X ≫ (nativeFreeThomComponentIso n n X).hom = thomFreeUnit n X := by
  rw [nativeFreeThomComponentIso_hom]
  change (ρ_ X).inv ≫
    (X ◁ eId PointedCGWH.{u, v} (OrthogonalOperatorIndex.ofIndex.{u, v} n)) ≫
    (X ◁ nativeToThom.{u, v} n n) =
    (ρ_ X).inv ≫ X ◁
      (eId PointedCGWH.{u, v} (OrthogonalOperatorIndex.ofIndex.{u, v} n) ≫ nativeToThom n n)
  rw [whiskerLeft_comp]

/-- The original extension action, expressed on the proved Thom component. -/
def thomExtensionComponent (n k : ℕ) (X : PointedCGWH.{u, v})
    (F : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})
    (f : X ⟶ F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex n)) :
    X ⊗ thom.{u, v} n k ⟶ F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex k) :=
  (nativeFreeThomComponentIso n k X).inv ≫
    EnrichedFunctorCat.Free.extensionComponent (OrthogonalOperatorIndex.ofIndex n) X F f
      (OrthogonalOperatorIndex.ofIndex k)

/-- The complete original extension/evaluation component square uses actual Free action maps. -/
theorem nativeFreeThom_extension_square (n k : ℕ) (X : PointedCGWH.{u, v})
    (F : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})
    (f : X ⟶ F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex n)) :
    (nativeFreeThomComponentIso n k X).hom ≫ thomExtensionComponent n k X F f =
      EnrichedFunctorCat.Free.extensionComponent (OrthogonalOperatorIndex.ofIndex n) X F f
        (OrthogonalOperatorIndex.ofIndex k) := by
  rw [thomExtensionComponent, Iso.hom_inv_id_assoc]

/-- The original evaluation-adjunction triangle commutes on the genuine Thom coefficient unit. -/
theorem thomExtension_unit_evaluation (n : ℕ) (X : PointedCGWH.{u, v})
    (F : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})
    (f : X ⟶ F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex n)) :
    thomFreeUnit n X ≫ thomExtensionComponent n n X F f = f := by
  rw [← nativeFreeThom_unit_square, Category.assoc, nativeFreeThom_extension_square]
  have h := EnrichedFunctorCat.Free.evaluate_extend
    (OrthogonalOperatorIndex.ofIndex.{u, v} n) X F f
  rw [EnrichedFunctorCat.Free.evaluate, EnrichedFunctorCat.Free.extend_component] at h
  exact h

/-- Every original free-functor transformation has an actual Thom component. -/
def thomComponent (n k : ℕ) (X : PointedCGWH.{u, v})
    (F : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})
    (t : nativeFree n X ⟶ F) :
    X ⊗ thom.{u, v} n k ⟶ F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex k) :=
  (nativeFreeThomComponentIso n k X).inv ≫
    EnrichedFunctorCat.component t (OrthogonalOperatorIndex.ofIndex k)

/-- The actual coefficient evaluation on Thom components. -/
def thomEvaluation (n : ℕ) (X : PointedCGWH.{u, v})
    (F : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})
    (t : nativeFree n X ⟶ F) : X ⟶ F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex n) :=
  thomFreeUnit n X ≫ thomComponent n n X F t

/-- The Thom evaluation function is exactly the original chosen Free evaluation function. -/
theorem thomEvaluation_eq_original (n : ℕ) (X : PointedCGWH.{u, v})
    (F : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})
    (t : nativeFree n X ⟶ F) :
    thomEvaluation n X F t =
      EnrichedFunctorCat.Free.evaluate (OrthogonalOperatorIndex.ofIndex n) X F t := by
  rw [thomEvaluation, thomComponent, ← nativeFreeThom_unit_square]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rfl

/-- The chosen original Free/evaluation adjunction has the same actual Thom evaluation square. -/
theorem nativeFreeThom_adjunction_square (n : ℕ) (X : PointedCGWH.{u, v})
    (F : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})
    (t : nativeFree n X ⟶ F) :
    (EnrichedFunctorCat.Free.adjunction (V := PointedCGWH.{u, v})
      (OrthogonalOperatorIndex.ofIndex.{u, v} n)).homEquiv X F t = thomEvaluation n X F t := by
  rw [EnrichedFunctorCat.Free.adjunction_homEquiv, thomEvaluation_eq_original]
  rfl

/-- The original adjunction reconstructs every Thom component from its exact
coefficient evaluation. -/
theorem thomComponent_reconstruction (n k : ℕ) (X : PointedCGWH.{u, v})
    (F : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})
    (t : nativeFree n X ⟶ F) :
    thomComponent n k X F t = thomExtensionComponent n k X F (thomEvaluation n X F t) := by
  rw [thomEvaluation_eq_original]
  change (nativeFreeThomComponentIso n k X).inv ≫
      EnrichedFunctorCat.component t (OrthogonalOperatorIndex.ofIndex k) =
    (nativeFreeThomComponentIso n k X).inv ≫
      EnrichedFunctorCat.Free.extensionComponent (OrthogonalOperatorIndex.ofIndex n) X F
        (EnrichedFunctorCat.Free.evaluate (OrthogonalOperatorIndex.ofIndex n) X F t)
          (OrthogonalOperatorIndex.ofIndex k)
  rw [EnrichedFunctorCat.Free.reconstruct_component]

end CategoryTheory.Spectra.OrthogonalCoendThom
