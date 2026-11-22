/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexBoundaryRLPRecognition
import MathlibExt.Topology.Category.CGWH.StrictFiberLanding
import MathlibExt.Topology.Category.PointedCGWH.FiberToLoop
import MathlibExt.Topology.Homotopy.TopCat.Singular.SingularFiberIso
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.HornRLPSingularRLP
import MathlibExt.Topology.Category.PointedCGWH.LoopHomotopyComparison

/-!
# The original chosen Serre fiber gives every component of native loop weakness

The actual native CGWH strict fiber over a chosen point is identified with
the ordinary topological point fiber, then with the strict fiber of the
original singular map. The native Serre condition is transported by the
actual realized-horn/singular lifting adjunction. Genuine fibration exactness
gives the positive-group bijections at the original total-space point.

A weak collapse of this same chosen native fiber to its point therefore
makes the entire original native one-sphere internal-Hom map weak, including
its component map, for that same actual pointed Serre map. The later
original successor-spectrum corner comparison is separate.

The collapse hypothesis remains explicit. Deriving it from original stable
equivalence requires the pre-model MMSS fiber/cofiber and delooping source
comparisons; no such stable recognition conclusion is asserted here.

The raw point-fiber comparison uses the shared public construction in
`CGWH.StrictFiberLanding`. All maps retain the public supplied fiber projections
and their actual original isomorphisms.
-/

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Simplicial Opposite
open scoped CGWH.modelCategory CGWH.limits SSet.modelCategoryQuillen
  Simplicial Topology MonoidalClosed

private theorem currentNativePiGroupOne_eq_one {X : SSet.{v}} [SSet.KanComplex X]
    (n : ℕ) (x : X _⦋0⦌) :
    @One.one (SSet.KanComplex.π (n + 1) X x)
      ((inferInstance :
        Group (SSet.KanComplex.π (n + 1) X x)).toDivInvMonoid.toMonoid.toMulOneClass.toOne) =
      1 := by
  let gOne : SSet.KanComplex.π (n + 1) X x := @One.one _
    ((inferInstance :
      Group (SSet.KanComplex.π (n + 1) X x)).toDivInvMonoid.toMonoid.toMulOneClass.toOne)
  let d : SSet.KanComplex.π (n + 1) X x :=
    SSet.KanComplex.π.mk (SSet.RelativeMorphism.const : X.PtSimplex (n + 1) x)
  have hd : d * gOne = gOne := by
    obtain ⟨s, hs⟩ := gOne.mk_surjective
    rw [← hs]
    exact (SSet.KanComplex.π.mul_mk_eq_iff).mpr
      ⟨SSet.PtSimplex.MulStruct.oneMul s (Fin.last n)⟩
  change gOne = 1
  calc
    gOne = d * gOne := hd.symm
    _ = d := ((inferInstance :
      Group (SSet.KanComplex.π (n + 1) X x)).toDivInvMonoid.toMonoid.toMulOneClass.mul_one d)
    _ = 1 := rfl

/-- Actual current simplicial fibration exactness gives the entire positive projection
bijection when all actual chosen fiber homotopy types are trivial. -/
private theorem currentNativeFibrationSequence_piMap_bijective
    (S : SSet.FibrationSequence.{v})
    (hsub : ∀ k : ℕ, Subsingleton (SSet.KanComplex.π k S.fiber S.fiberPoint))
    (n : ℕ) :
    Function.Bijective (SSet.KanComplex.π.map S.p S.hb (n + 1)) := by
  constructor
  · let oneE : SSet.KanComplex.π (n + 1) S.E S.e := @One.one _
      ((inferInstance :
        Group (SSet.KanComplex.π (n + 1) S.E S.e)).toDivInvMonoid.toMonoid.toMulOneClass.toOne)
    let oneB : SSet.KanComplex.π (n + 1) S.B S.b := @One.one _
      ((inferInstance :
        Group (SSet.KanComplex.π (n + 1) S.B S.b)).toDivInvMonoid.toMonoid.toMulOneClass.toOne)
    let φ : SSet.KanComplex.π (n + 1) S.E S.e →*
        SSet.KanComplex.π (n + 1) S.B S.b :=
      { toFun := SSet.KanComplex.π.map S.p S.hb (n + 1)
        map_one' := by
          change SSet.KanComplex.π.map S.p S.hb (n + 1) oneE = oneB
          rw [show oneE = 1 from currentNativePiGroupOne_eq_one n S.e,
            show oneB = 1 from currentNativePiGroupOne_eq_one n S.b]
          exact SSet.KanComplex.π.map_one S.p S.hb (n + 1)
        map_mul' := SSet.KanComplex.π.map_mul S.p S.hb n }
    change Function.Injective φ
    rw [injective_iff_map_eq_one]
    intro q hq
    change SSet.KanComplex.π.map S.p S.hb (n + 1) q = oneB at hq
    have hq' : SSet.KanComplex.π.map S.p S.hb (n + 1) q = 1 :=
      hq.trans (currentNativePiGroupOne_eq_one n S.b)
    obtain ⟨r, hr⟩ := S.exactness_at_E q hq'
    have hrOne : r = 1 := (hsub (n + 1)).elim _ _
    change q = oneE
    have hqOne : q = 1 := by
      rw [← hr, hrOne, SSet.KanComplex.π.map_one]
    exact hqOne.trans (currentNativePiGroupOne_eq_one n S.e).symm
  · intro q
    exact S.exactness_at_B q ((hsub n).elim _ _)


namespace PointedCGWH.FiberGeometry

/-- The whole chosen native strict fiber has the actual singular strict
fiber isomorphism, preserving the original map and chosen basepoint. -/
def strictFiberSingularIso {E B : CGWH.{u, v}} (p : E ⟶ B)
    (b : CGWH.point.{u, v} ⟶ B) :
    TopCat.toSSet.obj (CGWH.cgwhToTop.obj (CGWH.strictFiber p b)) ≅
      (SSet.Subcomplex.fiber (TopCat.toSSet.map (CGWH.cgwhToTop.map p))
        (TopCat.toSSetObj₀Equiv.symm (CGWH.pointHomEquiv B b)) : SSet.{v}) :=
  TopCat.toSSet.mapIso (CGWH.strictFiberPointFiberIso p b) ≪≫
    SSet.singularFiberIso (CGWH.cgwhToTop.map p).hom (CGWH.pointHomEquiv B b)

/-- Native Serre fibrancy gives the actual singular Kan fibration through
the original realized-horn lifting adjunction. -/
theorem singular_fibration_of_native {E B : CGWH.{u, v}} (p : E ⟶ B)
    [Fibration p] : Fibration (TopCat.toSSet.map (CGWH.cgwhToTop.map p)) := by
  apply (SSet.modelCategoryQuillen.fibration_iff _).mpr
  have hp : CGWH.modelFibrations p :=
    (HomotopicalAlgebra.fibration_iff p).mp (inferInstance : Fibration p)
  rw [CGWH.modelFibrations_eq_inverseImage, MorphismProperty.inverseImage_iff] at hp
  exact TopCat.hornRLP_iff_toSSet_mem_J_rlp.mp hp

/-- The actual singular fibration sequence of the original native map,
with its supplied chosen points and their supplied equation. -/
def nativeSerreFibrationSequence {E B : CGWH.{u, v}} (p : E ⟶ B)
    [Fibration p] (b : CGWH.point.{u, v} ⟶ B) (e : CGWH.point.{u, v} ⟶ E)
    (over : e ≫ p = b) : SSet.FibrationSequence.{v} where
  E := TopCat.toSSet.obj (CGWH.cgwhToTop.obj E)
  B := TopCat.toSSet.obj (CGWH.cgwhToTop.obj B)
  p := TopCat.toSSet.map (CGWH.cgwhToTop.map p)
  fibration_p := singular_fibration_of_native p
  fibrant_B := by
    let _ : SSet.KanComplex (TopCat.toSSet.obj (CGWH.cgwhToTop.obj B)) :=
      TopCat.toSSet_obj_kanComplex _
    infer_instance
  e := TopCat.toSSetObj₀Equiv.symm (CGWH.pointHomEquiv E e)
  b := TopCat.toSSetObj₀Equiv.symm (CGWH.pointHomEquiv B b)
  hb := by
    change TopCat.toSSetObj₀Equiv.symm (p (e PUnit.unit)) =
      TopCat.toSSetObj₀Equiv.symm (b PUnit.unit)
    exact congrArg TopCat.toSSetObj₀Equiv.symm
      (ConcreteCategory.congr_hom over PUnit.unit)

/-- The actual fibration sequence has exactly the original singular map. -/
@[simp]
theorem nativeSerreFibrationSequence_proj {E B : CGWH.{u, v}} (p : E ⟶ B)
    [Fibration p] (b : CGWH.point.{u, v} ⟶ B) (e : CGWH.point.{u, v} ⟶ E)
    (over : e ≫ p = b) :
    (nativeSerreFibrationSequence p b e over).p =
      TopCat.toSSet.map (CGWH.cgwhToTop.map p) := rfl

/-- The actual strict fiber of the sequence is the same original singular
fiber used by the native strict-fiber isomorphism. -/
@[simp]
theorem nativeSerreFibrationSequence_fiber {E B : CGWH.{u, v}} (p : E ⟶ B)
    [Fibration p] (b : CGWH.point.{u, v} ⟶ B) (e : CGWH.point.{u, v} ⟶ E)
    (over : e ≫ p = b) :
    (nativeSerreFibrationSequence p b e over).fiber =
      (SSet.Subcomplex.fiber (TopCat.toSSet.map (CGWH.cgwhToTop.map p))
        (TopCat.toSSetObj₀Equiv.symm (CGWH.pointHomEquiv B b)) : SSet.{v}) := rfl

/-- The original chosen native strict-fiber point is exactly the chosen
fiber point of the actual singular Serre sequence. -/
theorem strictFiberSingularIso_hom_point
    {E B : CGWH.{u, v}} (p : E ⟶ B) [Fibration p]
    (b : CGWH.point.{u, v} ⟶ B) (e : CGWH.point.{u, v} ⟶ E)
    (over : e ≫ p = b) :
    (strictFiberSingularIso p b).hom.app _
        (TopCat.toSSetObj₀Equiv.symm (CGWH.pointHomEquiv (CGWH.strictFiber p b)
          (CGWH.strictFiberPoint p b e over))) =
      (nativeSerreFibrationSequence p b e over).fiberPoint := by
  apply Subtype.ext
  change ((SSet.singularFiberIso (CGWH.cgwhToTop.map p).hom
      (CGWH.pointHomEquiv B b)).hom.app _
        ((TopCat.toSSet.map (CGWH.strictFiberPointFiberIso p b).hom).app _
          (TopCat.toSSetObj₀Equiv.symm (CGWH.pointHomEquiv (CGWH.strictFiber p b)
            (CGWH.strictFiberPoint p b e over))))).val = _
  have hApp := SSet.singularFiberIso_hom_app_val (CGWH.cgwhToTop.map p).hom
    (CGWH.pointHomEquiv B b) (op ⦋0⦌)
      ((TopCat.toSSet.map (CGWH.strictFiberPointFiberIso p b).hom).app _
        (TopCat.toSSetObj₀Equiv.symm (CGWH.pointHomEquiv (CGWH.strictFiber p b)
          (CGWH.strictFiberPoint p b e over))))
  exact hApp.trans (congrArg
    (TopCat.toSSetObj₀Equiv (X := CGWH.cgwhToTop.obj E)).symm
    (CGWH.strictFiberPointFiberIso_hom_point_val p b e over))

/-- A weak collapse of the same chosen native strict fiber makes every
homotopy type of the actual singular strict fiber subsingleton at its
original chosen point, including degree zero. -/
theorem nativeSerre_fiber_pi_subsingleton_of_weak_collapse
    {E B : CGWH.{u, v}} (p : E ⟶ B) [Fibration p]
    (b : CGWH.point.{u, v} ⟶ B) (e : CGWH.point.{u, v} ⟶ E)
    (over : e ≫ p = b)
    (hF : CGWH.weakHomotopyEquivalences (CGWH.strictFiberToPoint p b)) (n : ℕ) :
    Subsingleton (SSet.KanComplex.π n
      (nativeSerreFibrationSequence p b e over).fiber
      (nativeSerreFibrationSequence p b e over).fiberPoint) := by
  have hTop : TopCat.weakHomotopyEquivalences
      (CGWH.cgwhToTop.map (CGWH.strictFiberToPoint p b)) := by
    rw [CGWH.weakHomotopyEquivalences_eq_inverseImage,
      MorphismProperty.inverseImage_iff] at hF
    exact hF
  have hSing := (TopCat.mem_weakHomotopyEquivalences_iff _).mp hTop
  let hT : IsTerminal (CGWH.cgwhToTop.obj CGWH.point.{u, v}) :=
    TopCat.isTerminalPUnit
  let hST := hT.isTerminalObj TopCat.toSSet
  let _ : SSet.KanComplex (TopCat.toSSet.obj (CGWH.cgwhToTop.obj CGWH.point.{u, v})) :=
    TopCat.toSSet_obj_kanComplex _
  let S := nativeSerreFibrationSequence p b e over
  let a := (strictFiberSingularIso p b).symm
  let z := a.hom.app _ S.fiberPoint
  let Eπ := SSet.KanComplex.π.equivOfIso a rfl n (x := S.fiberPoint)
  have hTerminalPi : Subsingleton (SSet.KanComplex.π n
      (TopCat.toSSet.obj (CGWH.cgwhToTop.obj CGWH.point.{u, v}))
      ((TopCat.toSSet.map (CGWH.cgwhToTop.map (CGWH.strictFiberToPoint p b))).app _ z)) := by
    constructor
    intro c d
    induction c using SSet.KanComplex.π.rec with
    | mk c =>
      induction d using SSet.KanComplex.π.rec with
      | mk d =>
        rw [SSet.KanComplex.π.mk_eq_mk_iff]
        have hcd : c = d := by
          apply SSet.RelativeMorphism.ext
          exact hST.hom_ext _ _
        subst d
        exact ⟨SSet.PtSimplex.RelStruct₀.refl c⟩
  have hNull : Subsingleton (SSet.KanComplex.π n
      (TopCat.toSSet.obj (CGWH.cgwhToTop.obj (CGWH.strictFiber p b))) z) := by
    constructor
    intro c d
    apply (hSing.bijective_piMap n z).1
    exact hTerminalPi.elim _ _
  exact ⟨fun q r => Eπ.injective (hNull.elim _ _)⟩

/-- The same native strict-fiber collapse gives the original based positive
singular-group bijections through genuine total/base fibration exactness. -/
theorem nativeSerre_based_positive_bijective_of_weak_collapse
    {E B : CGWH.{u, v}} (p : E ⟶ B) [Fibration p]
    (b : CGWH.point.{u, v} ⟶ B) (e : CGWH.point.{u, v} ⟶ E)
    (over : e ≫ p = b)
    (hF : CGWH.weakHomotopyEquivalences (CGWH.strictFiberToPoint p b)) (n : ℕ) :
    Function.Bijective (SSet.KanComplex.π.map
      (nativeSerreFibrationSequence p b e over).p
      (nativeSerreFibrationSequence p b e over).hb (n + 1)) := by
  let S := nativeSerreFibrationSequence p b e over
  exact currentNativeFibrationSequence_piMap_bijective S
    (nativeSerre_fiber_pi_subsingleton_of_weak_collapse p b e over hF) n

/-- For the original pointed native Serre map, nullity of its original
chosen strict fiber gives bijectivity of each original positive `piNMap`. -/
theorem piNMap_bijective_of_strictFiber_weak_collapse
    {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) [Fibration f]
    (hF : CGWH.weakHomotopyEquivalences
      (CGWH.strictFiberToPoint f.right Y.hom)) (n : ℕ) :
    Function.Bijective (PointedCGWH.piNMap (n + 1) f) := by
  let _ : Fibration f.right := (PointedCGWH.fibration_iff f).mp inferInstance
  let S := nativeSerreFibrationSequence f.right Y.hom X.hom (Under.w f)
  have hS : Function.Bijective (SSet.KanComplex.π.map S.p S.hb (n + 1)) :=
    nativeSerre_based_positive_bijective_of_weak_collapse
      f.right Y.hom X.hom (Under.w f) hF n
  have transfer : ∀ {y : S.B _⦋0⦌} (h : S.p.app _ S.e = y),
      Function.Bijective (SSet.KanComplex.π.map S.p h (n + 1)) →
        Function.Bijective (SSet.KanComplex.π.map S.p rfl (n + 1) (x := S.e)) := by
    intro y h hh
    subst y
    exact hh
  have hRaw := (TopCat.bijective_singular_positive_piMap_iff
    (CGWH.cgwhToTop.map f.right) (PointedCGWH.underlyingBasepoint X) n).mp
      (transfer S.hb hS)
  exact (PointedCGWH.LoopGeometry.piNMap_bijective_iff_raw n f).mpr hRaw

/-- Original native Serre fibrancy and nullity of the same chosen fiber
give actual one-sphere internal-Hom weakness on all components. -/
theorem ihomSphereOne_weak_of_strictFiber_weak_collapse
    {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) [Fibration f]
    (hF : CGWH.weakHomotopyEquivalences
      (CGWH.strictFiberToPoint f.right Y.hom)) :
    weakEquivalences PointedCGWH.{u, v} ((ihom PointedCGWH.sphereOne).map f) :=
  PointedCGWH.LoopGeometry.ihomSphereOne_weak_of_basedPositive f
    (piNMap_bijective_of_strictFiber_weak_collapse f hF)

/-- The full actual native-to-singular comparison retains the total projection. -/
theorem strictFiberSingularIso_hom_projection
    {E B : CGWH.{u, v}} (p : E ⟶ B) (b : CGWH.point.{u, v} ⟶ B) :
    (strictFiberSingularIso p b).hom ≫
        (SSet.Subcomplex.fiber (TopCat.toSSet.map (CGWH.cgwhToTop.map p))
          (TopCat.toSSetObj₀Equiv.symm (CGWH.pointHomEquiv B b))).ι =
      (CGWH.cgwhToTop ⋙ TopCat.toSSet).map (CGWH.strictFiberToTotal p b) := by
  have hRaw : (CGWH.strictFiberPointFiberIso p b).hom ≫
      AlgebraicTopology.subspaceIncl
        (X := CGWH.cgwhToTop.obj E)
        (Set.ofPred fun x => (CGWH.cgwhToTop.map p) x = CGWH.pointHomEquiv B b) =
      CGWH.cgwhToTop.map (CGWH.strictFiberToTotal p b) := by
    apply ConcreteCategory.hom_ext
    intro x
    exact CGWH.strictFiberPointFiberIso_hom_val p b x
  change (TopCat.toSSet.map (CGWH.strictFiberPointFiberIso p b).hom ≫
      (SSet.singularFiberIso (CGWH.cgwhToTop.map p).hom (CGWH.pointHomEquiv B b)).hom) ≫
    (SSet.Subcomplex.fiber (TopCat.toSSet.map (CGWH.cgwhToTop.map p))
      (TopCat.toSSetObj₀Equiv.symm (CGWH.pointHomEquiv B b))).ι = _
  let a := (CGWH.strictFiberPointFiberIso p b).hom
  let d := (SSet.singularFiberIso (CGWH.cgwhToTop.map p).hom
    (CGWH.pointHomEquiv B b)).hom
  let j := AlgebraicTopology.subspaceIncl
    (X := CGWH.cgwhToTop.obj E)
    (Set.ofPred fun x => (CGWH.cgwhToTop.map p) x = CGWH.pointHomEquiv B b)
  have hSing : d ≫
      (SSet.Subcomplex.fiber (TopCat.toSSet.map (CGWH.cgwhToTop.map p))
        (TopCat.toSSetObj₀Equiv.symm (CGWH.pointHomEquiv B b))).ι =
      TopCat.toSSet.map j :=
    SSet.singularFiberIso_hom_ι (CGWH.cgwhToTop.map p).hom (CGWH.pointHomEquiv B b)
  exact (Category.assoc (TopCat.toSSet.map a) d _).trans
    ((congrArg (fun r => TopCat.toSSet.map a ≫ r) hSing).trans
      ((TopCat.toSSet.map_comp a j).symm.trans (congrArg TopCat.toSSet.map hRaw)))

/-- The complete inverse native-to-singular comparison retains the original projection. -/
theorem strictFiberSingularIso_inv_projection
    {E B : CGWH.{u, v}} (p : E ⟶ B) (b : CGWH.point.{u, v} ⟶ B) :
    (strictFiberSingularIso p b).inv ≫
        (CGWH.cgwhToTop ⋙ TopCat.toSSet).map (CGWH.strictFiberToTotal p b) =
      (SSet.Subcomplex.fiber (TopCat.toSSet.map (CGWH.cgwhToTop.map p))
        (TopCat.toSSetObj₀Equiv.symm (CGWH.pointHomEquiv B b))).ι := by
  rw [← strictFiberSingularIso_hom_projection p b, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

/-- Every compatible native based square commutes with both full original fiber maps. -/
theorem strictFiberSingularIso_naturality
    {E B E' B' : CGWH.{u, v}}
    {p : E ⟶ B} {p' : E' ⟶ B'}
    {b : CGWH.point.{u, v} ⟶ B} {b' : CGWH.point.{u, v} ⟶ B'}
    (a : E ⟶ E') (d : B ⟶ B') (square : a ≫ p' = p ≫ d)
    (base : b ≫ d = b') :
    (CGWH.cgwhToTop ⋙ TopCat.toSSet).map (CGWH.strictFiberMap a d square base) ≫
        (strictFiberSingularIso p' b').hom =
      (strictFiberSingularIso p b).hom ≫
        SSet.Subcomplex.mapFiber
          ((CGWH.cgwhToTop ⋙ TopCat.toSSet).map a)
          ((CGWH.cgwhToTop ⋙ TopCat.toSSet).map d)
          (by
            change (CGWH.cgwhToTop ⋙ TopCat.toSSet).map a ≫
              (CGWH.cgwhToTop ⋙ TopCat.toSSet).map p' =
              (CGWH.cgwhToTop ⋙ TopCat.toSSet).map p ≫
              (CGWH.cgwhToTop ⋙ TopCat.toSSet).map d
            rw [← (CGWH.cgwhToTop ⋙ TopCat.toSSet).map_comp,
              ← (CGWH.cgwhToTop ⋙ TopCat.toSSet).map_comp, square])
          (by
            change TopCat.toSSetObj₀Equiv.symm (d (b PUnit.unit)) =
              TopCat.toSSetObj₀Equiv.symm (b' PUnit.unit)
            exact congrArg TopCat.toSSetObj₀Equiv.symm
              (ConcreteCategory.congr_hom base PUnit.unit)) := by
  let G := CGWH.cgwhToTop ⋙ TopCat.toSSet
  let j := (SSet.Subcomplex.fiber (TopCat.toSSet.map (CGWH.cgwhToTop.map p'))
    (TopCat.toSSetObj₀Equiv.symm (CGWH.pointHomEquiv B' b'))).ι
  apply (cancel_mono j).mp
  have hLeft : (G.map (CGWH.strictFiberMap a d square base) ≫
      (strictFiberSingularIso p' b').hom) ≫ j =
      G.map (CGWH.strictFiberMap a d square base) ≫
      G.map (CGWH.strictFiberToTotal p' b') :=
    (Category.assoc _ _ _).trans
      (congrArg (fun r => G.map (CGWH.strictFiberMap a d square base) ≫ r)
        (strictFiberSingularIso_hom_projection p' b'))
  have hNative : G.map (CGWH.strictFiberMap a d square base) ≫
      G.map (CGWH.strictFiberToTotal p' b') =
      G.map (CGWH.strictFiberToTotal p b) ≫ G.map a :=
    (G.map_comp _ _).symm.trans
      ((congrArg G.map (CGWH.strictFiberMap_toTotal a d square base)).trans
        (G.map_comp _ _))
  have hSquare : G.map a ≫ G.map p' = G.map p ≫ G.map d :=
    (G.map_comp _ _).symm.trans ((congrArg G.map square).trans (G.map_comp _ _))
  have hBase : (G.map d).app _ (TopCat.toSSetObj₀Equiv.symm (CGWH.pointHomEquiv B b)) =
      TopCat.toSSetObj₀Equiv.symm (CGWH.pointHomEquiv B' b') := by
    change TopCat.toSSetObj₀Equiv.symm (d (b PUnit.unit)) =
      TopCat.toSSetObj₀Equiv.symm (b' PUnit.unit)
    exact congrArg TopCat.toSSetObj₀Equiv.symm
      (ConcreteCategory.congr_hom base PUnit.unit)
  have hRight : ((strictFiberSingularIso p b).hom ≫
      SSet.Subcomplex.mapFiber (G.map a) (G.map d) hSquare hBase) ≫ j =
      G.map (CGWH.strictFiberToTotal p b) ≫ G.map a :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun r => (strictFiberSingularIso p b).hom ≫ r)
        (SSet.Subcomplex.mapFiber_ι (G.map a) (G.map d) hSquare hBase)).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun r => r ≫ G.map a) (strictFiberSingularIso_hom_projection p b))))
  exact hLeft.trans (hNative.trans hRight.symm)


end PointedCGWH.FiberGeometry
