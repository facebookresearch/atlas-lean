/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.TriHexFKTorusBoundaryReach
import Code.FK.TriHexSurfacePercolationClosure
















open Filter Finset MeasureTheory Set Topology

namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

noncomputable section




def triHexTorusRadialSize (n : Nat) : Nat := 4 * n + 5

theorem triHexTorusRadialSize_gt_two (n : Nat) :
    2 < triHexTorusRadialSize n := by
  simp [triHexTorusRadialSize]


def triHexTorusRadialTarget (n : Nat) :
    Finset (TorusSite (triHexTorusRadialSize n)) := by
  letI : Fact (2 < triHexTorusRadialSize n) :=
    ⟨triHexTorusRadialSize_gt_two n⟩
  exact Finset.univ.filter fun z =>
    z.1.val = 2 * n + 2 || z.2.val = 2 * n + 2


noncomputable def triangularTorusRadialReachProbability
    (p q : Real) (n : Nat) : Real := by
  letI : Fact (2 < triHexTorusRadialSize n) :=
    ⟨triHexTorusRadialSize_gt_two n⟩
  exact activeProbOf (triangularTorusGraph (triHexTorusRadialSize n))
    (fun _ => p) q
    (triangularTorusActiveReachEvent (triHexTorusRadialSize n) (0, 0)
      (triHexTorusRadialTarget n))



noncomputable def hexagonalTorusRadialReachProbability
    (p q : Real) (n : Nat) : Real := by
  letI : Fact (2 < triHexTorusRadialSize n) :=
    ⟨triHexTorusRadialSize_gt_two n⟩
  exact activeProbOf (hexagonalTorusGraph (triHexTorusRadialSize n))
    (fun _ => BeffaraDC.dualParam p q) q
    (hexagonalTorusActiveWhiteReachEvent (triHexTorusRadialSize n) (0, 0)
      (triHexTorusRadialTarget n))



theorem triHexFK_torus_radialReachProbability_eq
    {p q : Real} (hq : 0 < q) (hp : p ∈ Ioo (0 : Real) 1)
    (hsurface : FrontierA.triangularFKCriticalPolynomial q
      (FrontierA.fkEdgeOdds p) = 0) (n : Nat) :
    hexagonalTorusRadialReachProbability p q n =
      triangularTorusRadialReachProbability p q n := by
  letI : Fact (2 < triHexTorusRadialSize n) :=
    ⟨triHexTorusRadialSize_gt_two n⟩
  exact triHexFK_torus_homogeneous_activeReachProbability_eq
    (triHexTorusRadialSize n) hq hp hsurface (0, 0)
      (triHexTorusRadialTarget n)


def TriangularTorusRadialPercolates (p q : Real) : Prop :=
  ∃ theta : Real,
    Tendsto (triangularTorusRadialReachProbability p q) atTop (nhds theta) ∧
      0 < theta


def HexagonalTorusRadialPercolates (p q : Real) : Prop :=
  ∃ theta : Real,
    Tendsto (hexagonalTorusRadialReachProbability p q) atTop (nhds theta) ∧
      0 < theta



theorem triangularTorusRadialPercolates_iff_hexagonal
    {p q : Real} (hq : 0 < q) (hp : p ∈ Ioo (0 : Real) 1)
    (hsurface : FrontierA.triangularFKCriticalPolynomial q
      (FrontierA.fkEdgeOdds p) = 0) :
    TriangularTorusRadialPercolates p q ↔
      HexagonalTorusRadialPercolates p q := by
  have heq : hexagonalTorusRadialReachProbability p q =
      triangularTorusRadialReachProbability p q := by
    funext n
    exact triHexFK_torus_radialReachProbability_eq hq hp hsurface n
  simp only [TriangularTorusRadialPercolates,
    HexagonalTorusRadialPercolates, heq]




noncomputable def triangularWiredBoundaryArmProbability
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (n : Nat) : Real :=
  (triangular.wiredBufferedInfiniteVolume hp hp1 hq :
    Measure (ConfigSpace (Sym2 (Site 2)))).real
      (triangular.bufferedCylinder n
        (triangular.bufferedRootBoundaryEvent n))



noncomputable def hexagonalWiredBoundaryArmProbability
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (n : Nat) : Real :=
  (hexagonal.wiredBufferedInfiniteVolume
      (BeffaraDC.dualParam_pos hp hp1 hq)
      (BeffaraDC.dualParam_lt_one hp hp1 hq) hq :
    Measure (ConfigSpace (Sym2 HexVertex))).real
      (hexagonal.bufferedCylinder n
        (hexagonal.bufferedRootBoundaryEvent n))




def TriHexTorusBufferedReachApproximation
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) : Prop :=
  Tendsto
      (fun n => triangularTorusRadialReachProbability p q n -
        triangularWiredBoundaryArmProbability hp hp1 hq n)
      atTop (nhds 0) ∧
    Tendsto
      (fun n => hexagonalTorusRadialReachProbability p q n -
        hexagonalWiredBoundaryArmProbability hp hp1 hq n)
      atTop (nhds 0)



theorem wiredPercolationProbability_eq_of_torusBufferedReachApproximation
    {p q : Real} (hq : 0 < q) (hp : p ∈ Ioo (0 : Real) 1)
    (hsurface : FrontierA.triangularFKCriticalPolynomial q
      (FrontierA.fkEdgeOdds p) = 0)
    (happrox : TriHexTorusBufferedReachApproximation hp.1 hp.2 hq) :
    triangular.wiredPercolationProbability p q =
      hexagonal.wiredPercolationProbability (BeffaraDC.dualParam p q) q := by
  have htriArm : Tendsto
      (triangularWiredBoundaryArmProbability hp.1 hp.2 hq)
      atTop (nhds (triangular.wiredPercolationProbability p q)) := by
    simpa [triangularWiredBoundaryArmProbability] using
      triangular.bufferedRootBoundaryCylinder_real_tendsto hp.1 hp.2 hq
  have hhexArm : Tendsto
      (hexagonalWiredBoundaryArmProbability hp.1 hp.2 hq)
      atTop (nhds (hexagonal.wiredPercolationProbability
        (BeffaraDC.dualParam p q) q)) := by
    simpa [hexagonalWiredBoundaryArmProbability] using
      hexagonal.bufferedRootBoundaryCylinder_real_tendsto
        (BeffaraDC.dualParam_pos hp.1 hp.2 hq)
        (BeffaraDC.dualParam_lt_one hp.1 hp.2 hq) hq
  have htriTorus : Tendsto
      (triangularTorusRadialReachProbability p q) atTop
      (nhds (triangular.wiredPercolationProbability p q)) := by
    have hadd := happrox.1.add htriArm
    convert hadd using 1
    · funext n
      ring
    · simp
  have hhexTorus : Tendsto
      (hexagonalTorusRadialReachProbability p q) atTop
      (nhds (hexagonal.wiredPercolationProbability
        (BeffaraDC.dualParam p q) q)) := by
    have hadd := happrox.2.add hhexArm
    convert hadd using 1
    · funext n
      ring
    · simp
  have hhexAsTri : Tendsto
      (triangularTorusRadialReachProbability p q) atTop
      (nhds (hexagonal.wiredPercolationProbability
        (BeffaraDC.dualParam p q) q)) := by
    apply hhexTorus.congr'
    filter_upwards with n
    exact triHexFK_torus_radialReachProbability_eq hq hp hsurface n
  exact tendsto_nhds_unique htriTorus hhexAsTri



theorem triHexSurfacePercolationEquivalence_of_torusBufferedReachApproximation
    {p q : Real} (hq : 0 < q) (hp : p ∈ Ioo (0 : Real) 1)
    (hsurface : FrontierA.triangularFKCriticalPolynomial q
      (FrontierA.fkEdgeOdds p) = 0)
    (happrox : TriHexTorusBufferedReachApproximation hp.1 hp.2 hq) :
    TriHexSurfacePercolationEquivalence q p := by
  unfold TriHexSurfacePercolationEquivalence PeriodicGraph.wiredPercolates
  rw [wiredPercolationProbability_eq_of_torusBufferedReachApproximation
    hq hp hsurface happrox]

end

end StatMech.FK.PeriodicPlanar
