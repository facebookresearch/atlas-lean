/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicProjectedFullMedialInterpolation
import Code.Universality.IsingFermionicSquareCaratheodory
import Code.Universality.IsingFermionicBoundaryLayerConsistency
import Code.Universality.IsingFermionicCalibratedRobinConsistency














namespace StatMech.Universality

open Filter Metric Set Topology
open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section



def fkIsingExpandingBoundarySquareRadialDart
    (k m : Nat) (hm : m ≤ fkIsingExpandingSquareSide k)
    (i j : Fin m) (s : FKIsingMedialSide) :
    fkIsingExpandingBoundarySquareCaratheodoryApproximation.M k :=
  .dart (fkIsingSquareRadialPatchEdge
    (fkIsingExpandingSquareSide k) m hm i j, s)



def fkIsingExpandingBoundarySquareRadialSamplePosition
    (k : Nat) (i j : Nat) : Complex :=
  isingRadialGridPosition (fkIsingExpandingSquareScale k) i j



noncomputable def fkIsingExpandingBoundarySquareRadialTwoScaleInterpolant
    (k m : Nat) (hm : m ≤ fkIsingExpandingSquareSide k) :
    Complex → Complex :=
  fkIsingSquareBoundaryRadialPatchTwoScaleInterpolant
    (fkIsingExpandingSquareSide k) m
    (fkIsingExpandingSquareSide_pos k) hm
    (fkIsingExpandingSquareScale k)
    (fkIsingExpandingBoundarySquareCaratheodoryApproximation.mesh k)

theorem fkIsingExpandingBoundarySquareRadialTwoScaleInterpolant_continuous
    (k m : Nat) (hm : m ≤ fkIsingExpandingSquareSide k) :
    Continuous
      (fkIsingExpandingBoundarySquareRadialTwoScaleInterpolant k m hm) :=
  fkIsingSquareBoundaryRadialPatchTwoScaleInterpolant_continuous _ _ _ _ _ _



theorem fkIsingExpandingBoundarySquareRadial_embedding_dist_lt
    (k m : Nat) (hm : m ≤ fkIsingExpandingSquareSide k)
    (i j : Fin m) (s : FKIsingMedialSide) :
    dist
        (fkIsingExpandingBoundarySquareCaratheodoryApproximation.medialEmbedding
          k (fkIsingExpandingBoundarySquareRadialDart k m hm i j s))
        (fkIsingExpandingBoundarySquareRadialSamplePosition k i.1 j.1) <
      fkIsingExpandingSquareScale k / 10 := by
  change dist
      (fkIsingSquareWiredPerturbedCarrierPosition
        (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)
        (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareScale_pos k)
        (.dart (fkIsingSquareRadialPatchEdge
          (fkIsingExpandingSquareSide k) m hm i j, s)))
      (fkIsingExpandingBoundarySquareRadialSamplePosition k i.1 j.1) < _
  rw [fkIsingExpandingBoundarySquareRadialSamplePosition,
    isingRadialGridPosition_eq_scaledCarrierPosition]
  exact fkIsingSquareWiredPerturbedCarrierPosition_dist_lt
    (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)
    (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareScale_pos k)
    (.dart (fkIsingSquareRadialPatchEdge
      (fkIsingExpandingSquareSide k) m hm i j, s))



theorem fkIsingExpandingBoundarySquareRadial_normalizedObservable
    (k m : Nat) (hm : m ≤ fkIsingExpandingSquareSide k)
    (i j : Fin m) (s : FKIsingMedialSide) :
    @FKIsingDobrushinDomain.normalizedFermionicObservable
        (fkIsingExpandingBoundarySquareCaratheodoryApproximation.P k)
        (fkIsingExpandingBoundarySquareCaratheodoryApproximation.M k)
        (fkIsingExpandingBoundarySquareCaratheodoryApproximation.decEqM k)
        (fkIsingExpandingBoundarySquareCaratheodoryApproximation.dobrushin k)
        (fkIsingExpandingBoundarySquareCaratheodoryApproximation.mesh k)
        (fkIsingExpandingBoundarySquareRadialDart k m hm i j s) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain
        (fkIsingExpandingSquareSide k)
        (fkIsingExpandingSquareSide_pos k)).normalizedFermionicObservable
        (fkIsingExpandingBoundarySquareCaratheodoryApproximation.mesh k)
        (.dart (fkIsingSquareRadialPatchEdge
          (fkIsingExpandingSquareSide k) m hm i j, s)) := by
  rfl



theorem fkIsingExpandingBoundarySquareRadial_projection_sample
    (k m : Nat) (hm : m ≤ fkIsingExpandingSquareSide k)
    (i j : Fin m) (s : FKIsingMedialSide) :
    isingProj
        (fkIsingSquareWiredDirectedTangent
          (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)
          (fkIsingExpandingBoundarySquareRadialDart k m hm i j s))
        (fkIsingExpandingBoundarySquareRadialTwoScaleInterpolant k m hm
          (fkIsingExpandingBoundarySquareRadialSamplePosition k i.1 j.1)) =
      @FKIsingDobrushinDomain.normalizedFermionicObservable
        (fkIsingExpandingBoundarySquareCaratheodoryApproximation.P k)
        (fkIsingExpandingBoundarySquareCaratheodoryApproximation.M k)
        (fkIsingExpandingBoundarySquareCaratheodoryApproximation.decEqM k)
        (fkIsingExpandingBoundarySquareCaratheodoryApproximation.dobrushin k)
        (fkIsingExpandingBoundarySquareCaratheodoryApproximation.mesh k)
        (fkIsingExpandingBoundarySquareRadialDart k m hm i j s) := by
  rw [fkIsingExpandingBoundarySquareRadial_normalizedObservable]
  exact fkIsingSquareBoundaryRadialPatchTwoScaleInterpolant_projection
    (fkIsingExpandingSquareSide k) m (fkIsingExpandingSquareSide_pos k) hm
    (fkIsingExpandingSquareScale k)
    (fkIsingExpandingBoundarySquareCaratheodoryApproximation.mesh k)
    (fkIsingExpandingSquareScale_pos k) i j s



theorem fkIsingExpandingBoundarySquareRadial_projection_embedding_dist_le
    (k m : Nat) (hm : m ≤ fkIsingExpandingSquareSide k)
    (i j : Fin m) (s : FKIsingMedialSide) (C alpha : NNReal)
    (hholder : HolderWith C alpha
      (fkIsingExpandingBoundarySquareRadialTwoScaleInterpolant k m hm)) :
    dist
        (isingProj
          (fkIsingSquareWiredDirectedTangent
            (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)
            (fkIsingExpandingBoundarySquareRadialDart k m hm i j s))
          (fkIsingExpandingBoundarySquareRadialTwoScaleInterpolant k m hm
            (fkIsingExpandingBoundarySquareCaratheodoryApproximation.medialEmbedding k
              (fkIsingExpandingBoundarySquareRadialDart k m hm i j s))))
        (@FKIsingDobrushinDomain.normalizedFermionicObservable
          (fkIsingExpandingBoundarySquareCaratheodoryApproximation.P k)
          (fkIsingExpandingBoundarySquareCaratheodoryApproximation.M k)
          (fkIsingExpandingBoundarySquareCaratheodoryApproximation.decEqM k)
          (fkIsingExpandingBoundarySquareCaratheodoryApproximation.dobrushin k)
          (fkIsingExpandingBoundarySquareCaratheodoryApproximation.mesh k)
          (fkIsingExpandingBoundarySquareRadialDart k m hm i j s)) ≤
      C *
        dist
          (fkIsingExpandingBoundarySquareCaratheodoryApproximation.medialEmbedding
            k (fkIsingExpandingBoundarySquareRadialDart k m hm i j s))
          (fkIsingExpandingBoundarySquareRadialSamplePosition k i.1 j.1) ^
            (alpha : Real) := by
  apply isingProj_dist_le_of_nearby_holder
  · rw [Complex.normSq_eq_norm_sq]
    simp [fkIsingSquareWiredDirectedTangent, Complex.norm_exp]
  · exact hholder
  · exact fkIsingExpandingBoundarySquareRadial_projection_sample
      k m hm i j s

namespace FKIsingSquareBoundaryLayerCoordinateOneForm



theorem fullSquareScaledVertexEmbedding_dist_le_two_abs
    (n : Nat) (scale : Real) (x y : FKIsingSquareFullVertexNode n)
    (hxy : (fkIsingSquareFullVertexGraph n).Adj x y) :
    dist (fullSquareScaledVertexEmbedding n scale y)
        (fullSquareScaledVertexEmbedding n scale x) ≤ 2 * |scale| := by
  have hunit : unitWt (y.1 - x.1) = 1 := by
    exact (adj_iff_unitWt_sub y.1 x.1).1 hxy.symm
  have hcases :
      (y.1 0 = x.1 0 + 1 ∧ y.1 1 = x.1 1) ∨
      (y.1 0 + 1 = x.1 0 ∧ y.1 1 = x.1 1) ∨
      (y.1 0 = x.1 0 ∧ y.1 1 = x.1 1 + 1) ∨
      (y.1 0 = x.1 0 ∧ y.1 1 + 1 = x.1 1) := by
    unfold unitWt at hunit
    simp only [Fin.sum_univ_two, Pi.sub_apply] at hunit
    omega
  rw [dist_eq_norm]
  calc
    ‖fullSquareScaledVertexEmbedding n scale y -
        fullSquareScaledVertexEmbedding n scale x‖ ≤
      |(fullSquareScaledVertexEmbedding n scale y -
        fullSquareScaledVertexEmbedding n scale x).re| +
      |(fullSquareScaledVertexEmbedding n scale y -
        fullSquareScaledVertexEmbedding n scale x).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ = 2 * |scale| := by
      rcases hcases with ⟨h0, h1⟩ | ⟨h0, h1⟩ |
          ⟨h0, h1⟩ | ⟨h0, h1⟩
      · have h0R : (y.1 0 : Real) = (x.1 0 : Real) + 1 := by
          exact_mod_cast h0
        have h1R : (y.1 1 : Real) = (x.1 1 : Real) := by
          exact_mod_cast h1
        simp [fullSquareScaledVertexEmbedding,
          fullSquareScaledCoordinateEmbedding,
          fkIsingSquareFullVertexCoordinate,
          fkIsingSquareWiredIntPoint, h0R, h1R, abs_mul]
        ring
      · have h0R : (y.1 0 : Real) + 1 = (x.1 0 : Real) := by
          exact_mod_cast h0
        have h1R : (y.1 1 : Real) = (x.1 1 : Real) := by
          exact_mod_cast h1
        have hy0 : (y.1 0 : Real) = (x.1 0 : Real) - 1 := by
          linarith
        simp [fullSquareScaledVertexEmbedding,
          fullSquareScaledCoordinateEmbedding,
          fkIsingSquareFullVertexCoordinate,
          fkIsingSquareWiredIntPoint, hy0, h1R, abs_mul]
        ring_nf
        rw [abs_neg]
      · have h0R : (y.1 0 : Real) = (x.1 0 : Real) := by
          exact_mod_cast h0
        have h1R : (y.1 1 : Real) = (x.1 1 : Real) + 1 := by
          exact_mod_cast h1
        simp [fullSquareScaledVertexEmbedding,
          fullSquareScaledCoordinateEmbedding,
          fkIsingSquareFullVertexCoordinate,
          fkIsingSquareWiredIntPoint, h0R, h1R, abs_mul]
        ring_nf
        rw [abs_neg]
        ring
      · have h0R : (y.1 0 : Real) = (x.1 0 : Real) := by
          exact_mod_cast h0
        have h1R : (y.1 1 : Real) + 1 = (x.1 1 : Real) := by
          exact_mod_cast h1
        have hy1 : (y.1 1 : Real) = (x.1 1 : Real) - 1 := by
          linarith
        simp [fullSquareScaledVertexEmbedding,
          fullSquareScaledCoordinateEmbedding,
          fkIsingSquareFullVertexCoordinate,
          fkIsingSquareWiredIntPoint, h0R, hy1, abs_mul]
        ring_nf
        rw [abs_neg]
        ring



theorem fullSquareScaledFaceEmbedding_dist_le_two_abs
    (n : Nat) (scale : Real) (c d : FKIsingSquareFullFaceNode n)
    (hcd : (fkIsingSquareFullFaceGraph n).Adj c d) :
    dist (fullSquareScaledFaceEmbedding n scale d)
        (fullSquareScaledFaceEmbedding n scale c) ≤ 2 * |scale| := by
  rw [dist_eq_norm]
  calc
    ‖fullSquareScaledFaceEmbedding n scale d -
        fullSquareScaledFaceEmbedding n scale c‖ ≤
      |(fullSquareScaledFaceEmbedding n scale d -
        fullSquareScaledFaceEmbedding n scale c).re| +
      |(fullSquareScaledFaceEmbedding n scale d -
        fullSquareScaledFaceEmbedding n scale c).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ = 2 * |scale| := by
      rcases hcd with ⟨hcol, hup | hdown⟩ | ⟨hrow, hright | hleft⟩
      · have h0 : c.1.1 = d.1.1 := congrArg Fin.val hcol
        have h1 : (c.2.1 : Real) + 1 = (d.2.1 : Real) := by
          exact_mod_cast hup
        have hd0 : (d.1.1 : Real) = (c.1.1 : Real) := by
          exact_mod_cast h0.symm
        have hd1 : (d.2.1 : Real) = (c.2.1 : Real) + 1 := by
          linarith
        simp [fullSquareScaledFaceEmbedding,
          fullSquareScaledCoordinateEmbedding,
          fkIsingSquareFullFaceCoordinate, fkIsingSquareInteriorCellKey,
          fkIsingSquareWiredIntPoint, hd0, hd1, abs_mul]
        ring_nf
        rw [abs_neg]
        ring
      · have h0 : c.1.1 = d.1.1 := congrArg Fin.val hcol
        have h1 : (d.2.1 : Real) + 1 = (c.2.1 : Real) := by
          exact_mod_cast hdown
        have hd0 : (d.1.1 : Real) = (c.1.1 : Real) := by
          exact_mod_cast h0.symm
        have hd1 : (d.2.1 : Real) = (c.2.1 : Real) - 1 := by
          linarith
        simp [fullSquareScaledFaceEmbedding,
          fullSquareScaledCoordinateEmbedding,
          fkIsingSquareFullFaceCoordinate, fkIsingSquareInteriorCellKey,
          fkIsingSquareWiredIntPoint, hd0, hd1, abs_mul]
        ring_nf
        rw [abs_neg]
        ring
      · have h0 : c.2.1 = d.2.1 := congrArg Fin.val hrow
        have h1 : (c.1.1 : Real) + 1 = (d.1.1 : Real) := by
          exact_mod_cast hright
        have hd0 : (d.2.1 : Real) = (c.2.1 : Real) := by
          exact_mod_cast h0.symm
        have hd1 : (d.1.1 : Real) = (c.1.1 : Real) + 1 := by
          linarith
        simp [fullSquareScaledFaceEmbedding,
          fullSquareScaledCoordinateEmbedding,
          fkIsingSquareFullFaceCoordinate, fkIsingSquareInteriorCellKey,
          fkIsingSquareWiredIntPoint, hd0, hd1, abs_mul]
        ring_nf
      · have h0 : c.2.1 = d.2.1 := congrArg Fin.val hrow
        have h1 : (d.1.1 : Real) + 1 = (c.1.1 : Real) := by
          exact_mod_cast hleft
        have hd0 : (d.2.1 : Real) = (c.2.1 : Real) := by
          exact_mod_cast h0.symm
        have hd1 : (d.1.1 : Real) = (c.1.1 : Real) - 1 := by
          linarith
        simp [fullSquareScaledFaceEmbedding,
          fullSquareScaledCoordinateEmbedding,
          fkIsingSquareFullFaceCoordinate, fkIsingSquareInteriorCellKey,
          fkIsingSquareWiredIntPoint, hd0, hd1, abs_mul]
        ring_nf
        rw [abs_neg]


theorem fullFace_neighbor_card_le_four
    (n : Nat) (c : FKIsingSquareFullFaceNode n) :
    Nat.card ↑((fkIsingSquareFullFaceGraph n).neighborSet c) ≤ 4 := by
  classical
  let center : Site 2 := ![(c.1.1 : Int), (c.2.1 : Int)]
  let f : (fkIsingSquareFullFaceGraph n).neighborSet c →
      (hypercubicLattice 2).neighborSet center := fun d ↦
    ⟨![(d.1.1.1 : Int), (d.1.2.1 : Int)], by
      change (hypercubicLattice 2).Adj center
        ![(d.1.1.1 : Int), (d.1.2.1 : Int)]
      rw [adj_iff_unitWt_sub]
      rcases d.2 with ⟨hcol, hup | hdown⟩ | ⟨hrow, hright | hleft⟩
      all_goals simp [unitWt, center] at *
      all_goals omega⟩
  have hf : Function.Injective f := by
    intro d e hde
    have h0 := congrArg (fun z : Site 2 ↦ z 0) (congrArg Subtype.val hde)
    have h1 := congrArg (fun z : Site 2 ↦ z 1) (congrArg Subtype.val hde)
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext
    · simpa [f] using h0
    · simpa [f] using h1
  calc
    Nat.card ((fkIsingSquareFullFaceGraph n).neighborSet c) ≤
        Nat.card ((hypercubicLattice 2).neighborSet center) :=
      Nat.card_le_card_of_injective f hf
    _ = (hypercubicLattice 2).degree center :=
      (Nat.card_eq_fintype_card).trans
        (SimpleGraph.card_neighborSet_eq_degree _ _)
    _ = 4 := by simpa using degree_eq 2 center



theorem isingFiniteGraphLaplacian_abs_le_four_mul
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (f : V → Real) (x : V) (D : Real) (hD : 0 ≤ D)
    (hcard : Nat.card ↑(G.neighborSet x) ≤ 4)
    (hneighbor : ∀ y, G.Adj x y → |f y - f x| ≤ D) :
    |isingFiniteGraphLaplacian G f x| ≤ 4 * D := by
  classical
  have hcardFinset : (G.neighborFinset x).card ≤ 4 := by
    have hncard : Nat.card ↑(G.neighborSet x) = G.degree x :=
      (Nat.card_eq_fintype_card).trans
        (SimpleGraph.card_neighborSet_eq_degree _ _)
    rw [SimpleGraph.card_neighborFinset_eq_degree, ← hncard]
    exact hcard
  unfold isingFiniteGraphLaplacian
  calc
    |∑ y ∈ G.neighborFinset x, (f y - f x)| ≤
        ∑ y ∈ G.neighborFinset x, |f y - f x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _y ∈ G.neighborFinset x, D := by
      apply Finset.sum_le_sum
      intro y hy
      rw [SimpleGraph.mem_neighborFinset] at hy
      exact hneighbor y hy
    _ = ((G.neighborFinset x).card : Real) * D := by simp
    _ ≤ 4 * D := by
      gcongr
      exact_mod_cast hcardFinset



theorem fullSquareScaledVertex_sampledLaplacian_le_lipschitz
    (n : Nat) (scale : Real) (Phi : Complex → Complex)
    (L : NNReal) (hPhi : LipschitzWith L (fun z ↦ (Phi z).im))
    (x : FKIsingSquareFullVertexNode n) :
    |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
      (fun y ↦ (Phi (fullSquareScaledVertexEmbedding n scale y)).im) x| ≤
        8 * (L : Real) * |scale| := by
  have hD : 0 ≤ 2 * (L : Real) * |scale| := by positivity
  calc
    _ ≤ 4 * (2 * (L : Real) * |scale|) := by
      apply isingFiniteGraphLaplacian_abs_le_four_mul
        (fkIsingSquareFullVertexGraph n) _ x _ hD
          (fullVertex_neighbor_card_le_four n x)
      intro y hxy
      rw [← Real.dist_eq]
      exact (hPhi.dist_le_mul _ _).trans (by
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          (mul_le_mul_of_nonneg_left
            (fullSquareScaledVertexEmbedding_dist_le_two_abs
              n scale x y hxy) L.2))
    _ = 8 * (L : Real) * |scale| := by ring


theorem fullSquareScaledFace_sampledLaplacian_le_lipschitz
    (n : Nat) (scale : Real) (Phi : Complex → Complex)
    (L : NNReal) (hPhi : LipschitzWith L (fun z ↦ (Phi z).im))
    (c : FKIsingSquareFullFaceNode n) :
    |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
      (fun d ↦ (Phi (fullSquareScaledFaceEmbedding n scale d)).im) c| ≤
        8 * (L : Real) * |scale| := by
  have hD : 0 ≤ 2 * (L : Real) * |scale| := by positivity
  calc
    _ ≤ 4 * (2 * (L : Real) * |scale|) := by
      apply isingFiniteGraphLaplacian_abs_le_four_mul
        (fkIsingSquareFullFaceGraph n) _ c _ hD
          (fullFace_neighbor_card_le_four n c)
      intro d hcd
      rw [← Real.dist_eq]
      exact (hPhi.dist_le_mul _ _).trans (by
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          (mul_le_mul_of_nonneg_left
            (fullSquareScaledFaceEmbedding_dist_le_two_abs
              n scale c d hcd) L.2))
    _ = 8 * (L : Real) * |scale| := by ring



theorem fullSquareVertex_bulk_directions
    (n : Nat) (x : FKIsingSquareFullVertexNode n)
    (hfixed : ¬ fkIsingSquareFullVertexFixedBoundary n x)
    (hghost : fkIsingSquareFullVertexGhostMultiplicity n x = 0) :
    fkIsingSquareDirectionAvailable n x .east ∧
      fkIsingSquareDirectionAvailable n x .north ∧
      fkIsingSquareDirectionAvailable n x .west ∧
      fkIsingSquareDirectionAvailable n x .south := by
  have hx := fkIsingSquareVertex_coordinate_bounds n x 0
  have hy := fkIsingSquareVertex_coordinate_bounds n x 1
  have hwest_ne : x.1 0 ≠ -(n : Int) := by
    simpa [fkIsingSquareFullVertexFixedBoundary, fkIsingSquareWiredArc]
      using hfixed
  have heast_ne : x.1 0 ≠ (n : Int) := by
    intro heast
    have hpos : 0 < fkIsingSquareFullVertexGhostMultiplicity n x :=
      (fkIsingSquareFullVertexGhostMultiplicity_pos_iff n x).2
        (Or.inr (Or.inl heast))
    omega
  have hnorth_ne : x.1 1 ≠ (n : Int) := by
    intro hnorth
    have hpos : 0 < fkIsingSquareFullVertexGhostMultiplicity n x :=
      (fkIsingSquareFullVertexGhostMultiplicity_pos_iff n x).2
        (Or.inr (Or.inr hnorth))
    omega
  have hsouth_ne : x.1 1 ≠ -(n : Int) := by
    intro hsouth
    have hpos : 0 < fkIsingSquareFullVertexGhostMultiplicity n x :=
      (fkIsingSquareFullVertexGhostMultiplicity_pos_iff n x).2
        (Or.inl hsouth)
    omega
  simp only [fkIsingSquareDirectionAvailable]
  omega



theorem fullSquareFace_bulk_coordinates
    (n : Nat) (c : FKIsingSquareFullFaceNode n)
    (hfixed : ¬ fkIsingSquareFullFaceFixedBoundary n c)
    (hghost : fkIsingSquareFullFaceGhostMultiplicity n c = 0) :
    c.1.1 + 1 < 2 * n ∧ c.2.1 + 1 < 2 * n ∧
      0 < c.1.1 ∧ 0 < c.2.1 := by
  have hx := c.1.2
  have hy := c.2.2
  have hwest_ne : c.1.1 ≠ 0 := by
    intro hwest
    have hpos : 0 < fkIsingSquareFullFaceGhostMultiplicity n c :=
      (fkIsingSquareFullFaceGhostMultiplicity_pos_iff n c).2 hwest
    omega
  have hsouth_ne : c.2.1 ≠ 0 := by
    intro hsouth
    exact hfixed (Or.inl hsouth)
  have heast_ne : c.1.1 + 1 ≠ 2 * n := by
    intro heast
    exact hfixed (Or.inr (Or.inl heast))
  have hnorth_ne : c.2.1 + 1 ≠ 2 * n := by
    intro hnorth
    exact hfixed (Or.inr (Or.inr hnorth))
  omega



structure DirectionalFourthOrderHarmonicData
    (f : Complex → Real) (z : Complex) (boundOne boundTwo : Real) : Prop where
  contDiffOne : ContDiff Real 4
    (fun t : Real ↦ f (z + (t : Complex) * (1 + Complex.I)))
  contDiffTwo : ContDiff Real 4
    (fun t : Real ↦ f (z + (t : Complex) * (1 - Complex.I)))
  fourthOne : ∀ t,
    |iteratedDeriv 4
      (fun s : Real ↦ f (z + (s : Complex) * (1 + Complex.I))) t| ≤ boundOne
  fourthTwo : ∀ t,
    |iteratedDeriv 4
      (fun s : Real ↦ f (z + (s : Complex) * (1 - Complex.I))) t| ≤ boundTwo
  harmonic :
    iteratedDeriv 2
        (fun t : Real ↦ f (z + (t : Complex) * (1 + Complex.I))) 0 +
      iteratedDeriv 2
        (fun t : Real ↦ f (z + (t : Complex) * (1 - Complex.I))) 0 = 0



structure PhysicalFourthOrderBulkData
    (N : Nat → Nat) (Phi : Complex → Complex) (mesh : Nat → Real) where
  boundOne : Real
  boundTwo : Real
  boundSum_nonneg : 0 ≤ boundOne + boundTwo
  vertex : ∀ k x,
    ¬ fkIsingSquareFullVertexFixedBoundary (N k) x →
    fkIsingSquareFullVertexGhostMultiplicity (N k) x = 0 →
      DirectionalFourthOrderHarmonicData (fun z ↦ (Phi z).im)
        (fullSquareScaledVertexEmbedding (N k) (mesh k) x)
        boundOne boundTwo
  face : ∀ k c,
    ¬ fkIsingSquareFullFaceFixedBoundary (N k) c →
    fkIsingSquareFullFaceGhostMultiplicity (N k) c = 0 →
      DirectionalFourthOrderHarmonicData (fun z ↦ (Phi z).im)
        (fullSquareScaledFaceEmbedding (N k) (mesh k) c)
        boundOne boundTwo

theorem PhysicalFourthOrderBulkData.vertexLaplacian
    {N : Nat → Nat} {Phi : Complex → Complex} {mesh : Nat → Real}
    (H : PhysicalFourthOrderBulkData N Phi mesh) (k : Nat)
    (x : FKIsingSquareFullVertexNode (N k))
    (hfixed : ¬ fkIsingSquareFullVertexFixedBoundary (N k) x)
    (hghost : fkIsingSquareFullVertexGhostMultiplicity (N k) x = 0) :
    |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph (N k))
      (fun y ↦ (Phi (fullSquareScaledVertexEmbedding
        (N k) (mesh k) y)).im) x| ≤
        (H.boundOne + H.boundTwo) * |mesh k| ^ 4 / 12 := by
  obtain ⟨heast, hnorth, hwest, hsouth⟩ :=
    fullSquareVertex_bulk_directions (N k) x hfixed hghost
  obtain ⟨hgOne, hgTwo, hfourthOne, hfourthTwo, hharmonic⟩ :=
    H.vertex k x hfixed hghost
  exact fullSquareScaledVertex_sampledLaplacian_le_fourthOrder
    (N k) (mesh k) (fun z ↦ (Phi z).im) x
    heast hnorth hwest hsouth H.boundOne H.boundTwo
    hgOne hgTwo hfourthOne hfourthTwo hharmonic

theorem PhysicalFourthOrderBulkData.faceLaplacian
    {N : Nat → Nat} {Phi : Complex → Complex} {mesh : Nat → Real}
    (H : PhysicalFourthOrderBulkData N Phi mesh) (k : Nat)
    (c : FKIsingSquareFullFaceNode (N k))
    (hfixed : ¬ fkIsingSquareFullFaceFixedBoundary (N k) c)
    (hghost : fkIsingSquareFullFaceGhostMultiplicity (N k) c = 0) :
    |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph (N k))
      (fun d ↦ (Phi (fullSquareScaledFaceEmbedding
        (N k) (mesh k) d)).im) c| ≤
        (H.boundOne + H.boundTwo) * |mesh k| ^ 4 / 12 := by
  obtain ⟨heast, hnorth, hwest, hsouth⟩ :=
    fullSquareFace_bulk_coordinates (N k) c hfixed hghost
  obtain ⟨hgOne, hgTwo, hfourthOne, hfourthTwo, hharmonic⟩ :=
    H.face k c hfixed hghost
  exact fullSquareScaledFace_sampledLaplacian_le_fourthOrder
    (N k) (mesh k) (fun z ↦ (Phi z).im) c
    heast hnorth hwest hsouth H.boundOne H.boundTwo
    hgOne hgTwo hfourthOne hfourthTwo hharmonic




structure PhysicalRobinConsistencyInputs
    (N : Nat → Nat) (hN : ∀ k, 0 < N k)
    (Phi : Complex → Complex) (mesh laplacianRate : Nat → Real) where
  mesh_nonneg : ∀ k, 0 ≤ mesh k
  laplacian_nonneg : ∀ k, 0 ≤ laplacianRate k
  vertexFixed : ∀ k x, fkIsingSquareFullVertexFixedBoundary (N k) x →
    (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im = 0
  faceFixed : ∀ k c, fkIsingSquareFullFaceFixedBoundary (N k) c →
    (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im = 1
  vertexFree : ∀ k x,
    ¬ fkIsingSquareFullVertexFixedBoundary (N k) x →
    0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x →
      (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im = 1
  faceFree : ∀ k c,
    ¬ fkIsingSquareFullFaceFixedBoundary (N k) c →
    0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c →
      (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im = 0
  vertexLaplacian : ∀ k x,
    ¬ fkIsingSquareFullVertexFixedBoundary (N k) x →
      |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph (N k))
        (fun y ↦ (Phi (fullSquareScaledVertexEmbedding
          (N k) (mesh k) y)).im) x| ≤ laplacianRate k
  faceLaplacian : ∀ k c,
    ¬ fkIsingSquareFullFaceFixedBoundary (N k) c →
      |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph (N k))
        (fun d ↦ (Phi (fullSquareScaledFaceEmbedding
          (N k) (mesh k) d)).im) c| ≤ laplacianRate k
  mesh_tendsto : Tendsto mesh atTop (nhds 0)
  scaledLaplacian_tendsto : Tendsto
    (fun k ↦ laplacianRate k * (N k : Real) ^ 2) atTop (nhds 0)




structure PhysicalSplitRobinConsistencyInputs
    (N : Nat → Nat) (hN : ∀ k, 0 < N k)
    (Phi : Complex → Complex)
    (mesh bulkRate layerRate : Nat → Real) where
  mesh_nonneg : ∀ k, 0 ≤ mesh k
  bulk_nonneg : ∀ k, 0 ≤ bulkRate k
  layer_nonneg : ∀ k, 0 ≤ layerRate k
  vertexFixed : ∀ k x, fkIsingSquareFullVertexFixedBoundary (N k) x →
    (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im = 0
  faceFixed : ∀ k c, fkIsingSquareFullFaceFixedBoundary (N k) c →
    (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im = 1
  vertexFree : ∀ k x,
    ¬ fkIsingSquareFullVertexFixedBoundary (N k) x →
    0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x →
      (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im = 1
  faceFree : ∀ k c,
    ¬ fkIsingSquareFullFaceFixedBoundary (N k) c →
    0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c →
      (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im = 0
  vertexBulk : ∀ k x,
    ¬ fkIsingSquareFullVertexFixedBoundary (N k) x →
    fkIsingSquareFullVertexGhostMultiplicity (N k) x = 0 →
      |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph (N k))
        (fun y ↦ (Phi (fullSquareScaledVertexEmbedding
          (N k) (mesh k) y)).im) x| ≤ bulkRate k
  faceBulk : ∀ k c,
    ¬ fkIsingSquareFullFaceFixedBoundary (N k) c →
    fkIsingSquareFullFaceGhostMultiplicity (N k) c = 0 →
      |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph (N k))
        (fun d ↦ (Phi (fullSquareScaledFaceEmbedding
          (N k) (mesh k) d)).im) c| ≤ bulkRate k
  vertexLayer : ∀ k x,
    ¬ fkIsingSquareFullVertexFixedBoundary (N k) x →
    0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x →
      |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph (N k))
        (fun y ↦ (Phi (fullSquareScaledVertexEmbedding
          (N k) (mesh k) y)).im) x| ≤ layerRate k
  faceLayer : ∀ k c,
    ¬ fkIsingSquareFullFaceFixedBoundary (N k) c →
    0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c →
      |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph (N k))
        (fun d ↦ (Phi (fullSquareScaledFaceEmbedding
          (N k) (mesh k) d)).im) c| ≤ layerRate k
  scaledBulk_tendsto : Tendsto
    (fun k ↦ bulkRate k * (N k : Real) ^ 2) atTop (nhds 0)
  layer_tendsto : Tendsto layerRate atTop (nhds 0)
  mesh_tendsto : Tendsto mesh atTop (nhds 0)




theorem PhysicalSplitRobinConsistencyInputs.ofFourthOrderAndLipschitz
    {N : Nat → Nat} {hN : ∀ k, 0 < N k}
    {Phi : Complex → Complex} {mesh : Nat → Real}
    (Hfourth : PhysicalFourthOrderBulkData N Phi mesh)
    (L : NNReal) (hPhi : LipschitzWith L (fun z ↦ (Phi z).im))
    (hmesh_nonneg : ∀ k, 0 ≤ mesh k)
    (hvertexFixed : ∀ k x,
      fkIsingSquareFullVertexFixedBoundary (N k) x →
        (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im = 0)
    (hfaceFixed : ∀ k c,
      fkIsingSquareFullFaceFixedBoundary (N k) c →
        (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im = 1)
    (hvertexFree : ∀ k x,
      ¬ fkIsingSquareFullVertexFixedBoundary (N k) x →
      0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x →
        (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im = 1)
    (hfaceFree : ∀ k c,
      ¬ fkIsingSquareFullFaceFixedBoundary (N k) c →
      0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c →
        (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im = 0)
    (hmesh_tendsto : Tendsto mesh atTop (nhds 0))
    (hscaledFourth_tendsto : Tendsto
      (fun k ↦ |mesh k| ^ 4 * (N k : Real) ^ 2) atTop (nhds 0)) :
    PhysicalSplitRobinConsistencyInputs N hN Phi mesh
      (fun k ↦ (Hfourth.boundOne + Hfourth.boundTwo) * |mesh k| ^ 4 / 12)
      (fun k ↦ 8 * (L : Real) * |mesh k|) := by
  refine
    { mesh_nonneg := hmesh_nonneg
      bulk_nonneg := ?_
      layer_nonneg := ?_
      vertexFixed := hvertexFixed
      faceFixed := hfaceFixed
      vertexFree := hvertexFree
      faceFree := hfaceFree
      vertexBulk := ?_
      faceBulk := ?_
      vertexLayer := ?_
      faceLayer := ?_
      scaledBulk_tendsto := ?_
      layer_tendsto := ?_
      mesh_tendsto := hmesh_tendsto }
  · intro k
    exact div_nonneg
      (mul_nonneg Hfourth.boundSum_nonneg (pow_nonneg (abs_nonneg _) 4))
      (by norm_num)
  · intro k
    exact mul_nonneg
      (mul_nonneg (by norm_num) L.2) (abs_nonneg _)
  · intro k x hfixed hghost
    exact Hfourth.vertexLaplacian k x hfixed hghost
  · intro k c hfixed hghost
    exact Hfourth.faceLaplacian k c hfixed hghost
  · intro k x _hfixed _hghost
    exact fullSquareScaledVertex_sampledLaplacian_le_lipschitz
      (N k) (mesh k) Phi L hPhi x
  · intro k c _hfixed _hghost
    exact fullSquareScaledFace_sampledLaplacian_le_lipschitz
      (N k) (mesh k) Phi L hPhi c
  · have hconstant : Tendsto
        (fun _ : Nat ↦ (Hfourth.boundOne + Hfourth.boundTwo) / 12)
        atTop (nhds ((Hfourth.boundOne + Hfourth.boundTwo) / 12)) :=
      tendsto_const_nhds
    have hproduct := hconstant.mul hscaledFourth_tendsto
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hproduct
  · have habs : Tendsto (fun k ↦ |mesh k|) atTop (nhds 0) := by
      simpa using hmesh_tendsto.abs
    simpa using tendsto_const_nhds.mul habs




theorem PhysicalSplitRobinConsistencyInputs.primitive_convergence
    {N : Nat → Nat} {hN : ∀ k, 0 < N k}
    {Phi : Complex → Complex}
    {mesh bulkRate layerRate : Nat → Real}
    (H : PhysicalSplitRobinConsistencyInputs
      N hN Phi mesh bulkRate layerRate)
    (lipschitzConstant : NNReal)
    (hPhi : LipschitzWith lipschitzConstant (fun z ↦ (Phi z).im)) :
    ∀ eta : Real, 0 < eta → ∀ᶠ k in atTop,
      ∀ e : FKIsingSquareInteriorRadialIncidence (N k) (hN k),
        |(fkIsingSquareBoundaryLayerCoordinateOneForm
              (N k) (hN k)).vertexPrimitive
            (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e) -
              (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k)
                (fkIsingSquareInteriorRadialEndpoint
                  (N k) (hN k) e))).im| < eta ∧
          |(fkIsingSquareBoundaryLayerCoordinateOneForm
              (N k) (hN k)).facePrimitive
            (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e) -
              (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k)
                (fkIsingSquareInteriorRadialEndpoint
                  (N k) (hN k) e))).im| < eta := by
  let upper : Nat → Real := fun k ↦
    vertexBarrierGrowthConstant * (bulkRate k * (N k : Real) ^ 2) +
      (1 / isingFermionicGhostCoefficient) * layerRate k +
      (lipschitzConstant : Real) * mesh k
  have hupper : Tendsto upper atTop (nhds 0) := by
    have hbulk : Tendsto
        (fun k ↦ vertexBarrierGrowthConstant *
          (bulkRate k * (N k : Real) ^ 2)) atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul H.scaledBulk_tendsto
    have hlayer : Tendsto
        (fun k ↦ (1 / isingFermionicGhostCoefficient) * layerRate k)
        atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul H.layer_tendsto
    have hmesh : Tendsto
        (fun k ↦ (lipschitzConstant : Real) * mesh k)
        atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul H.mesh_tendsto
    simpa [upper] using (hbulk.add hlayer).add hmesh
  intro eta heta
  have heventually : ∀ᶠ k in atTop, dist (upper k) 0 < eta :=
    (Metric.tendsto_nhds.1 hupper) eta heta
  filter_upwards [heventually] with k hk
  intro e
  have hupper_nonneg : 0 ≤ upper k := by
    dsimp only [upper]
    exact add_nonneg
      (add_nonneg
        (mul_nonneg vertexBarrierGrowthConstant_nonneg
          (mul_nonneg (H.bulk_nonneg k) (sq_nonneg _)))
        (mul_nonneg
          (div_nonneg (by norm_num)
            isingFermionicGhostCoefficient_pos.le)
          (H.layer_nonneg k)))
      (mul_nonneg lipschitzConstant.2 (H.mesh_nonneg k))
  have hk' : upper k < eta := by
    simpa [Real.dist_eq, abs_of_nonneg hupper_nonneg] using hk
  let vertexEmbedding :=
    fullSquareScaledVertexEmbedding (N k) (mesh k)
  let faceEmbedding :=
    fullSquareScaledFaceEmbedding (N k) (mesh k)
  let x := fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e
  let c := fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e
  have hv := vertexSampled_target_error_le_split
    (N k) (hN k) vertexEmbedding Phi (bulkRate k) (layerRate k)
    (H.bulk_nonneg k) (H.layer_nonneg k) (H.vertexBulk k)
    (H.vertexLayer k) (H.vertexFree k) (some x)
  have hvBoundary : vertexBoundaryConsistencyError (N k) (hN k)
      (vertexSampledImaginaryTarget (N k) vertexEmbedding Phi) = 0 :=
    vertexSampled_boundaryConsistencyError_eq_zero
      (N k) (hN k) vertexEmbedding Phi (H.vertexFixed k)
  have hvBarrier := vertexExplicitPoissonBarrierBound_le_growth
    (N k) (hN k)
  have hv' : |vertexDirichlet (N k) (hN k) (some x) -
      (Phi (vertexEmbedding x)).im| ≤ upper k := by
    calc
      _ ≤ vertexBoundaryConsistencyError (N k) (hN k)
            (vertexSampledImaginaryTarget (N k) vertexEmbedding Phi) +
          bulkRate k * vertexExplicitPoissonBarrierBound (N k) +
          layerRate k * (1 / isingFermionicGhostCoefficient) := hv
      _ ≤ 0 + bulkRate k *
            (vertexBarrierGrowthConstant * (N k : Real) ^ 2) +
          layerRate k * (1 / isingFermionicGhostCoefficient) := by
        rw [hvBoundary]
        gcongr
        exact H.bulk_nonneg k
      _ ≤ upper k := by
        dsimp only [upper]
        have hm : 0 ≤ (lipschitzConstant : Real) * mesh k :=
          mul_nonneg lipschitzConstant.2 (H.mesh_nonneg k)
        nlinarith
  have hf := faceSampled_target_error_le_split
    (N k) (hN k) faceEmbedding Phi (bulkRate k) (layerRate k)
    (H.bulk_nonneg k) (H.layer_nonneg k) (H.faceBulk k)
    (H.faceLayer k) (H.faceFree k) (some c)
  have hfBoundary : faceBoundaryConsistencyError (N k) (hN k)
      (faceSampledImaginaryTarget (N k) faceEmbedding Phi) = 0 :=
    faceSampled_boundaryConsistencyError_eq_zero
      (N k) (hN k) faceEmbedding Phi (H.faceFixed k)
  have hfBarrier : faceExplicitPoissonBarrierBound (N k) ≤
      vertexBarrierGrowthConstant * (N k : Real) ^ 2 := by
    calc
      faceExplicitPoissonBarrierBound (N k) =
          (1 / 2 : Real) * (N k : Real) ^ 2 := by
        unfold faceExplicitPoissonBarrierBound
        ring
      _ ≤ vertexBarrierGrowthConstant * (N k : Real) ^ 2 :=
        mul_le_mul_of_nonneg_right half_le_vertexBarrierGrowthConstant
          (sq_nonneg _)
  have hfOwn : |faceDirichlet (N k) (hN k) (some c) -
      (Phi (faceEmbedding c)).im| ≤
        vertexBarrierGrowthConstant * (bulkRate k * (N k : Real) ^ 2) +
          (1 / isingFermionicGhostCoefficient) * layerRate k := by
    calc
      _ ≤ faceBoundaryConsistencyError (N k) (hN k)
            (faceSampledImaginaryTarget (N k) faceEmbedding Phi) +
          bulkRate k * faceExplicitPoissonBarrierBound (N k) +
          layerRate k * (1 / isingFermionicGhostCoefficient) := hf
      _ ≤ 0 + bulkRate k *
            (vertexBarrierGrowthConstant * (N k : Real) ^ 2) +
          layerRate k * (1 / isingFermionicGhostCoefficient) := by
        rw [hfBoundary]
        gcongr
        exact H.bulk_nonneg k
      _ = _ := by ring
  have hmismatch : |(Phi (faceEmbedding c)).im -
      (Phi (vertexEmbedding x)).im| ≤
        (lipschitzConstant : Real) * mesh k := by
    rw [← Real.dist_eq]
    calc
      dist (Phi (faceEmbedding c)).im (Phi (vertexEmbedding x)).im ≤
          lipschitzConstant * dist (faceEmbedding c) (vertexEmbedding x) :=
        hPhi.dist_le_mul _ _
      _ ≤ lipschitzConstant * mesh k :=
        mul_le_mul_of_nonneg_left
          (fullSquareScaledEmbedding_incidenceDistance
            N hN mesh H.mesh_nonneg k e) lipschitzConstant.2
  have hf' : |faceDirichlet (N k) (hN k) (some c) -
      (Phi (vertexEmbedding x)).im| ≤ upper k := by
    rw [show faceDirichlet (N k) (hN k) (some c) -
        (Phi (vertexEmbedding x)).im =
      (faceDirichlet (N k) (hN k) (some c) -
        (Phi (faceEmbedding c)).im) +
      ((Phi (faceEmbedding c)).im - (Phi (vertexEmbedding x)).im) by ring]
    calc
      |_ + _| ≤ |faceDirichlet (N k) (hN k) (some c) -
          (Phi (faceEmbedding c)).im| +
        |(Phi (faceEmbedding c)).im -
          (Phi (vertexEmbedding x)).im| := abs_add_le _ _
      _ ≤ (vertexBarrierGrowthConstant *
            (bulkRate k * (N k : Real) ^ 2) +
          (1 / isingFermionicGhostCoefficient) * layerRate k) +
            (lipschitzConstant : Real) * mesh k :=
        add_le_add hfOwn hmismatch
      _ = upper k := by rfl
  have hphysical := physicalIncidence_close_of_dirichlet_close
    (N k) (hN k) e (Phi (vertexEmbedding x)).im (upper k) hv' hf'
  exact ⟨hphysical.1.trans_lt hk', hphysical.2.trans_lt hk'⟩




theorem PhysicalRobinConsistencyInputs.primitive_convergence
    {N : Nat → Nat} {hN : ∀ k, 0 < N k}
    {Phi : Complex → Complex} {mesh laplacianRate : Nat → Real}
    (H : PhysicalRobinConsistencyInputs N hN Phi mesh laplacianRate)
    (lipschitzConstant : NNReal)
    (hPhi : LipschitzWith lipschitzConstant (fun z ↦ (Phi z).im)) :
    ∀ eta : Real, 0 < eta → ∀ᶠ k in atTop,
      ∀ e : FKIsingSquareInteriorRadialIncidence (N k) (hN k),
        |(fkIsingSquareBoundaryLayerCoordinateOneForm
              (N k) (hN k)).vertexPrimitive
            (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e) -
              (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k)
                (fkIsingSquareInteriorRadialEndpoint
                  (N k) (hN k) e))).im| < eta ∧
          |(fkIsingSquareBoundaryLayerCoordinateOneForm
              (N k) (hN k)).facePrimitive
            (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e) -
              (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k)
                (fkIsingSquareInteriorRadialEndpoint
                  (N k) (hN k) e))).im| < eta := by
  exact physicalIncidence_uniform_convergence_of_scaledExactBoundaryAndLaplacian
    N hN Phi mesh laplacianRate lipschitzConstant H.mesh_nonneg
    H.laplacian_nonneg H.vertexFixed H.faceFixed H.vertexFree H.faceFree
    H.vertexLaplacian H.faceLaplacian hPhi H.mesh_tendsto
    H.scaledLaplacian_tendsto

end FKIsingSquareBoundaryLayerCoordinateOneForm

end

end StatMech.Universality
