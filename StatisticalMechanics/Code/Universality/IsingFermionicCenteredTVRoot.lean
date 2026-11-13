/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicCenteredTVRegularity
import Code.Universality.IsingFermionicCenteredRootReduction










open Filter Set Topology

namespace StatMech.Universality

noncomputable section



theorem fkIsingExpandingBoundarySquareCenteredRootNode_edges_le_fullCarrierTV
    (k : Nat) (hk : 2 ≤ k) :
    ‖fkIsingExpandingBoundarySquareCenteredRootNode k 1 0 -
        fkIsingExpandingBoundarySquareCenteredRootNode k 1 1‖ ≤
          fkIsingExpandingSquareScale k * 2432 ∧
      ‖fkIsingExpandingBoundarySquareCenteredRootNode k 1 1 -
        fkIsingExpandingBoundarySquareCenteredRootNode k 0 1‖ ≤
          fkIsingExpandingSquareScale k * 2432 ∧
      ‖fkIsingExpandingBoundarySquareCenteredRootNode k 0 1 -
        fkIsingExpandingBoundarySquareCenteredRootNode k 0 0‖ ≤
          fkIsingExpandingSquareScale k * 2432 ∧
      ‖fkIsingExpandingBoundarySquareCenteredRootNode k 0 0 -
        fkIsingExpandingBoundarySquareCenteredRootNode k 1 0‖ ≤
          fkIsingExpandingSquareScale k * 2432 := by
  let n := fkIsingExpandingSquareSide k
  let rho := (k / 2) * (k + 1)
  have hn : 0 < n := fkIsingExpandingSquareSide_pos k
  have hnLarge : 3 ≤ n := by
    dsimp [n, fkIsingExpandingSquareSide]
    nlinarith
  have hrho : 0 < rho := by
    dsimp [rho]
    exact Nat.mul_pos (Nat.div_pos (by omega) (by norm_num)) (by omega)
  have hrho_le : rho ≤ k * (k + 1) := by
    dsimp [rho]
    exact Nat.mul_le_mul_right (k + 1) (Nat.div_le_self k 2)
  have hn_eq : n = k * (k + 1) + (k + 1) := by
    dsimp [n, fkIsingExpandingSquareSide]
    ring
  have hrho_side : rho ≤ n - 2 := by omega
  have hsucc : 1 + (fkIsingExpandingSquareSide k - 1) =
      fkIsingExpandingSquareSide k := by
    have := fkIsingExpandingSquareSide_pos k
    omega
  have hedges :=
    fkIsingSquareBoundaryCenteredRadialPatchFullObservable_cell_edges_le_of_margin
      n n n rho (fkIsingExpandingSquareMesh k) hn
      (by omega) (by omega) (by omega) (by omega) hrho
      (fkIsingExpandingSquareMesh_pos k)
      (by omega) (by omega) (by omega) (by omega)
  have hcoefficient := fkIsingExpandingSquare_fullCarrierTVCoefficient_le k hk
  constructor
  · convert hedges.1.trans hcoefficient using 1 <;>
      simp [fkIsingExpandingBoundarySquareCenteredRootNode, n,
        hsucc, Real.sqrt_mul (by norm_num : (0 : Real) ≤ 2)]
  constructor
  · convert hedges.2.1.trans hcoefficient using 1 <;>
      simp [fkIsingExpandingBoundarySquareCenteredRootNode, n,
        hsucc, Real.sqrt_mul (by norm_num : (0 : Real) ≤ 2)]
  constructor
  · convert hedges.2.2.1.trans hcoefficient using 1 <;>
      simp [fkIsingExpandingBoundarySquareCenteredRootNode, n,
        hsucc, Real.sqrt_mul (by norm_num : (0 : Real) ≤ 2)]
  · convert hedges.2.2.2.trans hcoefficient using 1 <;>
      simp [fkIsingExpandingBoundarySquareCenteredRootNode, n,
        hsucc, Real.sqrt_mul (by norm_num : (0 : Real) ≤ 2)]



theorem
    fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_root_tendsto_fullCarrierTV
    (target : Complex → Complex)
    (hbase : Tendsto
      (fun k ↦ fkIsingExpandingBoundarySquareCenteredRootNode k 0 0)
      atTop (nhds (target 0))) :
    Tendsto
      (fun k ↦ fkIsingExpandingBoundarySquareCenteredReflectedInterpolant k
        fkIsingExpandingBoundarySquareCaratheodoryApproximation.root)
      atTop (nhds (target
        fkIsingExpandingBoundarySquareCaratheodoryApproximation.root)) := by
  have hscale : Tendsto
      (fun k ↦ fkIsingExpandingSquareScale k * (2432 : Real))
      atTop (nhds 0) := by
    simpa [mul_comm] using
      fkIsingExpandingSquareScale_tendsto_zero.const_mul (2432 : Real)
  have tendstoDiff (f : Nat → Complex)
      (hf : ∀ᶠ k in atTop,
        ‖f k‖ ≤ fkIsingExpandingSquareScale k * (2432 : Real)) :
      Tendsto f atTop (nhds 0) := by
    rw [Metric.tendsto_nhds]
    intro epsilon hepsilon
    have hepsilonScale := (Metric.tendsto_nhds.1 hscale) epsilon hepsilon
    filter_upwards [hf, hepsilonScale] with k hkBound hkScale
    rw [dist_zero_right]
    refine lt_of_le_of_lt hkBound ?_
    have hnonneg :
        0 ≤ fkIsingExpandingSquareScale k * (2432 : Real) :=
      mul_nonneg (fkIsingExpandingSquareScale_pos k).le (by norm_num)
    simpa [Real.dist_eq, abs_of_nonneg hnonneg,
      abs_of_pos (fkIsingExpandingSquareScale_pos k)] using hkScale
  have h10Bound : ∀ᶠ k in atTop,
      ‖fkIsingExpandingBoundarySquareCenteredRootNode k 1 0 -
        fkIsingExpandingBoundarySquareCenteredRootNode k 0 0‖ ≤
          fkIsingExpandingSquareScale k * (2432 : Real) := by
    filter_upwards [eventually_ge_atTop 2] with k hk
    rw [norm_sub_rev]
    exact (fkIsingExpandingBoundarySquareCenteredRootNode_edges_le_fullCarrierTV
      k hk).2.2.2
  have h01Bound : ∀ᶠ k in atTop,
      ‖fkIsingExpandingBoundarySquareCenteredRootNode k 0 1 -
        fkIsingExpandingBoundarySquareCenteredRootNode k 0 0‖ ≤
          fkIsingExpandingSquareScale k * (2432 : Real) := by
    filter_upwards [eventually_ge_atTop 2] with k hk
    exact (fkIsingExpandingBoundarySquareCenteredRootNode_edges_le_fullCarrierTV
      k hk).2.2.1
  have h11Bound : ∀ᶠ k in atTop,
      ‖fkIsingExpandingBoundarySquareCenteredRootNode k 1 1 -
        fkIsingExpandingBoundarySquareCenteredRootNode k 1 0‖ ≤
          fkIsingExpandingSquareScale k * (2432 : Real) := by
    filter_upwards [eventually_ge_atTop 2] with k hk
    rw [norm_sub_rev]
    exact (fkIsingExpandingBoundarySquareCenteredRootNode_edges_le_fullCarrierTV
      k hk).1
  have h10Diff := tendstoDiff _ h10Bound
  have h01Diff := tendstoDiff _ h01Bound
  have h11Diff := tendstoDiff _ h11Bound
  have h10 : Tendsto
      (fun k ↦ fkIsingExpandingBoundarySquareCenteredRootNode k 1 0)
      atTop (nhds (target 0)) := by
    convert h10Diff.add hbase using 1 <;> simp
  have h01 : Tendsto
      (fun k ↦ fkIsingExpandingBoundarySquareCenteredRootNode k 0 1)
      atTop (nhds (target 0)) := by
    convert h01Diff.add hbase using 1 <;> simp
  have h11 : Tendsto
      (fun k ↦ fkIsingExpandingBoundarySquareCenteredRootNode k 1 1)
      atTop (nhds (target 0)) := by
    convert h11Diff.add h10 using 1 <;> simp
  apply
    fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_root_tendsto_of_center_nodes
      target
  intro a b
  fin_cases a <;> fin_cases b
  · exact hbase
  · exact h01
  · exact h10
  · exact h11



theorem fkIsingExpandingBoundarySquareCenteredRootNode_sub_base_tendsto_fullCarrierTV
    (a b : Fin 2) :
    Tendsto
      (fun k ↦ fkIsingExpandingBoundarySquareCenteredRootNode k a b -
        fkIsingExpandingBoundarySquareCenteredRootNode k 0 0)
      atTop (nhds 0) := by
  have hscale : Tendsto
      (fun k ↦ fkIsingExpandingSquareScale k * (2432 : Real))
      atTop (nhds 0) := by
    simpa [mul_comm] using
      fkIsingExpandingSquareScale_tendsto_zero.const_mul (2432 : Real)
  have tendstoDiff (f : Nat → Complex)
      (hf : ∀ᶠ k in atTop,
        ‖f k‖ ≤ fkIsingExpandingSquareScale k * (2432 : Real)) :
      Tendsto f atTop (nhds 0) := by
    rw [Metric.tendsto_nhds]
    intro epsilon hepsilon
    have hepsilonScale := (Metric.tendsto_nhds.1 hscale) epsilon hepsilon
    filter_upwards [hf, hepsilonScale] with k hkBound hkScale
    rw [dist_zero_right]
    refine lt_of_le_of_lt hkBound ?_
    have hnonneg :
        0 ≤ fkIsingExpandingSquareScale k * (2432 : Real) :=
      mul_nonneg (fkIsingExpandingSquareScale_pos k).le (by norm_num)
    simpa [Real.dist_eq, abs_of_nonneg hnonneg,
      abs_of_pos (fkIsingExpandingSquareScale_pos k)] using hkScale
  have h10 : Tendsto
      (fun k ↦ fkIsingExpandingBoundarySquareCenteredRootNode k 1 0 -
        fkIsingExpandingBoundarySquareCenteredRootNode k 0 0)
      atTop (nhds 0) := by
    apply tendstoDiff
    filter_upwards [eventually_ge_atTop 2] with k hk
    rw [norm_sub_rev]
    exact (fkIsingExpandingBoundarySquareCenteredRootNode_edges_le_fullCarrierTV
      k hk).2.2.2
  have h01 : Tendsto
      (fun k ↦ fkIsingExpandingBoundarySquareCenteredRootNode k 0 1 -
        fkIsingExpandingBoundarySquareCenteredRootNode k 0 0)
      atTop (nhds 0) := by
    apply tendstoDiff
    filter_upwards [eventually_ge_atTop 2] with k hk
    exact (fkIsingExpandingBoundarySquareCenteredRootNode_edges_le_fullCarrierTV
      k hk).2.2.1
  have h11_10 : Tendsto
      (fun k ↦ fkIsingExpandingBoundarySquareCenteredRootNode k 1 1 -
        fkIsingExpandingBoundarySquareCenteredRootNode k 1 0)
      atTop (nhds 0) := by
    apply tendstoDiff
    filter_upwards [eventually_ge_atTop 2] with k hk
    rw [norm_sub_rev]
    exact (fkIsingExpandingBoundarySquareCenteredRootNode_edges_le_fullCarrierTV
      k hk).1
  have ha : a = 0 ∨ a = 1 := by
    fin_cases a
    · exact Or.inl rfl
    · exact Or.inr (Fin.ext rfl)
  have hb : b = 0 ∨ b = 1 := by
    fin_cases b
    · exact Or.inl rfl
    · exact Or.inr (Fin.ext rfl)
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · simpa using tendsto_const_nhds (x := (0 : Complex))
  · exact h01
  · exact h10
  · convert h11_10.add h10 using 1 <;> ring





theorem
    fkIsingExpandingBoundarySquareCenteredRootNode_tendsto_iff_root_tendsto_fullCarrierTV
    (target : Complex → Complex) :
    Tendsto
        (fun k ↦ fkIsingExpandingBoundarySquareCenteredRootNode k 0 0)
        atTop (nhds (target 0)) ↔
      Tendsto
        (fun k ↦ fkIsingExpandingBoundarySquareCenteredReflectedInterpolant k
          fkIsingExpandingBoundarySquareCaratheodoryApproximation.root)
        atTop (nhds (target
          fkIsingExpandingBoundarySquareCaratheodoryApproximation.root)) := by
  constructor
  · exact
      fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_root_tendsto_fullCarrierTV
        target
  · intro hroot
    have h00 :=
      fkIsingExpandingBoundarySquareCenteredRootNode_sub_base_tendsto_fullCarrierTV
        (0 : Fin 2) (0 : Fin 2)
    have h10 :=
      fkIsingExpandingBoundarySquareCenteredRootNode_sub_base_tendsto_fullCarrierTV
        (1 : Fin 2) (0 : Fin 2)
    have h01 :=
      fkIsingExpandingBoundarySquareCenteredRootNode_sub_base_tendsto_fullCarrierTV
        (0 : Fin 2) (1 : Fin 2)
    have h11 :=
      fkIsingExpandingBoundarySquareCenteredRootNode_sub_base_tendsto_fullCarrierTV
        (1 : Fin 2) (1 : Fin 2)
    have hinterpSub : Tendsto
        (fun k ↦
          fkIsingExpandingBoundarySquareCenteredReflectedInterpolant k 0 -
            fkIsingExpandingBoundarySquareCenteredRootNode k 0 0)
        atTop (nhds 0) := by
      have hsum := (((h00.add h10).add h01).add h11).const_mul
        (1 / 4 : Complex)
      convert hsum using 1
      · funext k
        rw [fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_zero_eq_center_average]
        ring
      · ring
    have hbase := hinterpSub.neg.add hroot
    simpa [fkIsingExpandingBoundarySquareCaratheodoryApproximation] using hbase

end

end StatMech.Universality
