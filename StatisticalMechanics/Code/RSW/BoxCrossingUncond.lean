/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


























































import Mathlib
import Code.RSW.Defs
import Code.RSW.Strip
import Code.RSW.SelfDuality
import Code.Lattice.CrossingParity
import Code.Lattice.FaceRegion
import Code.Universality.Defs
import Code.Inequalities.IncreasingEvent

open Set MeasureTheory SimpleGraph
open scoped ENNReal NNReal

namespace StatMech

namespace RSW

namespace Uncond

open StatMech.Lattice
open StatMech.RSW.Box
open StatMech.RSW.Strip
open StatMech.Universality














def leftReach (ω : ConfigSpace (Sym2 (Site 2))) (x₀ : Site 2) : Set (Site 2) :=
  cluster 2 ω x₀

@[simp] theorem mem_leftReach {ω : ConfigSpace (Sym2 (Site 2))} {x₀ y : Site 2} :
    y ∈ leftReach ω x₀ ↔ Connected 2 ω x₀ y := Iff.rfl

theorem self_mem_leftReach (ω : ConfigSpace (Sym2 (Site 2))) (x₀ : Site 2) :
    x₀ ∈ leftReach ω x₀ := self_mem_cluster ω x₀








theorem noPrimalConn_separated (ω : ConfigSpace (Sym2 (Site 2))) (x₀ : Site 2)
    {y₀ : Site 2} (hy₀ : ¬ Connected 2 ω x₀ y₀) :
    ¬ (latticeMinusBarrier (leftReach ω x₀)).Reachable x₀ y₀ :=
  cluster_separated_from_exterior x₀ (by simpa [leftReach, mem_cluster] using hy₀)







theorem noPrimalConn_dualBarrier (ω : ConfigSpace (Sym2 (Site 2))) (x₀ : Site 2)
    {x y : Site 2} (hadj : (hypercubicLattice 2).Adj x y)
    (hmem : s(x, y) ∈ bdEdgeSet2 (leftReach ω x₀)) :
    ω s(x, y) = false ∧ dualConfig ω (crossEdge s(x, y)) = true :=
  ⟨cluster_cutEdge_isClosed x₀ hadj hmem, cluster_cutEdge_crosses_dual_open x₀ hadj hmem⟩






theorem escape_crosses_dualBarrier_oddly (ω : ConfigSpace (Sym2 (Site 2))) (x₀ : Site 2)
    {y : Site 2} (hy : ¬ Connected 2 ω x₀ y)
    (w : (hypercubicLattice 2).Walk x₀ y) :
    ¬ Even (crossCount (leftReach ω x₀) w) :=
  origin_crossCount_odd x₀ (by simpa [leftReach, mem_cluster] using hy) w














theorem dualBarrierExists (ω : ConfigSpace (Sym2 (Site 2))) (x₀ : Site 2)
    (hfin : (cluster 2 ω x₀).Finite) {y₀ : Site 2}
    (w : (hypercubicLattice 2).Walk x₀ y₀) (hy₀ : ¬ Connected 2 ω x₀ y₀) :
    (∃ (u : Site 2) (c : (faceBoundaryGraph (leftReach ω x₀)).Walk u u), c.IsCycle) ∧
      ¬ (latticeMinusBarrier (leftReach ω x₀)).Reachable x₀ y₀ ∧
      ∀ γ : (hypercubicLattice 2).Walk x₀ y₀,
        ¬ Even (crossCount (leftReach ω x₀) γ) := by
  have hzc : y₀ ∉ cluster 2 ω x₀ := by simpa [mem_cluster] using hy₀
  exact cluster_enclosed_with_winding x₀ hfin w hzc


















theorem primal_or_dualBarrier (ω : ConfigSpace (Sym2 (Site 2))) (x₀ : Site 2)
    (hfin : (cluster 2 ω x₀).Finite) {y₀ : Site 2}
    (w : (hypercubicLattice 2).Walk x₀ y₀) :
    Connected 2 ω x₀ y₀ ∨
      ((∃ (u : Site 2) (c : (faceBoundaryGraph (leftReach ω x₀)).Walk u u), c.IsCycle) ∧
        ¬ (latticeMinusBarrier (leftReach ω x₀)).Reachable x₀ y₀ ∧
        (∀ γ : (hypercubicLattice 2).Walk x₀ y₀,
          ¬ Even (crossCount (leftReach ω x₀) γ))) := by
  rcases Classical.em (Connected 2 ω x₀ y₀) with hconn | hconn
  · exact Or.inl hconn
  · exact Or.inr (dualBarrierExists ω x₀ hfin w hconn)









theorem dualBarrier_isOpenDual (ω : ConfigSpace (Sym2 (Site 2))) (x₀ : Site 2)
    {x y : Site 2} (hadj : (hypercubicLattice 2).Adj x y)
    (hmem : s(x, y) ∈ bdEdgeSet2 (leftReach ω x₀)) :
    dualConfig ω (crossEdge s(x, y)) = true :=
  (noPrimalConn_dualBarrier ω x₀ hadj hmem).2












def squareCross (n : ℤ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  horizontalCrossingEvent 0 n 0 n


def squareDualCross (n : ℤ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  dualVerticalCrossingEvent 0 n 0 n











theorem square_cross_ge_half (μ : Measure (ConfigSpace (Sym2 (Site 2))))
    [IsProbabilityMeasure μ] (n : ℤ)
    (hsep : (squareCross n)ᶜ ⊆ squareDualCross n)
    (hselfDual : μ.real (squareDualCross n) = μ.real (squareCross n))
    (hmeas : MeasurableSet (squareCross n)) :
    (1 : ℝ) / 2 ≤ μ.real (squareCross n) := by
  have hcompl : μ.real (squareCross n)ᶜ = 1 - μ.real (squareCross n) := by
    rw [measureReal_compl hmeas, probReal_univ]
  have hmono : μ.real (squareCross n)ᶜ ≤ μ.real (squareDualCross n) :=
    measureReal_mono hsep
  rw [hselfDual, hcompl] at hmono
  linarith










def boxCross (n : ℤ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  horizontalCrossingEvent 0 (2 * n) 0 n



def boxLeftHalf (n : ℤ) (hn : 0 ≤ n) {z : Site 2} (hz0 : z 0 = n) (hzc : 0 ≤ z 1)
    (hzd : z 1 ≤ n) : Set (ConfigSpace (Sym2 (Site 2))) :=
  leftHalfCrossingEvent 0 n 0 n z
    (rightSide_subset (mem_shared_column (a := 0) (m := n) (b := 2 * n) (c := 0) (d := n)
      hn (by linarith) hz0 hzc hzd).1)



def boxRightHalf (n : ℤ) (hn : 0 ≤ n) {z : Site 2} (hz0 : z 0 = n) (hzc : 0 ≤ z 1)
    (hzd : z 1 ≤ n) : Set (ConfigSpace (Sym2 (Site 2))) :=
  rightHalfCrossingEvent n (2 * n) 0 n z
    (leftSide_subset (mem_shared_column (a := 0) (m := n) (b := 2 * n) (c := 0) (d := n)
      hn (by linarith) hz0 hzc hzd).2)





theorem measureReal_boxCross_ge_halves
    (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsFiniteMeasure μ]
    (hpa : PositivelyAssociated μ) (n : ℤ) (hn : 0 ≤ n) {z : Site 2} (hz0 : z 0 = n)
    (hzc : 0 ≤ z 1) (hzd : z 1 ≤ n) :
    μ.real (boxLeftHalf n hn hz0 hzc hzd) * μ.real (boxRightHalf n hn hz0 hzc hzd)
      ≤ μ.real (boxCross n) := by
  have hmb : (n : ℤ) ≤ 2 * n := by linarith
  exact measureReal_horizontalCrossing_ge_halves (a := 0) (m := n) (b := 2 * n) (c := 0)
    (d := n) hn hmb hz0 hzc hzd μ hpa











theorem box_crossing_lower_bound
    (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ]
    (hpa : PositivelyAssociated μ) (n : ℤ) (hn : 0 ≤ n) {z : Site 2} (hz0 : z 0 = n)
    (hzc : 0 ≤ z 1) (hzd : z 1 ≤ n)
    (hleft : (1 : ℝ) / 2 ≤ μ.real (boxLeftHalf n hn hz0 hzc hzd))
    (hright : (1 : ℝ) / 2 ≤ μ.real (boxRightHalf n hn hz0 hzc hzd)) :
    (1 : ℝ) / 4 ≤ μ.real (boxCross n) := by
  have hprod : (1 : ℝ) / 4
      ≤ μ.real (boxLeftHalf n hn hz0 hzc hzd) * μ.real (boxRightHalf n hn hz0 hzc hzd) := by
    have h1 : (0 : ℝ) ≤ μ.real (boxLeftHalf n hn hz0 hzc hzd) := measureReal_nonneg
    nlinarith [hleft, hright, h1]
  exact le_trans hprod (measureReal_boxCross_ge_halves μ hpa n hn hz0 hzc hzd)



theorem box_crossing_lower_bound_pos
    (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ]
    (hpa : PositivelyAssociated μ) (n : ℤ) (hn : 0 ≤ n) {z : Site 2} (hz0 : z 0 = n)
    (hzc : 0 ≤ z 1) (hzd : z 1 ≤ n)
    (hleft : (1 : ℝ) / 2 ≤ μ.real (boxLeftHalf n hn hz0 hzc hzd))
    (hright : (1 : ℝ) / 2 ≤ μ.real (boxRightHalf n hn hz0 hzc hzd)) :
    ∃ c : ℝ, 0 < c ∧ c ≤ μ.real (boxCross n) :=
  ⟨1 / 4, by norm_num,
    box_crossing_lower_bound μ hpa n hn hz0 hzc hzd hleft hright⟩

end Uncond

end RSW

end StatMech
