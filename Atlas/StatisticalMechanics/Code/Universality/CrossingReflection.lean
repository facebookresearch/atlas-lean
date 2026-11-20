/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



























































import Code.Universality.CrossingTranslationInvariance

open Set MeasureTheory SimpleGraph
open scoped ENNReal NNReal

namespace StatMech

namespace Universality

open StatMech.Lattice
open StatMech.RSW.Box
open StatMech.RSW.Strip




def crf_swapFun (x : Site 2) : Site 2 := ![x 1, x 0]




def crf_swap : Site 2 ≃ Site 2 where
  toFun := crf_swapFun
  invFun := crf_swapFun
  left_inv x := by funext i; fin_cases i <;> simp [crf_swapFun]
  right_inv x := by funext i; fin_cases i <;> simp [crf_swapFun]

@[simp] theorem crf_swap_zero (x : Site 2) : (crf_swap x) 0 = x 1 := by
  simp [crf_swap, crf_swapFun]
@[simp] theorem crf_swap_one (x : Site 2) : (crf_swap x) 1 = x 0 := by
  simp [crf_swap, crf_swapFun]
@[simp] theorem crf_swap_symm : crf_swap.symm = crf_swap := rfl
@[simp] theorem crf_swap_involutive (x : Site 2) : crf_swap (crf_swap x) = x := by
  funext i; fin_cases i <;> simp




theorem crf_adj_swap (x y : Site 2) :
    (hypercubicLattice 2).Adj x y ↔ (hypercubicLattice 2).Adj (crf_swap x) (crf_swap y) := by
  rw [hypercubicLattice_adj, hypercubicLattice_adj, Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [crf_swap_zero, crf_swap_one]
  constructor <;> intro h <;> omega




noncomputable def crf_edgeEquiv : Sym2 (Site 2) ≃ Sym2 (Site 2) := sym2Congr crf_swap


theorem crf_edgeEquiv_symm_apply (e : Sym2 (Site 2)) :
    crf_edgeEquiv.symm e = e.map crf_swap := by simp [crf_edgeEquiv, sym2Congr]






noncomputable def crf_swapConfig : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2)) :=
  Equiv.piCongrLeft (fun _ => Bool) crf_edgeEquiv


theorem crf_swapConfig_apply (ω : ConfigSpace (Sym2 (Site 2))) (e : Sym2 (Site 2)) :
    crf_swapConfig ω e = ω (e.map crf_swap) := by
  rw [crf_swapConfig, Equiv.piCongrLeft_apply]; simp [crf_edgeEquiv_symm_apply]


theorem crf_measurable_swapConfig : Measurable crf_swapConfig :=
  (MeasurableEquiv.piCongrLeft (fun _ => Bool) crf_edgeEquiv).measurable






theorem crf_map_swapConfig :
    Measure.map crf_swapConfig rba_selfDualMeasure = rba_selfDualMeasure := by
  rw [crf_swapConfig, rba_selfDualMeasure]
  unfold bernoulliProductMeasure
  exact Measure.infinitePi_map_piCongrLeft
    (fun _ : Sym2 (Site 2) => bernoulliMeasure (2⁻¹ : ℝ≥0) half_le_one) crf_edgeEquiv




theorem crf_swap_invariant :
    MeasurePreserving crf_swapConfig rba_selfDualMeasure rba_selfDualMeasure :=
  ⟨crf_measurable_swapConfig, crf_map_swapConfig⟩






theorem crf_isOpenEdge_swap (ω : ConfigSpace (Sym2 (Site 2))) (x y : Site 2) :
    IsOpenEdge 2 (crf_swapConfig ω) x y ↔ IsOpenEdge 2 ω (crf_swap x) (crf_swap y) := by
  unfold IsOpenEdge
  rw [crf_adj_swap x y]
  have hopen : (crf_swapConfig ω) s(x, y) = true ↔ ω s(crf_swap x, crf_swap y) = true := by
    rw [crf_swapConfig_apply,
      show (s(x, y) : Sym2 (Site 2)).map crf_swap = s(crf_swap x, crf_swap y) from
      Sym2.map_mk _ _ _]
  rw [hopen]



theorem crf_mem_rect_swap (a b c d : ℤ) (x : Site 2) :
    x ∈ rect a b c d ↔ (crf_swap x) ∈ rect c d a b := by
  simp only [mem_rect, crf_swap_zero, crf_swap_one]
  constructor <;> intro h <;> exact ⟨by omega, by omega, by omega, by omega⟩




theorem crf_mem_bottomSide_swap (a b c d : ℤ) (x : Site 2) :
    x ∈ bottomSide a b c d ↔ (crf_swap x) ∈ leftSide c d a b := by
  simp only [mem_bottomSide, mem_leftSide, mem_rect, crf_swap_zero, crf_swap_one]
  constructor <;> rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩ <;>
    exact ⟨⟨by omega, by omega, by omega, by omega⟩, by omega⟩



theorem crf_mem_topSide_swap (a b c d : ℤ) (x : Site 2) :
    x ∈ topSide a b c d ↔ (crf_swap x) ∈ rightSide c d a b := by
  simp only [mem_topSide, mem_rightSide, mem_rect, crf_swap_zero, crf_swap_one]
  constructor <;> rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩ <;>
    exact ⟨⟨by omega, by omega, by omega, by omega⟩, by omega⟩







noncomputable def crf_inducedHom (a b c d : ℤ) (ω : ConfigSpace (Sym2 (Site 2))) :
    (openSubgraphInduce 2 ω (rect a b c d)) →g
      (openSubgraphInduce 2 (crf_swapConfig ω) (rect c d a b)) where
  toFun := fun x => ⟨crf_swap (x : Site 2), (crf_mem_rect_swap a b c d x).1 x.2⟩
  map_rel' := by
    intro x y hxy
    rw [openSubgraphInduce_adj, openSubgraph_adj] at hxy
    obtain ⟨hadj, hopen⟩ := hxy
    show IsOpenEdge 2 (crf_swapConfig ω) (crf_swap (x : Site 2)) (crf_swap (y : Site 2))
    rw [crf_isOpenEdge_swap ω (crf_swap (x : Site 2)) (crf_swap (y : Site 2))]
    simp only [crf_swap_involutive]
    exact ⟨hadj, hopen⟩




noncomputable def crf_inducedHomInv (a b c d : ℤ) (ω : ConfigSpace (Sym2 (Site 2))) :
    (openSubgraphInduce 2 (crf_swapConfig ω) (rect c d a b)) →g
      (openSubgraphInduce 2 ω (rect a b c d)) where
  toFun := fun x => ⟨crf_swap (x : Site 2), (crf_mem_rect_swap c d a b x).1 x.2⟩
  map_rel' := by
    intro x y hxy
    rw [openSubgraphInduce_adj, openSubgraph_adj] at hxy
    obtain ⟨hadj, hopen⟩ := hxy
    show IsOpenEdge 2 ω (crf_swap (x : Site 2)) (crf_swap (y : Site 2))
    exact (crf_isOpenEdge_swap ω (x : Site 2) (y : Site 2)).1 ⟨hadj, hopen⟩






theorem crf_vertical_to_horizontal (a b c d : ℤ) (ω : ConfigSpace (Sym2 (Site 2)))
    (h : VerticalCrossing ω a b c d) :
    HorizontalCrossing (crf_swapConfig ω) c d a b := by
  obtain ⟨x, y, hxy⟩ := h
  refine ⟨⟨crf_swap (x : Site 2), (crf_mem_bottomSide_swap a b c d x).1 x.2⟩,
          ⟨crf_swap (y : Site 2), (crf_mem_topSide_swap a b c d y).1 y.2⟩, ?_⟩
  exact (hxy : (openSubgraphInduce 2 ω (rect a b c d)).Reachable _ _).map
    (crf_inducedHom a b c d ω)




theorem crf_horizontal_to_vertical (a b c d : ℤ) (ω : ConfigSpace (Sym2 (Site 2)))
    (h : HorizontalCrossing (crf_swapConfig ω) c d a b) :
    VerticalCrossing ω a b c d := by
  obtain ⟨x, y, hxy⟩ := h
  refine ⟨⟨crf_swap (x : Site 2), by
            have := crf_mem_bottomSide_swap a b c d (crf_swap (x : Site 2))
            simp only [crf_swap_involutive] at this; exact this.2 x.2⟩,
          ⟨crf_swap (y : Site 2), by
            have := crf_mem_topSide_swap a b c d (crf_swap (y : Site 2))
            simp only [crf_swap_involutive] at this; exact this.2 y.2⟩, ?_⟩
  exact (hxy : (openSubgraphInduce 2 (crf_swapConfig ω) (rect c d a b)).Reachable _ _).map
    (crf_inducedHomInv a b c d ω)






theorem crf_verticalCrossingEvent_swap (a b c d : ℤ) :
    verticalCrossingEvent a b c d = crf_swapConfig ⁻¹' horizontalCrossingEvent c d a b := by
  ext ω
  simp only [Set.mem_preimage, mem_verticalCrossingEvent, mem_horizontalCrossingEvent]
  exact ⟨crf_vertical_to_horizontal a b c d ω, crf_horizontal_to_vertical a b c d ω⟩



















theorem crf_verticalCrossing_eq_horizontal_swap (a b c d : ℤ)
    (hmeas : MeasurableSet (horizontalCrossingEvent c d a b)) :
    rba_selfDualMeasure.real (verticalCrossingEvent a b c d)
      = rba_selfDualMeasure.real (horizontalCrossingEvent c d a b) := by
  rw [crf_verticalCrossingEvent_swap a b c d,
    crf_swap_invariant.measureReal_preimage hmeas.nullMeasurableSet]













theorem crf_hrefl
    (hmeas : ∀ (k0 : ℕ), 2 ≤ k0 → ∀ n : ℤ, 0 < n →
      MeasurableSet (horizontalCrossingEvent 0 ((k0 : ℤ) * n) 0 n)) :
    ∀ (k0 : ℕ), 2 ≤ k0 → ∀ n : ℤ, 0 < n →
      rba_selfDualMeasure.real (verticalCrossingEvent 0 n 0 ((k0 : ℤ) * n))
        = rba_selfDualMeasure.real (horizontalCrossingEvent 0 ((k0 : ℤ) * n) 0 n) :=
  fun k0 hk0 n hn =>
    crf_verticalCrossing_eq_horizontal_swap 0 n 0 ((k0 : ℤ) * n) (hmeas k0 hk0 n hn)






theorem crf_hrefl_fixed {k0 : ℕ}
    (hmeas : ∀ n : ℤ, 0 < n → MeasurableSet (horizontalCrossingEvent 0 ((k0 : ℤ) * n) 0 n)) :
    ∀ n : ℤ, 0 < n →
      rba_selfDualMeasure.real (verticalCrossingEvent 0 n 0 ((k0 : ℤ) * n))
        = rba_selfDualMeasure.real (horizontalCrossingEvent 0 ((k0 : ℤ) * n) 0 n) :=
  fun n hn =>
    crf_verticalCrossing_eq_horizontal_swap 0 n 0 ((k0 : ℤ) * n) (hmeas n hn)

end Universality

end StatMech
