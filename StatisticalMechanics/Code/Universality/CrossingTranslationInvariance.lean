/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





























































import Code.Universality.RSWAspectInduction
import Code.Universality.RSWBxpAssembly

open Set MeasureTheory SimpleGraph
open scoped ENNReal NNReal

namespace StatMech

namespace Universality

open StatMech.Lattice
open StatMech.RSW.Box
open StatMech.RSW.Strip






def sym2Congr {α β : Type*} (e : α ≃ β) : Sym2 α ≃ Sym2 β where
  toFun := Sym2.map e
  invFun := Sym2.map e.symm
  left_inv x := by rw [Sym2.map_map]; simp
  right_inv x := by rw [Sym2.map_map]; simp

@[simp] theorem sym2Congr_apply {α β : Type*} (e : α ≃ β) (x : Sym2 α) :
    sym2Congr e x = Sym2.map e x := rfl






noncomputable def cti_edgeEquiv (v : Site 2) : Sym2 (Site 2) ≃ Sym2 (Site 2) :=
  (sym2Congr (Equiv.addRight v)).symm



theorem cti_edgeEquiv_symm_apply (v : Site 2) (e : Sym2 (Site 2)) :
    (cti_edgeEquiv v).symm e = e.map (· + v) := by
  simp [cti_edgeEquiv, sym2Congr]






theorem cti_translateConfig_eq (v : Site 2) :
    translateConfig v = (Equiv.piCongrLeft (fun _ => Bool) (cti_edgeEquiv v)) := by
  funext ω e
  rw [translateConfig, Equiv.piCongrLeft_apply]
  simp [cti_edgeEquiv_symm_apply]



theorem cti_measurable_translateConfig (v : Site 2) :
    Measurable (translateConfig v) := by
  rw [cti_translateConfig_eq]
  exact (MeasurableEquiv.piCongrLeft (fun _ => Bool) (cti_edgeEquiv v)).measurable








theorem cti_map_translateConfig (v : Site 2) :
    Measure.map (translateConfig v) rba_selfDualMeasure = rba_selfDualMeasure := by
  rw [cti_translateConfig_eq, rba_selfDualMeasure]
  unfold bernoulliProductMeasure
  exact Measure.infinitePi_map_piCongrLeft
    (fun _ : Sym2 (Site 2) => bernoulliMeasure (2⁻¹ : ℝ≥0) half_le_one) (cti_edgeEquiv v)






theorem cti_selfDual_shift_invariant (v : Site 2) :
    MeasurePreserving (translateConfig v) rba_selfDualMeasure rba_selfDualMeasure :=
  ⟨cti_measurable_translateConfig v, cti_map_translateConfig v⟩








theorem cti_isOpenEdge_translate (t : Site 2) (ω : ConfigSpace (Sym2 (Site 2)))
    (x y : Site 2) :
    IsOpenEdge 2 (translateConfig t ω) x y ↔ IsOpenEdge 2 ω (x + t) (y + t) := by
  unfold IsOpenEdge
  have hadjiff : (hypercubicLattice 2).Adj x y ↔ (hypercubicLattice 2).Adj (x + t) (y + t) := by
    rw [hypercubicLattice_adj, hypercubicLattice_adj]
    constructor <;> intro h <;> rw [← h] <;>
      refine Finset.sum_congr rfl (fun i _ => ?_) <;> simp [Pi.add_apply]
  have hopeniff : (translateConfig t ω) s(x, y) = true ↔ ω s(x + t, y + t) = true := by
    rw [translateConfig_apply]
    rw [show (s(x, y) : Sym2 (Site 2)).map (· + t) = s(x + t, y + t) from Sym2.map_mk _ _ _]
  rw [hadjiff, hopeniff]



theorem cti_mem_rect_translate (a b c d : ℤ) (t : Site 2) (x : Site 2) :
    x ∈ rect a b c d ↔ (x + t) ∈ rect (a + t 0) (b + t 0) (c + t 1) (d + t 1) := by
  simp only [mem_rect, Pi.add_apply]
  constructor <;> intro h <;> exact ⟨by omega, by omega, by omega, by omega⟩


theorem cti_mem_leftSide_translate (a b c d : ℤ) (t : Site 2) (x : Site 2) :
    x ∈ leftSide a b c d ↔ (x + t) ∈ leftSide (a + t 0) (b + t 0) (c + t 1) (d + t 1) := by
  simp only [mem_leftSide, mem_rect, Pi.add_apply]
  constructor <;> rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩ <;>
    exact ⟨⟨by omega, by omega, by omega, by omega⟩, by omega⟩


theorem cti_mem_rightSide_translate (a b c d : ℤ) (t : Site 2) (x : Site 2) :
    x ∈ rightSide a b c d ↔ (x + t) ∈ rightSide (a + t 0) (b + t 0) (c + t 1) (d + t 1) := by
  simp only [mem_rightSide, mem_rect, Pi.add_apply]
  constructor <;> rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩ <;>
    exact ⟨⟨by omega, by omega, by omega, by omega⟩, by omega⟩


theorem cti_mem_bottomSide_translate (a b c d : ℤ) (t : Site 2) (x : Site 2) :
    x ∈ bottomSide a b c d ↔ (x + t) ∈ bottomSide (a + t 0) (b + t 0) (c + t 1) (d + t 1) := by
  simp only [mem_bottomSide, mem_rect, Pi.add_apply]
  constructor <;> rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩ <;>
    exact ⟨⟨by omega, by omega, by omega, by omega⟩, by omega⟩


theorem cti_mem_topSide_translate (a b c d : ℤ) (t : Site 2) (x : Site 2) :
    x ∈ topSide a b c d ↔ (x + t) ∈ topSide (a + t 0) (b + t 0) (c + t 1) (d + t 1) := by
  simp only [mem_topSide, mem_rect, Pi.add_apply]
  constructor <;> rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩ <;>
    exact ⟨⟨by omega, by omega, by omega, by omega⟩, by omega⟩








noncomputable def cti_inducedHom (a b c d : ℤ) (t : Site 2)
    (ω : ConfigSpace (Sym2 (Site 2))) :
    (openSubgraphInduce 2 (translateConfig t ω) (rect a b c d)) →g
      (openSubgraphInduce 2 ω (rect (a + t 0) (b + t 0) (c + t 1) (d + t 1))) where
  toFun := fun x => ⟨(x : Site 2) + t, (cti_mem_rect_translate a b c d t x).1 x.2⟩
  map_rel' := by
    intro x y hxy
    rw [openSubgraphInduce_adj] at hxy ⊢
    rw [openSubgraph_adj] at hxy ⊢
    obtain ⟨hadj, hopen⟩ := hxy
    exact ⟨((cti_isOpenEdge_translate t ω x y).1 ⟨hadj, hopen⟩).1,
           ((cti_isOpenEdge_translate t ω x y).1 ⟨hadj, hopen⟩).2⟩




noncomputable def cti_inducedHomInv (a b c d : ℤ) (t : Site 2)
    (ω : ConfigSpace (Sym2 (Site 2))) :
    (openSubgraphInduce 2 ω (rect (a + t 0) (b + t 0) (c + t 1) (d + t 1))) →g
      (openSubgraphInduce 2 (translateConfig t ω) (rect a b c d)) where
  toFun := fun x => ⟨(x : Site 2) - t, by
    rw [cti_mem_rect_translate a b c d t]; simp only [sub_add_cancel]; exact x.2⟩
  map_rel' := by
    intro x y hxy
    rw [openSubgraphInduce_adj] at hxy ⊢
    rw [openSubgraph_adj] at hxy ⊢
    obtain ⟨hadj, hopen⟩ := hxy
    have key := (cti_isOpenEdge_translate t ω ((x : Site 2) - t) ((y : Site 2) - t)).2
    simp only [sub_add_cancel] at key
    exact ⟨(key ⟨hadj, hopen⟩).1, (key ⟨hadj, hopen⟩).2⟩








theorem cti_horizontalCrossing_translate_fwd (a b c d : ℤ) (t : Site 2)
    (ω : ConfigSpace (Sym2 (Site 2)))
    (h : HorizontalCrossing (translateConfig t ω) a b c d) :
    HorizontalCrossing ω (a + t 0) (b + t 0) (c + t 1) (d + t 1) := by
  obtain ⟨x, y, hxy⟩ := h
  refine ⟨⟨(x : Site 2) + t, (cti_mem_leftSide_translate a b c d t x).1 x.2⟩,
          ⟨(y : Site 2) + t, (cti_mem_rightSide_translate a b c d t y).1 y.2⟩, ?_⟩
  exact (hxy : (openSubgraphInduce 2 (translateConfig t ω) (rect a b c d)).Reachable _ _).map
    (cti_inducedHom a b c d t ω)


theorem cti_horizontalCrossing_translate_bwd (a b c d : ℤ) (t : Site 2)
    (ω : ConfigSpace (Sym2 (Site 2)))
    (h : HorizontalCrossing ω (a + t 0) (b + t 0) (c + t 1) (d + t 1)) :
    HorizontalCrossing (translateConfig t ω) a b c d := by
  obtain ⟨x, y, hxy⟩ := h
  refine ⟨⟨(x : Site 2) - t, by
            rw [cti_mem_leftSide_translate a b c d t]; simp only [sub_add_cancel]; exact x.2⟩,
          ⟨(y : Site 2) - t, by
            rw [cti_mem_rightSide_translate a b c d t]; simp only [sub_add_cancel]; exact y.2⟩, ?_⟩
  exact (hxy :
      (openSubgraphInduce 2 ω (rect (a + t 0) (b + t 0) (c + t 1) (d + t 1))).Reachable _ _).map
    (cti_inducedHomInv a b c d t ω)


theorem cti_verticalCrossing_translate_fwd (a b c d : ℤ) (t : Site 2)
    (ω : ConfigSpace (Sym2 (Site 2)))
    (h : VerticalCrossing (translateConfig t ω) a b c d) :
    VerticalCrossing ω (a + t 0) (b + t 0) (c + t 1) (d + t 1) := by
  obtain ⟨x, y, hxy⟩ := h
  refine ⟨⟨(x : Site 2) + t, (cti_mem_bottomSide_translate a b c d t x).1 x.2⟩,
          ⟨(y : Site 2) + t, (cti_mem_topSide_translate a b c d t y).1 y.2⟩, ?_⟩
  exact (hxy : (openSubgraphInduce 2 (translateConfig t ω) (rect a b c d)).Reachable _ _).map
    (cti_inducedHom a b c d t ω)


theorem cti_verticalCrossing_translate_bwd (a b c d : ℤ) (t : Site 2)
    (ω : ConfigSpace (Sym2 (Site 2)))
    (h : VerticalCrossing ω (a + t 0) (b + t 0) (c + t 1) (d + t 1)) :
    VerticalCrossing (translateConfig t ω) a b c d := by
  obtain ⟨x, y, hxy⟩ := h
  refine ⟨⟨(x : Site 2) - t, by
            rw [cti_mem_bottomSide_translate a b c d t]; simp only [sub_add_cancel]; exact x.2⟩,
          ⟨(y : Site 2) - t, by
            rw [cti_mem_topSide_translate a b c d t]; simp only [sub_add_cancel]; exact y.2⟩, ?_⟩
  exact (hxy :
      (openSubgraphInduce 2 ω (rect (a + t 0) (b + t 0) (c + t 1) (d + t 1))).Reachable _ _).map
    (cti_inducedHomInv a b c d t ω)





theorem cti_horizontalCrossingEvent_translate (a b c d : ℤ) (t : Site 2) :
    horizontalCrossingEvent (a + t 0) (b + t 0) (c + t 1) (d + t 1)
      = translateConfig t ⁻¹' horizontalCrossingEvent a b c d := by
  ext ω
  simp only [Set.mem_preimage, mem_horizontalCrossingEvent]
  exact ⟨cti_horizontalCrossing_translate_bwd a b c d t ω,
         cti_horizontalCrossing_translate_fwd a b c d t ω⟩



theorem cti_verticalCrossingEvent_translate (a b c d : ℤ) (t : Site 2) :
    verticalCrossingEvent (a + t 0) (b + t 0) (c + t 1) (d + t 1)
      = translateConfig t ⁻¹' verticalCrossingEvent a b c d := by
  ext ω
  simp only [Set.mem_preimage, mem_verticalCrossingEvent]
  exact ⟨cti_verticalCrossing_translate_bwd a b c d t ω,
         cti_verticalCrossing_translate_fwd a b c d t ω⟩



















theorem cti_horizontalCrossing_translation_invariant (a b c d : ℤ) (t : Site 2)
    (hmeas : MeasurableSet (horizontalCrossingEvent a b c d)) :
    rba_selfDualMeasure.real (horizontalCrossingEvent (a + t 0) (b + t 0) (c + t 1) (d + t 1))
      = rba_selfDualMeasure.real (horizontalCrossingEvent a b c d) := by
  rw [cti_horizontalCrossingEvent_translate a b c d t,
    (cti_selfDual_shift_invariant t).measureReal_preimage hmeas.nullMeasurableSet]



theorem cti_verticalCrossing_translation_invariant (a b c d : ℤ) (t : Site 2)
    (hmeas : MeasurableSet (verticalCrossingEvent a b c d)) :
    rba_selfDualMeasure.real (verticalCrossingEvent (a + t 0) (b + t 0) (c + t 1) (d + t 1))
      = rba_selfDualMeasure.real (verticalCrossingEvent a b c d) := by
  rw [cti_verticalCrossingEvent_translate a b c d t,
    (cti_selfDual_shift_invariant t).measureReal_preimage hmeas.nullMeasurableSet]















theorem cti_h2box_discharge {n : ℤ} {γ : ℝ}
    (hmeas : MeasurableSet (horizontalCrossingEvent 0 (2 * n) 0 n))
    (h2box0 : γ ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 (2 * n) 0 n))
    (k : ℕ) (_hk : 1 ≤ k) :
    γ ≤ rba_selfDualMeasure.real
        (horizontalCrossingEvent (((k : ℤ) - 1) * n) (((k : ℤ) + 1) * n) 0 n) := by
  have h := cti_horizontalCrossing_translation_invariant 0 (2 * n) 0 n
    (![((k : ℤ) - 1) * n, 0]) hmeas
  have e0 : ((0 : ℤ) + (![((k : ℤ) - 1) * n, (0 : ℤ)] : Site 2) 0) = ((k : ℤ) - 1) * n := by
    simp
  have e1 : ((2 * n : ℤ) + (![((k : ℤ) - 1) * n, (0 : ℤ)] : Site 2) 0) = ((k : ℤ) + 1) * n := by
    simp; ring
  have e2 : ((0 : ℤ) + (![((k : ℤ) - 1) * n, (0 : ℤ)] : Site 2) 1) = 0 := by simp
  have e3 : ((n : ℤ) + (![((k : ℤ) - 1) * n, (0 : ℤ)] : Site 2) 1) = n := by simp
  rw [e0, e1, e2, e3] at h
  rw [h]; exact h2box0





theorem cti_hband_discharge {n : ℤ}
    (hmeas : MeasurableSet (verticalCrossingEvent 0 n 0 n))
    (hband0 : (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (verticalCrossingEvent 0 n 0 n))
    (k : ℕ) (_hk : 1 ≤ k) :
    (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real
        (verticalCrossingEvent (((k : ℤ) - 1) * n) ((k : ℤ) * n) 0 n) := by
  have h := cti_verticalCrossing_translation_invariant 0 n 0 n
    (![((k : ℤ) - 1) * n, 0]) hmeas
  have e0 : ((0 : ℤ) + (![((k : ℤ) - 1) * n, (0 : ℤ)] : Site 2) 0) = ((k : ℤ) - 1) * n := by
    simp
  have e1 : ((n : ℤ) + (![((k : ℤ) - 1) * n, (0 : ℤ)] : Site 2) 0) = (k : ℤ) * n := by
    simp; ring
  have e2 : ((0 : ℤ) + (![((k : ℤ) - 1) * n, (0 : ℤ)] : Site 2) 1) = 0 := by simp
  have e3 : ((n : ℤ) + (![((k : ℤ) - 1) * n, (0 : ℤ)] : Site 2) 1) = n := by simp
  rw [e0, e1, e2, e3] at h
  rw [h]; exact hband0


















theorem cti_rai_cross_pos_selfDual
    (hpa : PositivelyAssociated rba_selfDualMeasure) {n : ℤ} (hn : 0 < n)
    {β γ : ℝ} (hβ : 0 < β) (hγ : 0 < γ)
    (hmeas2box : MeasurableSet (horizontalCrossingEvent 0 (2 * n) 0 n))
    (hmeasband : MeasurableSet (verticalCrossingEvent 0 n 0 n))
    (hseed : β ≤ rai_cross rba_selfDualMeasure n 1)
    (h2box0 : γ ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 (2 * n) 0 n))
    (hband0 : (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (verticalCrossingEvent 0 n 0 n)) :
    ∀ k : ℕ, 1 ≤ k → ∃ c : ℝ, 0 < c ∧ c ≤ rai_cross rba_selfDualMeasure n k :=
  rai_cross_pos rba_selfDualMeasure hpa hn hβ hγ hseed
    (cti_h2box_discharge hmeas2box h2box0)
    (cti_hband_discharge hmeasband hband0)

end Universality

end StatMech
