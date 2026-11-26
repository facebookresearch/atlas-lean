/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Percolation.Universality.RSWAspectInduction
public import MathlibExt.Probability.Percolation.Universality.RSWBxpAssembly

/-!
# Translation invariance of crossing probabilities at `p = 1/2`

`translateConfig t` preserves `ℙ_{1/2}`, and the crossing events of a rectangle shifted by `t` are
the preimages of the crossing events of the original rectangle under `translateConfig t`. Hence
crossing probabilities under `ℙ_{1/2}` are translation invariant. As an application, the
translated hypotheses of the aspect-ratio induction (`rai_cross_lb`) follow from the hypotheses for
the rectangles at the origin.

## Main results

* `StatMech.Universality.cti_selfDual_shift_invariant`: `translateConfig t` preserves `ℙ_{1/2}`.
* `StatMech.Universality.cti_horizontalCrossingEvent_translate`,
  `StatMech.Universality.cti_verticalCrossingEvent_translate`.
* `StatMech.Universality.cti_horizontalCrossing_translation_invariant`,
  `StatMech.Universality.cti_verticalCrossing_translation_invariant`.
* `StatMech.Universality.cti_rai_cross_pos_selfDual`.
-/

@[expose] public section

open Set MeasureTheory SimpleGraph
open scoped ENNReal NNReal

namespace StatMech

namespace Universality

open StatMech.Lattice
open StatMech.RSW.Box
open StatMech.RSW.Strip

/-- The bijection of edges `e ↦ e - v`, so that reindexing by it is `translateConfig v`. -/
noncomputable def cti_edgeEquiv (v : Site 2) : Sym2 (Site 2) ≃ Sym2 (Site 2) :=
  (sym2Congr (Equiv.addRight v)).symm

theorem cti_edgeEquiv_symm_apply (v : Site 2) (e : Sym2 (Site 2)) :
    (cti_edgeEquiv v).symm e = e.map (· + v) := by
  simp [cti_edgeEquiv, sym2Congr]

/-- `translateConfig v` is reindexing along `cti_edgeEquiv v`. -/
theorem cti_translateConfig_eq (v : Site 2) :
    translateConfig v = (Equiv.piCongrLeft (fun _ => Bool) (cti_edgeEquiv v)) := by
  funext ω e
  rw [translateConfig, Equiv.piCongrLeft_apply]
  simp [cti_edgeEquiv_symm_apply]

/-- `translateConfig v` is measurable. -/
theorem cti_measurable_translateConfig (v : Site 2) :
    Measurable (translateConfig v) := by
  rw [cti_translateConfig_eq]
  exact (MeasurableEquiv.piCongrLeft (fun _ => Bool) (cti_edgeEquiv v)).measurable

/-- `translateConfig v` preserves `ℙ_{1/2}`.

See also `StatMech.Percolation.bernoulli_translationInvariant`, the same fact for the shift action
and every `p`. -/
theorem cti_map_translateConfig (v : Site 2) :
    Measure.map (translateConfig v) halfMeasure = halfMeasure := by
  rw [cti_translateConfig_eq, halfMeasure]
  unfold bernoulliProductMeasure
  exact Measure.infinitePi_map_piCongrLeft
    (fun _ : Sym2 (Site 2) => bernoulliMeasure (2⁻¹ : ℝ≥0) half_le_one) (cti_edgeEquiv v)

/-- `translateConfig v` is measure preserving for `ℙ_{1/2}`. -/
theorem cti_selfDual_shift_invariant (v : Site 2) :
    MeasurePreserving (translateConfig v) halfMeasure halfMeasure :=
  ⟨cti_measurable_translateConfig v, cti_map_translateConfig v⟩

/-- An edge is open in `translateConfig t ω` iff its translate by `t` is open in `ω`. -/
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

/-- Translation by `t` as a graph homomorphism between the open subgraphs induced on a rectangle
and on its translate. -/
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

/-- Translation by `-t` as a graph homomorphism, inverse to `cti_inducedHom`. -/
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

/-- The left–right crossing event of the translated rectangle is the preimage of the original one
under `translateConfig t`. -/
theorem cti_horizontalCrossingEvent_translate (a b c d : ℤ) (t : Site 2) :
    horizontalCrossingEvent (a + t 0) (b + t 0) (c + t 1) (d + t 1)
      = translateConfig t ⁻¹' horizontalCrossingEvent a b c d := by
  ext ω
  simp only [Set.mem_preimage, mem_horizontalCrossingEvent]
  exact ⟨cti_horizontalCrossing_translate_bwd a b c d t ω,
         cti_horizontalCrossing_translate_fwd a b c d t ω⟩

/-- The bottom–top crossing event of the translated rectangle is the preimage of the original one
under `translateConfig t`. -/
theorem cti_verticalCrossingEvent_translate (a b c d : ℤ) (t : Site 2) :
    verticalCrossingEvent (a + t 0) (b + t 0) (c + t 1) (d + t 1)
      = translateConfig t ⁻¹' verticalCrossingEvent a b c d := by
  ext ω
  simp only [Set.mem_preimage, mem_verticalCrossingEvent]
  exact ⟨cti_verticalCrossing_translate_bwd a b c d t ω,
         cti_verticalCrossing_translate_fwd a b c d t ω⟩

/-- Left–right crossing probabilities under `ℙ_{1/2}` are translation invariant. -/
theorem cti_horizontalCrossing_translation_invariant (a b c d : ℤ) (t : Site 2)
    (hmeas : MeasurableSet (horizontalCrossingEvent a b c d)) :
    halfMeasure.real (horizontalCrossingEvent (a + t 0) (b + t 0) (c + t 1) (d + t 1))
      = halfMeasure.real (horizontalCrossingEvent a b c d) := by
  rw [cti_horizontalCrossingEvent_translate a b c d t,
    (cti_selfDual_shift_invariant t).measureReal_preimage hmeas.nullMeasurableSet]

/-- Bottom–top crossing probabilities under `ℙ_{1/2}` are translation invariant. -/
theorem cti_verticalCrossing_translation_invariant (a b c d : ℤ) (t : Site 2)
    (hmeas : MeasurableSet (verticalCrossingEvent a b c d)) :
    halfMeasure.real (verticalCrossingEvent (a + t 0) (b + t 0) (c + t 1) (d + t 1))
      = halfMeasure.real (verticalCrossingEvent a b c d) := by
  rw [cti_verticalCrossingEvent_translate a b c d t,
    (cti_selfDual_shift_invariant t).measureReal_preimage hmeas.nullMeasurableSet]

/-- The `2n × n` hypothesis of `rai_cross_lb` at every position follows from the one at the origin.
-/
theorem cti_h2box_discharge {n : ℤ} {γ : ℝ}
    (hmeas : MeasurableSet (horizontalCrossingEvent 0 (2 * n) 0 n))
    (h2box0 : γ ≤ halfMeasure.real (horizontalCrossingEvent 0 (2 * n) 0 n))
    (k : ℕ) (_hk : 1 ≤ k) :
    γ ≤ halfMeasure.real
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

/-- The band hypothesis of `rai_cross_lb` at every position follows from the one at the origin. -/
theorem cti_hband_discharge {n : ℤ}
    (hmeas : MeasurableSet (verticalCrossingEvent 0 n 0 n))
    (hband0 : (1 : ℝ) / 2 ≤ halfMeasure.real (verticalCrossingEvent 0 n 0 n))
    (k : ℕ) (_hk : 1 ≤ k) :
    (1 : ℝ) / 2 ≤ halfMeasure.real
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

/-- `rai_cross_pos` for `ℙ_{1/2}` with the translated hypotheses discharged: positive association,
a square bound `β`, a bound `γ` on the crossing of `[0, 2n] × [0, n]` (the RSW input) and the
band bound `1/2` at the origin give positive crossing probabilities of `[0, kn] × [0, n]`. -/
theorem cti_rai_cross_pos_selfDual
    (hpa : PositivelyAssociated halfMeasure) {n : ℤ} (hn : 0 < n)
    {β γ : ℝ} (hβ : 0 < β) (hγ : 0 < γ)
    (hmeas2box : MeasurableSet (horizontalCrossingEvent 0 (2 * n) 0 n))
    (hmeasband : MeasurableSet (verticalCrossingEvent 0 n 0 n))
    (hseed : β ≤ rai_cross halfMeasure n 1)
    (h2box0 : γ ≤ halfMeasure.real (horizontalCrossingEvent 0 (2 * n) 0 n))
    (hband0 : (1 : ℝ) / 2 ≤ halfMeasure.real (verticalCrossingEvent 0 n 0 n)) :
    ∀ k : ℕ, 1 ≤ k → ∃ c : ℝ, 0 < c ∧ c ≤ rai_cross halfMeasure n k :=
  rai_cross_pos halfMeasure hpa hn hβ hγ hseed
    (cti_h2box_discharge hmeas2box h2box0)
    (cti_hband_discharge hmeasband hband0)

end Universality

end StatMech
