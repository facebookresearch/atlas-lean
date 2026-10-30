/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanExteriorClosure
public import MathlibExt.Probability.Percolation.Universality.KestenHalf

/-!
# Gluing crossings, measurability of crossing events, and self-duality bounds

Building blocks for Russo–Seymour–Welsh arguments on `ℤ²` for a positively associated measure `μ`:

* crossing events of rectangles depend on finitely many edges and are measurable;
* gluing: `μ(H[a, m']) μ(V[m, m']) μ(H[m, b]) ≤ μ(H[a, b])` for horizontal crossings `H` and the
  vertical crossing `V` of the overlap (`StatMech.Lattice.jec_rsw_strip_glue`), iterated once;
* the square-root trick for two equiprobable increasing events;
* at `p = 1/2`, `dualConfig` crossings have the same law as primal crossings, and a uniform lower
  bound on crossings of `ρn × n` rectangles gives the box-crossing property.

`rba_self_dual_square_half` derives `ℙ_{1/2}(H) ≥ 1/2` for a square from a separation hypothesis
`hsep`; that hypothesis is false for `[0, 2]²` (see its docstring).

## Main results

* `StatMech.Universality.measurableSet_horizontalCrossingEvent`,
  `StatMech.Universality.measurableSet_verticalCrossingEvent`.
* `StatMech.Universality.rba_rsw_box_crossing_chain`: two gluing steps.
* `StatMech.Universality.rba_sqrt_square_seed`: square-root trick for the two crossings of a box.
* `StatMech.Universality.rba_glued_rectangle_lower_bound`.
* `StatMech.Universality.rba_bxp_of_uniform_seed`: uniform crossing bounds give the box-crossing
  property.

## References

* L. Russo, *A note on percolation*, Z. Wahrsch. Verw. Gebiete 43 (1978), 39–48.
* P. D. Seymour, D. J. A. Welsh, *Percolation probabilities on the square lattice*, Ann. Discrete
  Math. 3 (1978), 227–245.
* G. R. Grimmett, *Percolation*, 2nd ed., Springer, 1999, §11.7.
-/

@[expose] public section

open Set MeasureTheory SimpleGraph
open scoped ENNReal NNReal

namespace StatMech

namespace Universality

open StatMech.Lattice
open StatMech.RSW.Box
open StatMech.RSW.Strip

/-- An event determined by the states of the edges inside a rectangle is measurable. -/
theorem measurableSet_of_rect_determined {a b c d : ℤ} {A : Set (ConfigSpace (Sym2 (Site 2)))}
    (hA : ∀ ω ω' : ConfigSpace (Sym2 (Site 2)),
      (∀ u ∈ rect a b c d, ∀ v ∈ rect a b c d, ω s(u, v) = ω' s(u, v)) → ω ∈ A → ω' ∈ A) :
    MeasurableSet A := by
  classical
  let F : Set (Sym2 (Site 2)) :=
    (fun q : Site 2 × Site 2 => s(q.1, q.2)) '' (rect a b c d ×ˢ rect a b c d)
  have hF : F.Finite := ((rect_finite a b c d).prod (rect_finite a b c d)).image _
  have := hF.to_subtype
  let r : ConfigSpace (Sym2 (Site 2)) → (F → Bool) := fun ω e => ω e
  have hr : Measurable r := by fun_prop
  have hAeq : A = r ⁻¹' (r '' A) := by
    ext ω
    refine ⟨fun h => ⟨ω, h, rfl⟩, ?_⟩
    rintro ⟨ω', h', he⟩
    refine hA ω' ω (fun u hu v hv => ?_) h'
    exact congrFun he ⟨s(u, v), ⟨(u, v), ⟨hu, hv⟩, rfl⟩⟩
  rw [hAeq]
  exact hr (Set.to_countable _).measurableSet

/-- The open subgraph induced on a rectangle depends only on the edges inside it. -/
theorem openSubgraphInduce_rect_congr {a b c d : ℤ} {ω ω' : ConfigSpace (Sym2 (Site 2))}
    (h : ∀ u ∈ rect a b c d, ∀ v ∈ rect a b c d, ω s(u, v) = ω' s(u, v)) :
    openSubgraphInduce 2 ω (rect a b c d) = openSubgraphInduce 2 ω' (rect a b c d) := by
  ext x y
  rw [openSubgraphInduce_adj, openSubgraphInduce_adj, openSubgraph_adj, openSubgraph_adj,
    h x x.2 y y.2]

/-- The left–right crossing event of a rectangle is measurable. -/
theorem measurableSet_horizontalCrossingEvent (a b c d : ℤ) :
    MeasurableSet (horizontalCrossingEvent a b c d) := by
  refine measurableSet_of_rect_determined (a := a) (b := b) (c := c) (d := d) ?_
  intro ω ω' h hω
  simp only [mem_horizontalCrossingEvent, HorizontalCrossing, ConnectedWithin,
    openSubgraphInduce_rect_congr h] at hω ⊢
  exact hω

/-- The bottom–top crossing event of a rectangle is measurable. -/
theorem measurableSet_verticalCrossingEvent (a b c d : ℤ) :
    MeasurableSet (verticalCrossingEvent a b c d) := by
  refine measurableSet_of_rect_determined (a := a) (b := b) (c := c) (d := d) ?_
  intro ω ω' h hω
  simp only [mem_verticalCrossingEvent, VerticalCrossing, ConnectedWithin,
    openSubgraphInduce_rect_congr h] at hω ⊢
  exact hω

/-- Two gluing steps: crossings of `[a, m'] , [m, b]` glued through `[m, m']`, then the result and
`[p, e]` glued through `[p, b]`, bound the crossing of `[a, e] × [c, d]` from below. -/
theorem rba_rsw_box_crossing_chain
    (μ : MeasureTheory.Measure (ConfigSpace (Sym2 (Site 2))))
    [MeasureTheory.IsProbabilityMeasure μ]
    (hpa : PositivelyAssociated μ) {a m m' b p e c d : ℤ}
    (ham : a ≤ m) (hmm' : m ≤ m') (hm'b : m' ≤ b)
    (hamL : a < m') (hmbR : m < b)
    (hap : a ≤ p) (hpb : p ≤ b) (hbe : b ≤ e) (hab : a < b) (hpe : p < e) (hcd : c ≤ d) :
    μ.real (horizontalCrossingEvent a m' c d)
        * μ.real (verticalCrossingEvent m m' c d)
        * μ.real (horizontalCrossingEvent m b c d)
        * μ.real (verticalCrossingEvent p b c d)
        * μ.real (horizontalCrossingEvent p e c d)
      ≤ μ.real (horizontalCrossingEvent a e c d) := by
  have hinner := StatMech.Lattice.jec_rsw_strip_glue μ hpa ham hmm' hm'b hamL hmbR hcd
  have houter := StatMech.Lattice.jec_rsw_strip_glue μ hpa hap hpb hbe hab hpe hcd
  have hVnn : (0 : ℝ) ≤ μ.real (verticalCrossingEvent p b c d) := measureReal_nonneg
  have hHnn : (0 : ℝ) ≤ μ.real (horizontalCrossingEvent p e c d) := measureReal_nonneg
  calc μ.real (horizontalCrossingEvent a m' c d)
        * μ.real (verticalCrossingEvent m m' c d)
        * μ.real (horizontalCrossingEvent m b c d)
        * μ.real (verticalCrossingEvent p b c d)
        * μ.real (horizontalCrossingEvent p e c d)
      = (μ.real (horizontalCrossingEvent a m' c d)
          * μ.real (verticalCrossingEvent m m' c d)
          * μ.real (horizontalCrossingEvent m b c d))
        * μ.real (verticalCrossingEvent p b c d)
        * μ.real (horizontalCrossingEvent p e c d) := by ring
    _ ≤ μ.real (horizontalCrossingEvent a b c d)
        * μ.real (verticalCrossingEvent p b c d)
        * μ.real (horizontalCrossingEvent p e c d) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hinner hVnn) hHnn
    _ ≤ μ.real (horizontalCrossingEvent a e c d) := houter

/-- Square-root trick: if the two crossings of a box are equiprobable under a positively associated
`μ` and `μ(H ∪ V) ≥ s`, then `μ(H) ≥ 1 - √(1 - s)`. -/
theorem rba_sqrt_square_seed
    (μ : MeasureTheory.Measure (ConfigSpace (Sym2 (Site 2))))
    [MeasureTheory.IsProbabilityMeasure μ]
    (hpa : PositivelyAssociated μ) {a b c d : ℤ} {s : ℝ}
    (hmeasH : MeasurableSet (horizontalCrossingEvent a b c d))
    (hmeasV : MeasurableSet (verticalCrossingEvent a b c d))
    (hsym : μ.real (verticalCrossingEvent a b c d)
              = μ.real (horizontalCrossingEvent a b c d))
    (hunion : s ≤ μ.real (horizontalCrossingEvent a b c d ∪ verticalCrossingEvent a b c d)) :
    1 - Real.sqrt (1 - s) ≤ μ.real (horizontalCrossingEvent a b c d) := by
  have h := rsw_sqrt_trick_eq μ hpa
    (horizontalCrossingEvent_isIncreasing a b c d)
    (verticalCrossingEvent_isIncreasing a b c d)
    hmeasH hmeasV hsym.symm
  have hmono :
      Real.sqrt (1 - μ.real (horizontalCrossingEvent a b c d ∪ verticalCrossingEvent a b c d))
        ≤ Real.sqrt (1 - s) := Real.sqrt_le_sqrt (by linarith)
  linarith

/-- Under `ℙ_{1/2}` the `dualConfig` bottom–top crossing has the probability of the primal one. -/
theorem rba_dualVerticalCrossing_eq (a b c d : ℤ)
    (hmeasV : MeasurableSet (verticalCrossingEvent a b c d)) :
    halfMeasure.real (dualVerticalCrossingEvent a b c d)
      = halfMeasure.real (verticalCrossingEvent a b c d) := by
  have hpre : dualVerticalCrossingEvent a b c d
      = dualConfig ⁻¹' verticalCrossingEvent a b c d := rfl
  unfold halfMeasure
  rw [hpre, Measure.real, ← Measure.map_apply measurable_dualConfig hmeasV,
    bernoulliProductMeasure_selfDual_half]
  rfl

/-- Under `ℙ_{1/2}` the `dualConfig` left–right crossing has the probability of the primal one. -/
theorem rba_dualHorizontalCrossing_eq (a b c d : ℤ)
    (hmeasH : MeasurableSet (horizontalCrossingEvent a b c d)) :
    halfMeasure.real (dualHorizontalCrossingEvent a b c d)
      = halfMeasure.real (horizontalCrossingEvent a b c d) := by
  have hpre : dualHorizontalCrossingEvent a b c d
      = dualConfig ⁻¹' horizontalCrossingEvent a b c d := rfl
  unfold halfMeasure
  rw [hpre, Measure.real, ← Measure.map_apply measurable_dualConfig hmeasH,
    bernoulliProductMeasure_selfDual_half]
  rfl

/-- `ℙ_{1/2}(H[0, n]²) ≥ 1/2`, given the separation hypothesis `hsep` and the symmetry
`ℙ_{1/2}(V) = ℙ_{1/2}(H)` of the square (special case of `rst_selfDual_box_crossing_half`).

The hypothesis `hsep` ("no open left–right crossing implies a `dualConfig` bottom–top crossing")
is not planar duality: `dualConfig` is the rotated complement on the primal lattice, so
`dualVerticalCrossingEvent a b c d` is a closed left–right crossing of the rotated rectangle
`[c, d] × [-b, -a]`. `bcc_dichotomy_false` shows `hsep` fails for `[0, 2]²`; it is not known to
hold for any nondegenerate rectangle. -/
theorem rba_self_dual_square_half (n : ℤ)
    (hmeasH : MeasurableSet (horizontalCrossingEvent 0 n 0 n))
    (hmeasV : MeasurableSet (verticalCrossingEvent 0 n 0 n))
    (hsep : (horizontalCrossingEvent 0 n 0 n)ᶜ ⊆ dualVerticalCrossingEvent 0 n 0 n)
    (hsqsym : halfMeasure.real (verticalCrossingEvent 0 n 0 n)
                = halfMeasure.real (horizontalCrossingEvent 0 n 0 n)) :
    (1 : ℝ) / 2 ≤ halfMeasure.real (horizontalCrossingEvent 0 n 0 n) := by
  have hselfDual : halfMeasure.real (dualVerticalCrossingEvent 0 n 0 n)
      = halfMeasure.real (horizontalCrossingEvent 0 n 0 n) := by
    rw [rba_dualVerticalCrossing_eq 0 n 0 n hmeasV, hsqsym]
  have hcompl : halfMeasure.real (horizontalCrossingEvent 0 n 0 n)ᶜ
      = 1 - halfMeasure.real (horizontalCrossingEvent 0 n 0 n) := by
    rw [measureReal_compl hmeasH, probReal_univ]
  have hmono : halfMeasure.real (horizontalCrossingEvent 0 n 0 n)ᶜ
      ≤ halfMeasure.real (dualVerticalCrossingEvent 0 n 0 n) :=
    measureReal_mono hsep
  rw [hselfDual, hcompl] at hmono
  linarith

/-- If the two overlapping horizontal crossings have probability at least `1/2` and the vertical
crossing of the overlap at least `v₀`, the glued horizontal crossing has probability at least
`v₀ / 4`. -/
theorem rba_glued_rectangle_lower_bound
    (μ : MeasureTheory.Measure (ConfigSpace (Sym2 (Site 2))))
    [MeasureTheory.IsProbabilityMeasure μ]
    (hpa : PositivelyAssociated μ) {a m m' b c d : ℤ} {v0 : ℝ}
    (ham : a ≤ m) (hmm' : m ≤ m') (hm'b : m' ≤ b)
    (hamL : a < m') (hmbR : m < b) (hcd : c ≤ d)
    (hL : (1 : ℝ) / 2 ≤ μ.real (horizontalCrossingEvent a m' c d))
    (hR : (1 : ℝ) / 2 ≤ μ.real (horizontalCrossingEvent m b c d))
    (hVlb : v0 ≤ μ.real (verticalCrossingEvent m m' c d)) (hv0 : 0 ≤ v0) :
    v0 / 4 ≤ μ.real (horizontalCrossingEvent a b c d) := by
  have hglue := StatMech.Lattice.jec_rsw_strip_glue μ hpa ham hmm' hm'b hamL hmbR hcd
  set HL := μ.real (horizontalCrossingEvent a m' c d) with hHL
  set HR := μ.real (horizontalCrossingEvent m b c d) with hHR
  set V := μ.real (verticalCrossingEvent m m' c d) with hVdef
  have hLnn : (0 : ℝ) ≤ HL := measureReal_nonneg
  have h1 : (1 / 2 : ℝ) * v0 ≤ HL * V := mul_le_mul hL hVlb hv0 hLnn
  have h2 : ((1 / 2 : ℝ) * v0) * (1 / 2) ≤ HL * V * HR :=
    mul_le_mul h1 hR (by norm_num) (by positivity)
  have hprod : v0 / 4 ≤ HL * V * HR := by nlinarith [h2]
  linarith [hglue, hprod]

/-- A constant `c > 0` bounding all translated long-way crossings of `⌊ρn⌋ × n` and `n × ⌊ρn⌋`
rectangles for `n ≥ n₀` gives the box-crossing property with aspect ratio `ρ`. -/
theorem rba_bxp_of_uniform_seed
    (μ : MeasureTheory.Measure (ConfigSpace (Sym2 (Site 2))))
    (ρ : ℝ) (hρ : 1 < ρ) (n0 : ℕ) (c : ℝ) (hc : 0 < c)
    (hH : ∀ (n : ℕ) (τ : Site 2), n0 ≤ n →
      c ≤ μ.real (translatedHorizontalCrossingEvent τ ⌊ρ * (n : ℝ)⌋ (n : ℤ)))
    (hV : ∀ (n : ℕ) (τ : Site 2), n0 ≤ n →
      c ≤ μ.real (translatedVerticalCrossingEvent τ (n : ℤ) ⌊ρ * (n : ℝ)⌋)) :
    BoxCrossingProperty μ ρ := by
  refine ⟨hρ, n0, ?_⟩
  have hlb : ∀ x ∈ boxCrossingProbabilities μ ρ n0, c ≤ x := by
    rintro x ⟨n, τ, hn, rfl | rfl⟩
    · exact hH n τ hn
    · exact hV n τ hn
  have hne : (boxCrossingProbabilities μ ρ n0).Nonempty :=
    ⟨μ.real (translatedHorizontalCrossingEvent 0 ⌊ρ * (n0 : ℝ)⌋ (n0 : ℤ)),
      n0, 0, le_refl _, Or.inl rfl⟩
  have hge : c ≤ sInf (boxCrossingProbabilities μ ρ n0) := le_csInf hne hlb
  rw [boxCrossingInf]; linarith

end Universality

end StatMech
