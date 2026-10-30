/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Percolation.Universality.BXPFromRSW
public import MathlibExt.Probability.Percolation.Universality.BXPTransfer

/-!
# Kesten's theorem from an RSW seed at `p = 1/2`

This file replaces the box-crossing hypothesis of `kesten_pc_eq_half_of_bxp` by more elementary
crossing inputs at `p = 1/2`:

* `KaSelfDualBoxSeed ℙ_{1/2}`: a uniform positive lower bound on `ℙ_{1/2}` of the long-way crossings
  of the rectangles `[0, 2n] × [0, n]` and `[0, n] × [0, 2n]`. This is the Russo–Seymour–Welsh
  theorem at `p = 1/2`; it is assumed.
* `KaCrossingTranslationInvariant ℙ_{1/2}`: crossing probabilities do not depend on translations.
  This one is proved (`kaCrossingTranslationInvariant_halfMeasure`).

From these, `ka_bxp_half_of_rsw` gives the box-crossing property of `ℙ_{1/2}` with aspect ratio `2`,
and `ka_kesten_pc_eq_half` / `ka_kesten_pc_eq_half_of_seed` give `p_c = 1/2` under the remaining
hypotheses of `kesten_pc_eq_half_of_bxp` (Harris's theorem as `hCorLowerBound`, subcritical decay
of a self-dual crossing family as `hSharpThreshold`, and the self-duality identity `hdich`).

## Main definitions

* `StatMech.Universality.KaSelfDualBoxSeed`: the RSW seed bound at aspect ratio `2`.
* `StatMech.Universality.KaCrossingTranslationInvariant`: translation invariance of crossing
  probabilities.

## Main results

* `StatMech.Universality.ka_rsw_strip_glue_extend`: gluing two horizontal crossings with a vertical
  one (positive association).
* `StatMech.Universality.ka_bxp_half_of_rsw`: the RSW seed implies the box-crossing property.
* `StatMech.Universality.ka_kesten_pc_eq_half_of_seed`: conditional Kesten theorem.

## References

* H. Kesten, *The critical probability of bond percolation on the square lattice equals 1/2*,
  Comm. Math. Phys. 74 (1980), 41–59.
* L. Russo, *A note on percolation*, Z. Wahrsch. Verw. Gebiete 43 (1978), 39–48.
* P. D. Seymour, D. J. A. Welsh, *Percolation probabilities on the square lattice*, Ann. Discrete
  Math. 3 (1978), 227–245.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace StatMech

namespace Universality

open StatMech.Lattice StatMech.TwoDim

/-- Gluing: for a positively associated `μ`, lower bounds `cL`, `cV`, `cR` on the crossings of
`[a, m'] × [c, d]` (horizontal), `[m, m'] × [c, d]` (vertical) and `[m, b] × [c, d]` (horizontal)
give `cL cV cR ≤ μ(horizontal crossing of [a, b] × [c, d])`. -/
theorem ka_rsw_strip_glue_extend
    (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ]
    (hpa : PositivelyAssociated μ) {a m m' b c d : ℤ}
    (ham : a ≤ m) (hmm' : m ≤ m') (hm'b : m' ≤ b)
    (hamL : a < m') (hmbR : m < b) (hcd : c ≤ d)
    {cL cV cR : ℝ}
    (hL : cL ≤ μ.real (StatMech.RSW.Box.horizontalCrossingEvent a m' c d))
    (hV : cV ≤ μ.real (StatMech.RSW.Box.verticalCrossingEvent m m' c d))
    (hR : cR ≤ μ.real (StatMech.RSW.Box.horizontalCrossingEvent m b c d))
    (hcV0 : 0 ≤ cV) (hcR0 : 0 ≤ cR) :
    cL * cV * cR ≤ μ.real (StatMech.RSW.Box.horizontalCrossingEvent a b c d) := by
  have hglue := StatMech.Lattice.jec_rsw_strip_glue μ hpa ham hmm' hm'b hamL hmbR hcd
  have h1 : (0 : ℝ) ≤ μ.real (StatMech.RSW.Box.horizontalCrossingEvent a m' c d) :=
    measureReal_nonneg
  calc cL * cV * cR
      ≤ μ.real (StatMech.RSW.Box.horizontalCrossingEvent a m' c d)
          * μ.real (StatMech.RSW.Box.verticalCrossingEvent m m' c d)
          * μ.real (StatMech.RSW.Box.horizontalCrossingEvent m b c d) := by
        apply mul_le_mul
        · exact mul_le_mul hL hV hcV0 h1
        · exact hR
        · exact hcR0
        · positivity
    _ ≤ μ.real (StatMech.RSW.Box.horizontalCrossingEvent a b c d) := hglue

/-- Special case of `ka_rsw_strip_glue_extend`: two crossings of `2n × n` boxes and a vertical
crossing of the middle `n × n` square give a crossing of `[0, 3n] × [0, n]`. -/
theorem ka_wide_box_extend
    (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ]
    (hpa : PositivelyAssociated μ) {n : ℤ} (hn : 0 < n) {cW cS : ℝ}
    (hcW0 : 0 ≤ cW) (hcS0 : 0 ≤ cS)
    (hW1 : cW ≤ μ.real (StatMech.RSW.Box.horizontalCrossingEvent 0 (2 * n) 0 n))
    (hW2 : cW ≤ μ.real (StatMech.RSW.Box.horizontalCrossingEvent n (3 * n) 0 n))
    (hS : cS ≤ μ.real (StatMech.RSW.Box.verticalCrossingEvent n (2 * n) 0 n)) :
    cW * cS * cW ≤ μ.real (StatMech.RSW.Box.horizontalCrossingEvent 0 (3 * n) 0 n) :=
  ka_rsw_strip_glue_extend μ hpa (a := 0) (m := n) (m' := 2 * n) (b := 3 * n) (c := 0) (d := n)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    hW1 hS hW2 hcS0 hcW0

/-- `⌊2n⌋ = 2n` for natural `n`. -/
theorem ka_floor_two_mul (n : ℕ) : ⌊(2 : ℝ) * (n : ℝ)⌋ = (2 * n : ℤ) := by
  rw [show (2 : ℝ) * (n : ℝ) = ((2 * n : ℤ) : ℝ) by push_cast; ring, Int.floor_intCast]

/-- A uniform positive lower bound on the long-way crossings of all translates of the `2n × n`
and `n × 2n` rectangles is the box-crossing property with aspect ratio `2`. -/
theorem ka_bxp_of_box_seed (μ : Measure (ConfigSpace (Sym2 (Site 2))))
    [IsProbabilityMeasure μ] {c : ℝ} (hc : 0 < c)
    (hH : ∀ (n : ℕ) (τ : Site 2),
        c ≤ μ.real (translatedHorizontalCrossingEvent τ (2 * (n : ℤ)) (n : ℤ)))
    (hV : ∀ (n : ℕ) (τ : Site 2),
        c ≤ μ.real (translatedVerticalCrossingEvent τ (n : ℤ) (2 * (n : ℤ)))) :
    BoxCrossingProperty μ 2 := by
  refine ⟨by norm_num, 0, ?_⟩
  unfold boxCrossingInf
  refine lt_of_lt_of_le hc (le_csInf (boxCrossingProbabilities_nonempty μ 2 0) ?_)
  rintro x ⟨n, τ, _hn, rfl | rfl⟩
  · rw [ka_floor_two_mul n]; exact hH n τ
  · rw [ka_floor_two_mul n]; exact hV n τ

/-- RSW seed at aspect ratio `2`: a constant `c > 0` bounding from below the probability of the
left–right crossing of `[0, 2n] × [0, n]` and of the bottom–top crossing of `[0, n] × [0, 2n]`,
for all `n`. For `μ = ℙ_{1/2}` this is the Russo–Seymour–Welsh theorem. -/
structure KaSelfDualBoxSeed (μ : Measure (ConfigSpace (Sym2 (Site 2)))) where
  c : ℝ
  c_pos : 0 < c
  wide : ∀ n : ℕ, c ≤ μ.real (StatMech.RSW.Box.horizontalCrossingEvent 0 (2 * (n : ℤ)) 0 (n : ℤ))
  tall : ∀ n : ℕ, c ≤ μ.real (StatMech.RSW.Box.verticalCrossingEvent 0 (n : ℤ) 0 (2 * (n : ℤ)))

/-- Crossing probabilities of translated rectangles equal those of the untranslated rectangles. -/
structure KaCrossingTranslationInvariant
    (μ : Measure (ConfigSpace (Sym2 (Site 2)))) : Prop where
  horiz : ∀ (τ : Site 2) (a b : ℤ),
    μ.real (translatedHorizontalCrossingEvent τ a b)
      = μ.real (TwoDim.horizontalCrossingEvent a b)
  vert : ∀ (τ : Site 2) (a b : ℤ),
    μ.real (translatedVerticalCrossingEvent τ a b)
      = μ.real (TwoDim.verticalCrossingEvent a b)

/-- `ℙ_{1/2}` has translation-invariant crossing probabilities. -/
theorem kaCrossingTranslationInvariant_halfMeasure :
    KaCrossingTranslationInvariant halfMeasure where
  horiz τ a b := by
    rw [bxr_translatedHorizontalCrossing_invariant τ a b
      (measurableSet_horizontalCrossingEvent 0 a 0 b), bxr_twoDim_horizontalCrossingEvent_eq]
  vert τ a b := by
    rw [bxr_translatedVerticalCrossing_invariant τ a b
      (measurableSet_verticalCrossingEvent 0 a 0 b), bxr_twoDim_verticalCrossingEvent_eq]

/-- The RSW seed and translation invariance give the box-crossing property of `ℙ_{1/2}` with
aspect ratio `2`. -/
theorem ka_bxp_half_of_rsw
    (hseed : KaSelfDualBoxSeed halfMeasure)
    (htinv : KaCrossingTranslationInvariant halfMeasure) :
    BoxCrossingProperty halfMeasure 2 := by
  refine ka_bxp_of_box_seed halfMeasure hseed.c_pos ?_ ?_
  · intro n τ
    rw [htinv.horiz τ (2 * (n : ℤ)) (n : ℤ),
      bxr_twoDim_horizontalCrossingEvent_eq (2 * (n : ℤ)) (n : ℤ)]
    exact hseed.wide n
  · intro n τ
    rw [htinv.vert τ (n : ℤ) (2 * (n : ℤ)),
      bxr_twoDim_verticalCrossingEvent_eq (n : ℤ) (2 * (n : ℤ))]
    exact hseed.tall n

/-- Conditional **Kesten theorem** `p_c(ℤ²) = 1/2` (Kesten 1980), with the box-crossing hypothesis
of `kesten_pc_eq_half_of_bxp` replaced by the RSW seed `hseed` (assumed) and translation
invariance `htinv` (provable, see `ka_kesten_pc_eq_half_of_seed`). The other inputs are as in
`kesten_pc_eq_half_of_bxp`: Harris's theorem as `hCorLowerBound`, subcritical decay of the
self-dual family `boxFam` as `hSharpThreshold`, and the self-duality identity `hdich`. -/
theorem ka_kesten_pc_eq_half
    {R : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2))}
    {boxFam : ℕ → Set (ConfigSpace (Sym2 (Site 2)))}
    (hseed : KaSelfDualBoxSeed halfMeasure)
    (htinv : KaCrossingTranslationInvariant halfMeasure)
    (hCorLowerBound : BoxCrossingProperty halfMeasure 2 →
        percolationProbability 2 (2⁻¹ : ℝ≥0) half_le_one = 0)
    (hHm : ∀ n, MeasurableSet (boxFam n))
    (hRmeas : Measurable R) (hRpres : Measure.map R halfMeasure = halfMeasure)
    (hdich : ∀ n, (boxFam n)ᶜ = (R ∘ dualConfig) ⁻¹' (boxFam n))
    (hSharpThreshold : ∀ (p : ℝ≥0) (hp : p ≤ 1), (p : ℝ) < criticalProbability 2 →
        Tendsto (fun n => (bernoulliProductMeasure p hp).real (boxFam n)) atTop (𝓝 0)) :
    criticalProbability 2 = 1 / 2 :=
  kesten_pc_eq_half_of_bxp (ρ := 2) (R := R) (boxFam := boxFam)
    (ka_bxp_half_of_rsw hseed htinv) hCorLowerBound hHm hRmeas hRpres hdich hSharpThreshold

/-- Conditional Kesten theorem with `θ(1/2) = 0`; the second conjunct comes from `hCorLowerBound`.
-/
theorem ka_kesten_no_percolation_at_pc
    {R : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2))}
    {boxFam : ℕ → Set (ConfigSpace (Sym2 (Site 2)))}
    (hseed : KaSelfDualBoxSeed halfMeasure)
    (htinv : KaCrossingTranslationInvariant halfMeasure)
    (hCorLowerBound : BoxCrossingProperty halfMeasure 2 →
        percolationProbability 2 (2⁻¹ : ℝ≥0) half_le_one = 0)
    (hHm : ∀ n, MeasurableSet (boxFam n))
    (hRmeas : Measurable R) (hRpres : Measure.map R halfMeasure = halfMeasure)
    (hdich : ∀ n, (boxFam n)ᶜ = (R ∘ dualConfig) ⁻¹' (boxFam n))
    (hSharpThreshold : ∀ (p : ℝ≥0) (hp : p ≤ 1), (p : ℝ) < criticalProbability 2 →
        Tendsto (fun n => (bernoulliProductMeasure p hp).real (boxFam n)) atTop (𝓝 0)) :
    criticalProbability 2 = 1 / 2 ∧
      percolationProbability 2 (2⁻¹ : ℝ≥0) half_le_one = 0 :=
  ⟨ka_kesten_pc_eq_half hseed htinv hCorLowerBound hHm hRmeas hRpres hdich hSharpThreshold,
    hCorLowerBound (ka_bxp_half_of_rsw hseed htinv)⟩

/-- Conditional **Kesten theorem** `p_c(ℤ²) = 1/2` (Kesten 1980) with translation invariance
discharged. Remaining hypotheses: the RSW seed `hseed` at `p = 1/2`, Harris's theorem
`hCorLowerBound`, subcritical decay `hSharpThreshold` of a self-dual family `boxFam`, and the
self-duality identity `hdich` for that family. -/
theorem ka_kesten_pc_eq_half_of_seed
    {R : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2))}
    {boxFam : ℕ → Set (ConfigSpace (Sym2 (Site 2)))}
    (hseed : KaSelfDualBoxSeed halfMeasure)
    (hCorLowerBound : BoxCrossingProperty halfMeasure 2 →
        percolationProbability 2 (2⁻¹ : ℝ≥0) half_le_one = 0)
    (hHm : ∀ n, MeasurableSet (boxFam n))
    (hRmeas : Measurable R) (hRpres : Measure.map R halfMeasure = halfMeasure)
    (hdich : ∀ n, (boxFam n)ᶜ = (R ∘ dualConfig) ⁻¹' (boxFam n))
    (hSharpThreshold : ∀ (p : ℝ≥0) (hp : p ≤ 1), (p : ℝ) < criticalProbability 2 →
        Tendsto (fun n => (bernoulliProductMeasure p hp).real (boxFam n)) atTop (𝓝 0)) :
    criticalProbability 2 = 1 / 2 :=
  ka_kesten_pc_eq_half hseed kaCrossingTranslationInvariant_halfMeasure hCorLowerBound hHm
    hRmeas hRpres hdich hSharpThreshold

end Universality

end StatMech
