/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Coalescent.VariableSFS

/-!
# Tests for the variable-size site frequency spectrum and identifiability

Kernel values and triangularity for `n = 3`, the variable-size spectrum for `n = 3` and its
constant-size reduction, the inversion corollary, Achaz-type estimators on a point-mass model
(non-vacuity of the estimator theorems), a non-vacuity witness for `integral_sfs_of_indep`
(sample size `2`, deterministic holding times), a non-vacuity witness for
`PiecewiseHistory` with boundary and junk-value checks, a second explicit tightness pair for
`K = 2`, the sharpness of `n ≥ 2K` at `K = 3`, and the finite-sample non-identifiability.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

namespace MathlibExtTest.Biology.PopulationGenetics.Coalescent.VariableSFS

open MathlibExt.Biology.PopulationGenetics.Coalescent
open MathlibExt.Biology.PopulationGenetics.Coalescent.SiteFrequencySpectrum
open MathlibExt.Biology.PopulationGenetics.Coalescent.VariableSFS

/-! ### The kernel for `n = 3` -/

/-- `n = 3`: singletons are expected once among two lineages and three times among three;
doubletons once among two lineages and never among three (the vanishing entry above the
anti-diagonal). -/
example : sfsKernel 3 1 2 = 1 ∧ sfsKernel 3 1 3 = 3 ∧ sfsKernel 3 2 2 = 1 ∧
    sfsKernel 3 2 3 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [sfsKernel, Nat.choose]

/-- The vanishing entry via `sfsKernel_eq_zero_of_lt`. -/
example : sfsKernel 3 2 3 = 0 := sfsKernel_eq_zero_of_lt (by norm_num) (by norm_num)

/-- The variable-size spectrum for `n = 3`: `E ξ₁ = (θ/2)(t₂ + 3 t₃)`, `E ξ₂ = (θ/2) t₂`. -/
example (θ : ℝ) (t : ℕ → ℝ) :
    variableSFS θ 3 t 1 = θ / 2 * (t 2 + 3 * t 3) ∧ variableSFS θ 3 t 2 = θ / 2 * t 2 := by
  have hI : (Icc 2 3 : Finset ℕ) = {2, 3} := by decide
  refine ⟨?_, ?_⟩ <;> simp only [variableSFS, hI] <;>
    rw [sum_insert (by decide), sum_singleton] <;> norm_num [sfsKernel, Nat.choose]

/-- The constant-size means recover Fu's spectrum `θ / i`. -/
example (θ : ℝ) : variableSFS θ 3 (fun k => ((k.choose 2 : ℕ) : ℝ)⁻¹) 2 = θ / 2 := by
  rw [variableSFS_inv_choose_two θ (by norm_num) (by norm_num)]
  norm_num

/-- Inversion for `n = 3`: equal expected spectra force equal `E T₂` and `E T₃`. -/
example {t t' : ℕ → ℝ} (h1 : variableSFS 1 3 t 1 = variableSFS 1 3 t' 1)
    (h2 : variableSFS 1 3 t 2 = variableSFS 1 3 t' 2) : t 2 = t' 2 ∧ t 3 = t' 3 := by
  have h := eq_of_variableSFS_eq one_ne_zero (n := 3) (t := t) (t' := t') (fun i hi => by
    have : i = 1 ∨ i = 2 := by simp only [mem_Ico] at hi; omega
    rcases this with rfl | rfl
    exacts [h1, h2])
  exact ⟨h 2 (by decide), h 3 (by decide)⟩

/-- With `θ = 0` the expected spectrum is identically `0`, so the hypothesis `θ ≠ 0` of
`eq_of_variableSFS_eq` cannot be dropped. -/
example (t : ℕ → ℝ) (i : ℕ) : variableSFS 0 3 t i = variableSFS 0 3 (fun _ => 0) i := by
  simp [variableSFS]

/-! ### Weighted estimators on a point-mass model -/

section Estimators

/-- The point-mass model: the counts are their constant-size means `θ / i`. -/
noncomputable def xiMean (θ : ℝ) (i : ℕ) : Unit → ℝ := fun _ => θ / i

lemma integrable_xiMean (θ : ℝ) (i : ℕ) : Integrable (xiMean θ i) (Measure.dirac ()) :=
  integrable_const _

lemma integral_xiMean (θ : ℝ) (n : ℕ) :
    ∀ i ∈ Ico 1 n, (Measure.dirac ())[xiMean θ i] = θ / i := fun i _ => by
  simp [xiMean]

/-- **Non-vacuity** of the estimator theorems: Fay–Wu's `H` and both Fu–Li numerators have
mean zero on the point-mass model, for `n = 5`. -/
example (θ : ℝ) : (Measure.dirac ())[fayWuH 5 (xiMean θ)] = 0 ∧
    (Measure.dirac ())[fuLiDNumerator 5 (xiMean θ)] = 0 ∧
    (Measure.dirac ())[fuLiFNumerator 5 (xiMean θ)] = 0 :=
  ⟨integral_fayWuH (by norm_num) (integrable_xiMean θ) (integral_xiMean θ 5),
    integral_fuLiDNumerator (by norm_num) (integrable_xiMean θ) (integral_xiMean θ 5),
    integral_fuLiFNumerator (by norm_num) (integrable_xiMean θ) (integral_xiMean θ 5)⟩

/-- Watterson's weights `1 / (i a₁)` sum to `1`, so `S / a₁` is a weighted estimator. -/
example (θ : ℝ) :
    (Measure.dirac ())[thetaWeighted 4 (fun i => 1 / (i * tajimaA1 4)) (xiMean θ)] = θ := by
  refine integral_thetaWeighted (integrable_xiMean θ) (integral_xiMean θ 4) ?_
  have hI : (Ico 1 4 : Finset ℕ) = {1, 2, 3} := by decide
  norm_num [tajimaA1, hI, sum_insert, sum_singleton]

end Estimators

/-! ### Non-vacuity of the variable-size spectrum: deterministic holding times -/

section Witness

/-- The single pair of positions among two blocks. -/
lemma blockPairs_two : blockPairs 2 = {(0, 1)} := by decide

/-- Merging two singletons. -/
lemma mergeBlocks_two : mergeBlocks [1, 1] 0 1 = [2] := rfl

/-- The random-joining law for two singletons is the point mass at `[[1, 1], [2]]`. -/
lemma randomJoining_two (ps : List (List ℕ)) :
    randomJoining (2 - 1) (List.replicate 2 1) ps = if ps = [[1, 1], [2]] then 1 else 0 := by
  have hl : (List.replicate 2 1).length = 2 := rfl
  rcases ps with _ | ⟨b, rest⟩
  · simp [randomJoining, blockPairs_two]
  · by_cases hb : b = [1, 1]
    · subst hb
      by_cases hr : rest = [[2]]
      · subst hr
        simp only [randomJoining, hl, blockPairs_two, sum_singleton, card_singleton]
        norm_num [mergeBlocks_two]
      · simp only [randomJoining, hl, blockPairs_two, sum_singleton, card_singleton]
        simp [mergeBlocks_two, hr]
    · simp [randomJoining, blockPairs_two, hb]

/-- Deterministic holding times (for example those of a population whose size changed): the
time with two lineages is `5`. -/
noncomputable def Tdet (k : ℕ) : Unit → ℝ := fun _ => if k = 2 then 5 else 0

/-- The unique block-size history for two copies. -/
def tauDet : Unit → List (List ℕ) := fun _ => [[1, 1], [2]]

/-- The counts, equal to their conditional means. -/
noncomputable def xiDet (θ : ℝ) (i : ℕ) : Unit → ℝ :=
  fun ω => θ / 2 * sfsLength 2 i (tauDet ω) (fun k => Tdet k ω)

lemma le_bot_of_unit (m : MeasurableSpace Unit) : m ≤ ⊥ := fun s _ => by
  rw [MeasurableSpace.measurableSet_bot_iff]
  rcases Set.eq_empty_or_nonempty s with h | ⟨x, hx⟩
  · exact Or.inl h
  · exact Or.inr (Set.eq_univ_of_forall fun y => by cases x; cases y; exact hx)

lemma law_tauDet (ps : List (List ℕ)) :
    (Measure.dirac ()).real (tauDet ⁻¹' {ps}) =
      randomJoining (2 - 1) (List.replicate 2 1) ps := by
  rw [randomJoining_two]
  by_cases h : ps = [[1, 1], [2]]
  · subst h
    have hu : tauDet ⁻¹' {[[1, 1], [2]]} = Set.univ := by ext ω; simp [tauDet]
    rw [hu, probReal_univ]
    simp
  · have : tauDet ⁻¹' {ps} = ∅ := by ext ω; simp [tauDet, Ne.symm h]
    simp [this, h]

lemma condExp_xiDet (θ : ℝ) (i : ℕ) :
    (Measure.dirac ())[xiDet θ i | MeasurableSpace.comap tauDet ⊤ ⊔
        MeasurableSpace.comap (fun ω k => Tdet k ω) MeasurableSpace.pi] =ᵐ[Measure.dirac ()]
      fun ω => θ / 2 * sfsLength 2 i (tauDet ω) (fun k => Tdet k ω) := by
  refine (condExp_of_stronglyMeasurable (μ := Measure.dirac ()) (f := xiDet θ i)
    (m := MeasurableSpace.comap tauDet ⊤ ⊔
      MeasurableSpace.comap (fun ω k => Tdet k ω) MeasurableSpace.pi)
    (fun _ _ => Subsingleton.measurableSet) ?_ Integrable.of_finite).eventuallyEq
  exact stronglyMeasurable_const' fun x y => by cases x; cases y; rfl

/-- **Non-vacuity**: every hypothesis of `integral_sfs_of_indep` holds for two copies,
deterministic holding times `T₂ = 5` and `ξ i` equal to its conditional mean; the conclusion
is `E ξ₁ = (θ / 2) · 2 · 5 = 5θ`. -/
example (θ : ℝ) : (Measure.dirac ())[xiDet θ 1] = 5 * θ := by
  rw [integral_sfs_of_indep (n := 2) (T := Tdet) (τ := tauDet) (θ := θ) (ξ := xiDet θ)
    (fun _ => measurable_const)
    (fun _ _ => integrable_const _) le_top law_tauDet
    (indep_of_indep_of_le_left (indep_bot_left _) (le_bot_of_unit _))
    (fun _ => Integrable.of_finite) (condExp_xiDet θ) le_rfl (by norm_num)]
  simp [variableSFS, sfsKernel, Tdet]
  ring

end Witness

/-! ### Piecewise-constant histories -/

/-- A two-piece history: size `1` on `[0, 1)` and size `2` after. -/
noncomputable def twoPiece : PiecewiseHistory 2 where
  size j := if j = 0 then 1 else 2
  start j := j
  size_pos j _ := by split_ifs <;> norm_num
  start_zero := by simp
  start_lt j _ := by push_cast; linarith

/-- **Non-vacuity**: the two-piece history has size `1` at `s = 1/2`, size `2` at the
breakpoint `s = 1` and at `s = 3`. -/
example : twoPiece.sizeFn (1 / 2) = 1 ∧ twoPiece.sizeFn 1 = 2 ∧ twoPiece.sizeFn 3 = 2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [PiecewiseHistory.sizeFn, twoPiece, sum_range_succ]

/-- Junk value: before the present (`s < 0`) the size function is `0`. -/
example : twoPiece.sizeFn (-1) = 0 := by
  simp [PiecewiseHistory.sizeFn, twoPiece, sum_range_succ]
  norm_num

/-- Junk value: for the zero size function the integrand of `c_m` is `1`, which is not
integrable on `(0, ∞)`, so `firstCoalMean` returns Lean's default `0`. -/
example : firstCoalMean (fun _ => 0) 2 = 0 := by
  simp [firstCoalMean, cumRate, Measure.real]

/-- Constant size (`K = 1`): `C(m,2) c_m = η₀`, so `c_2 = η₀`. -/
example (h : PiecewiseHistory 1) : firstCoalMean h.sizeFn 2 = h.size 0 := by
  have := h.choose_two_mul_firstCoalMean one_pos le_rfl
  simpa using this

/-- A two-piece history: size `1` on `[0, log 2)`, then size `3` (first half of the tightness
example). -/
noncomputable def tightA : PiecewiseHistory 2 where
  size j := if j = 0 then 1 else 3
  start j := if j = 0 then 0 else Real.log 2
  size_pos j _ := by split_ifs <;> norm_num
  start_zero := by simp
  start_lt j hj := by
    obtain rfl : j = 0 := by omega
    simpa using Real.log_pos one_lt_two

/-- A two-piece history: size `37/32` on `[0, (37/32) log 3)`, then size `59/16` (second half
of the tightness example). -/
noncomputable def tightB : PiecewiseHistory 2 where
  size j := if j = 0 then 37 / 32 else 59 / 16
  start j := if j = 0 then 0 else 37 / 32 * Real.log 3
  size_pos j _ := by split_ifs <;> norm_num
  start_zero := by simp
  start_lt j hj := by
    obtain rfl : j = 0 := by omega
    have := Real.log_pos (by norm_num : (1 : ℝ) < 3)
    simp only [↓reduceIte, Nat.add_eq_zero_iff, one_ne_zero, and_false]
    positivity

/-- The first coalescent-time breakpoint of a two-piece history. -/
private lemma cumRate_start_one (h : PiecewiseHistory 2) :
    cumRate h.sizeFn (h.start 1) = h.start 1 / h.size 0 := by
  rw [(h.cumRate_piece 0 (by norm_num) _ (h.start_lt 0 (by norm_num)).le fun _ => le_rfl).2]
  simp [h.start_zero, cumRate]

/-- The closed form of `C(m,2) c_m` for a two-piece history. -/
private lemma two_piece (h : PiecewiseHistory 2) {m : ℕ} (hm : 2 ≤ m) :
    ((m.choose 2 : ℕ) : ℝ) * firstCoalMean h.sizeFn m =
      h.size 0 + (h.size 1 - h.size 0) *
        Real.exp (-((m.choose 2 : ℕ) : ℝ) * (h.start 1 / h.size 0)) := by
  rw [h.choose_two_mul_firstCoalMean (by norm_num) hm,
    show (Ico 1 2 : Finset ℕ) = {1} by decide, sum_singleton, cumRate_start_one]

/-- **A second explicit pair for `K = 2`** with different breakpoints in coalescent time
(`log 2` and `log 3`, unlike the construction of `exists_ne_firstCoalMean_eq_of_lt`): with
`a c_m = η₀ + (η₁ - η₀) x^a`, `a = C(m,2)`, both histories give `a c_m = 2` at `a = 1` and
`5/4` at `a = 3` (`x = 1/2` and `x = 1/3`). -/
example :
    ∃ h h' : PiecewiseHistory 2, (∃ s, 0 ≤ s ∧ h.sizeFn s ≠ h'.sizeFn s) ∧
      ∀ m ∈ Icc 2 3, firstCoalMean h.sizeFn m = firstCoalMean h'.sizeFn m := by
  refine ⟨tightA, tightB, ⟨0, le_rfl, ?_⟩, fun m hm => ?_⟩
  · rw [tightA.sizeFn_eq (j := 0) (by norm_num) tightA.start_zero.le (fun hk => by
      simpa only [tightA.start_zero] using tightA.start_lt 0 hk),
      tightB.sizeFn_eq (j := 0) (by norm_num) tightB.start_zero.le (fun hk => by
      simpa only [tightB.start_zero] using tightB.start_lt 0 hk)]
    simp [tightA, tightB]
    norm_num
  · have hm2 := (mem_Icc.1 hm).1
    have ha : ((m.choose 2 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.choose_pos hm2).ne'
    refine mul_left_cancel₀ ha ?_
    rw [two_piece _ hm2, two_piece _ hm2]
    simp only [tightA, tightB, ↓reduceIte, one_ne_zero, div_one]
    have e2 : ∀ k : ℕ, Real.exp (-(k : ℝ) * Real.log 2) = ((2 : ℝ) ^ k)⁻¹ := fun k => by
      rw [neg_mul, Real.exp_neg, ← Real.log_pow, Real.exp_log (by positivity)]
    have e3 : ∀ k : ℕ, Real.exp (-(k : ℝ) * (37 / 32 * Real.log 3 / (37 / 32))) =
        ((3 : ℝ) ^ k)⁻¹ := fun k => by
      rw [show 37 / 32 * Real.log 3 / (37 / 32) = Real.log 3 by ring, neg_mul, Real.exp_neg,
        ← Real.log_pow, Real.exp_log (by positivity)]
    rw [e2, e3]
    have hm3 := (mem_Icc.1 hm).2
    obtain rfl | rfl : m = 2 ∨ m = 3 := by omega
    · norm_num
    · norm_num [Nat.choose]

/-- **The bound `n ≥ 2K` is sharp** for `K = 3`: `c_2, …, c_5` do not determine a three-piece
history, `c_2, …, c_6` do. -/
example : (∃ h h' : PiecewiseHistory 3, (∃ s, 0 ≤ s ∧ h.sizeFn s ≠ h'.sizeFn s) ∧
      ∀ m ∈ Icc 2 5, firstCoalMean h.sizeFn m = firstCoalMean h'.sizeFn m) ∧
    ∀ h h' : PiecewiseHistory 3,
      (∀ m ∈ Icc 2 6, firstCoalMean h.sizeFn m = firstCoalMean h'.sizeFn m) →
        ∀ s, 0 ≤ s → h.sizeFn s = h'.sizeFn s :=
  ⟨PiecewiseHistory.exists_ne_firstCoalMean_eq_of_lt 3 (by norm_num),
    fun h h' hc => PiecewiseHistory.sizeFn_eq_of_firstCoalMean_eq h h' (by norm_num) hc⟩

/-- **Non-vacuity** of the finite-sample non-identifiability: two bounded histories, different
on a set of positive measure, with the same `c_2, …, c_{20}`. -/
example : ∃ η₁ η₂ : ℝ → ℝ, Measurable η₁ ∧ Measurable η₂ ∧
      (∃ a b : ℝ, 0 < a ∧ ∀ s, a ≤ η₁ s ∧ η₁ s ≤ b ∧ a ≤ η₂ s ∧ η₂ s ≤ b) ∧
      ¬ (η₁ =ᵐ[volume.restrict (Set.Ici 0)] η₂) ∧
      ∀ m ∈ Icc 2 20, firstCoalMean η₁ m = firstCoalMean η₂ m :=
  exists_ne_ae_firstCoalMean_eq_Icc 20

/-- The first-coalescence times ignore the junk values of a size function before the present:
replacing `sizeFn` by its value at `max s 0` changes nothing. -/
example : firstCoalMean (fun s => twoPiece.sizeFn (max s 0)) 3 = firstCoalMean twoPiece.sizeFn 3 :=
  firstCoalMean_comp_max _ _

end MathlibExtTest.Biology.PopulationGenetics.Coalescent.VariableSFS
