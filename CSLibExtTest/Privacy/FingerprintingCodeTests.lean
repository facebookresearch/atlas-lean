/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Privacy.FingerprintingCode

/-!
# Tests for fingerprinting codes

A one-user code that always accuses its user meets the security predicates for nonempty coalitions
with error `0`. It falsely accuses with probability `1` against the empty coalition, so its
Bun, Ullman and Vadhan security holds only at `ξ = 1`. A code that never accuses, and one that
always accuses an innocent user, show that the completeness and soundness clauses can fail.
Concrete codebooks pin feasibility and β-feasibility, the Bernoulli and codebook masses,
independent draws, the keys of the generators, and Tardos's weights, scores and accusation rule.
-/

namespace CSLibExtTest.Privacy.FingerprintingCodeTests

open CSLibExt.Privacy.Fingerprinting
open scoped ENNReal

/-! ### A one-user code that always accuses its user -/

/-- The code for one user and one column whose codebook is all `false` and whose tracing always
accuses user `0`. -/
noncomputable def trivialCode : FingerprintingCode 1 1 Unit where
  gen := PMF.pure (fun _ _ => false, ())
  trace := fun _ _ => PMF.pure (some 0)

@[simp]
theorem trivialCode_gen :
    trivialCode.gen = PMF.pure (fun _ _ => false, ()) :=
  rfl

@[simp]
theorem trivialCode_trace (u : Unit) (w : Word 1) :
    trivialCode.trace u w = PMF.pure (some 0) :=
  rfl

/-- Every nonempty coalition of one user contains the user. -/
theorem zero_mem_of_nonempty {S : Finset (Fin 1)} (hS : S.Nonempty) : (0 : Fin 1) ∈ S := by
  obtain ⟨i, hi⟩ := hS
  rwa [Subsingleton.elim i 0] at hi

/-- Every outcome of the tracing game of `trivialCode` accuses user `0`. -/
theorem trivialCode_accuses {S : Finset (Fin 1)} (P : Pirate 1 1 S)
    {t : Codebook 1 1 × Word 1 × Option (Fin 1)} (ht : t ∈ (tracingGame trivialCode S P).support) :
    t.2.2 = some 0 := by
  simp only [tracingGame, trivialCode_gen, trivialCode_trace, PMF.pure_bind,
    PMF.mem_support_bind_iff, PMF.mem_support_map_iff, PMF.mem_support_pure_iff] at ht
  obtain ⟨w, _, a, rfl, rfl⟩ := ht
  rfl

/-- An event that contains no outcome accusing user `0` has probability `0` in the tracing game of
`trivialCode`. -/
theorem trivialCode_prob_eq_zero {S : Finset (Fin 1)} (P : Pirate 1 1 S)
    (E : Set (Codebook 1 1 × Word 1 × Option (Fin 1))) (hE : ∀ t ∈ E, t.2.2 ≠ some 0) :
    ((tracingGame trivialCode S P).toOuterMeasure E).toReal = 0 := by
  rw [(PMF.toOuterMeasure_apply_eq_zero_iff _ _).mpr, ENNReal.toReal_zero]
  exact Set.disjoint_left.mpr fun t ht htE => hE t htE (trivialCode_accuses P ht)

/-- Against a nonempty coalition, `trivialCode` never accuses an innocent user. -/
theorem trivialCode_soundnessErrorProb {S : Finset (Fin 1)} (hS : S.Nonempty)
    (P : Pirate 1 1 S) : soundnessErrorProb trivialCode S P = 0 := by
  refine trivialCode_prob_eq_zero P (soundnessFailureEvent S) fun t ht _ => ?_
  obtain ⟨i, hi, _⟩ := ht
  exact hi (Subsingleton.elim (0 : Fin 1) i ▸ zero_mem_of_nonempty hS)

theorem trivialCode_isFingerprintingSecure :
    IsFingerprintingSecure trivialCode 1 0 0 := by
  refine ⟨le_rfl, le_rfl, fun S hS _ P => ⟨?_, (trivialCode_soundnessErrorProb hS P).le⟩⟩
  refine (trivialCode_prob_eq_zero P (completenessFailureEvent S) fun t ht h0 => ?_).le
  have hnone : t.2.2 = none := ht.2
  rw [hnone] at h0
  exact Option.some_ne_none 0 h0.symm

theorem trivialCode_isErrorRobustFingerprintingSecure {β : ℝ} (hβ : 0 ≤ β) :
    IsErrorRobustFingerprintingSecure trivialCode 1 β 0 0 := by
  refine ⟨hβ, le_rfl, le_rfl, fun S hS _ P => ⟨?_, (trivialCode_soundnessErrorProb hS P).le⟩⟩
  refine (trivialCode_prob_eq_zero P (errorRobustCompletenessFailureEvent β S)
    fun t ht h0 => ?_).le
  have hnone : t.2.2 = none := ht.2
  rw [hnone] at h0
  exact Option.some_ne_none 0 h0.symm

theorem trivialCode_isFingerprintingSecureCombined :
    IsFingerprintingSecureCombined trivialCode 1 0 := by
  refine ⟨le_rfl, fun S hS _ P =>
    (trivialCode_prob_eq_zero P (combinedFailureEvent S) fun t ht h0 => ?_).le⟩
  exact ht.2 ⟨0, zero_mem_of_nonempty hS, h0⟩

/-- Against the empty coalition, which the nonempty-coalition predicates leave out, `trivialCode`
accuses an innocent user with probability `1`. -/
theorem trivialCode_empty_coalition_soundness (P : Pirate 1 1 ∅) :
    soundnessErrorProb trivialCode ∅ P = 1 := by
  rw [soundnessErrorProb, (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr, ENNReal.toReal_one]
  intro t ht
  exact ⟨0, Finset.notMem_empty 0, trivialCode_accuses P ht⟩

/-- Although `trivialCode` meets the nonempty-coalition predicate with zero errors, its
soundness error against the empty coalition rules out security below `1`. -/
theorem trivialCode_not_isBUVFingerprintingSecure {ξ : ℝ} (hξ : ξ < 1) :
    ¬ IsBUVFingerprintingSecure trivialCode ξ := by
  intro h
  let P : Pirate 1 1 ∅ := fun _ => PMF.pure fun _ => false
  have hs := (h.2.2 ∅ P).2
  rw [trivialCode_empty_coalition_soundness P] at hs
  exact hξ.not_ge hs

/-- The upper endpoint `1` is allowed, even for `trivialCode`. -/
theorem trivialCode_isBUVFingerprintingSecure_one : IsBUVFingerprintingSecure trivialCode 1 := by
  refine ⟨zero_lt_one, le_rfl, fun S P => ?_⟩
  have event_le_one (E : Set (Codebook 1 1 × Word 1 × Option (Fin 1))) :
      ((tracingGame trivialCode S P).toOuterMeasure E).toReal ≤ 1 := by
    let _ : MeasurableSpace (Codebook 1 1 × Word 1 × Option (Fin 1)) := ⊤
    rw [← PMF.toMeasure_apply_eq_toOuterMeasure_apply _ MeasurableSpace.measurableSet_top]
    exact MeasureTheory.measureReal_le_one
  exact ⟨event_le_one (completenessFailureEvent S), event_le_one (soundnessFailureEvent S)⟩

theorem trivialCode_isFingerprintingSecure_one : IsFingerprintingSecure trivialCode 1 1 1 :=
  trivialCode_isBUVFingerprintingSecure_one.isFingerprintingSecure

/-- The lower endpoint `0` is excluded by the security parameter range alone. -/
theorem not_isBUVFingerprintingSecure_zero {n d : ℕ} {Key : Type*}
    (FC : FingerprintingCode n d Key) : ¬ IsBUVFingerprintingSecure FC 0 :=
  fun h => (lt_irrefl (0 : ℝ)) h.1

/-! ### Codes that fail completeness or soundness -/

/-- The code for one user and one column whose codebook is all `false` and whose tracing never
accuses. -/
noncomputable def silentCode : FingerprintingCode 1 1 Unit where
  gen := PMF.pure (fun _ _ => false, ())
  trace := fun _ _ => PMF.pure none

/-- The pirate of user `0` that outputs the user's own codeword, a feasible word. -/
noncomputable def copyPirate : Pirate 1 1 {0} :=
  fun cs => PMF.pure (cs ⟨0, Finset.mem_singleton_self 0⟩)

/-- The pirate of user `0` that outputs the all-`true` word, which is not feasible against the
all-`false` codebook. -/
noncomputable def onesPirate : Pirate 1 1 {0} :=
  fun _ => PMF.pure fun _ => true

theorem silentCode_tracingGame_copyPirate :
    tracingGame silentCode {0} copyPirate = PMF.pure (fun _ _ => false, fun _ => false, none) := by
  simp only [tracingGame, silentCode, copyPirate, PMF.pure_bind, PMF.pure_map, submatrix_apply]

theorem silentCode_tracingGame_onesPirate :
    tracingGame silentCode {0} onesPirate = PMF.pure (fun _ _ => false, fun _ => true, none) := by
  simp only [tracingGame, silentCode, onesPirate, PMF.pure_bind, PMF.pure_map]

/-- A code that never accuses fails completeness with probability `1` against a pirate that copies
its codeword. -/
theorem silentCode_completenessErrorProb :
    completenessErrorProb silentCode {0} copyPirate = 1 := by
  rw [completenessErrorProb, silentCode_tracingGame_copyPirate, PMF.toOuterMeasure_pure_apply,
    ite_eq_left, ENNReal.toReal_one]
  exact ⟨fun _ => ⟨0, Finset.mem_singleton_self 0, rfl⟩, rfl⟩

/-- An infeasible word is no completeness failure, even when tracing accuses nobody. -/
theorem silentCode_completenessErrorProb_onesPirate :
    completenessErrorProb silentCode {0} onesPirate = 0 := by
  rw [completenessErrorProb, silentCode_tracingGame_onesPirate, PMF.toOuterMeasure_pure_apply,
    ite_eq_right, ENNReal.toReal_zero]
  rintro ⟨h, -⟩
  obtain ⟨i, hi, hw⟩ := h 0
  exact Bool.noConfusion hw

/-- The all-`true` word has no feasible column, so it is `β`-feasible exactly for `β ≥ 1`. -/
theorem silentCode_errorRobustCompletenessErrorProb_onesPirate (β : ℝ) :
    errorRobustCompletenessErrorProb β silentCode {0} onesPirate = if 1 ≤ β then 1 else 0 := by
  have hcard : (Finset.univ.filter fun j : Fin 1 => ∃ i ∈ ({0} : Finset (Fin 1)),
      (fun _ => true : Word 1) j = (fun _ _ => false : Codebook 1 1) i j).card = 0 := by
    decide
  have hiff : ErrorRobustFeasible β (fun _ _ => false : Codebook 1 1) {0} (fun _ => true) ↔
      1 ≤ β := by
    rw [ErrorRobustFeasible, hcard]
    constructor <;> intro h <;> push_cast at h ⊢ <;> linarith
  rw [errorRobustCompletenessErrorProb, silentCode_tracingGame_onesPirate,
    PMF.toOuterMeasure_pure_apply]
  by_cases hβ : 1 ≤ β
  · rw [ite_eq_left ⟨hiff.mpr hβ, rfl⟩, ite_eq_left hβ, ENNReal.toReal_one]
  · rw [ite_eq_right fun h => hβ (hiff.mp h.1), ite_eq_right hβ, ENNReal.toReal_zero]

/-- The completeness clause has content: a code that never accuses is not secure for any
completeness error below `1`. -/
theorem silentCode_not_isFingerprintingSecure {γ ξ : ℝ} (hγ : γ < 1) :
    ¬ IsFingerprintingSecure silentCode 1 γ ξ := fun h => by
  have := (h.2.2 {0} (Finset.singleton_nonempty 0) (by simp) copyPirate).1
  rw [silentCode_completenessErrorProb] at this
  linarith

/-- The code for two users and one column whose codebook is all `false` and whose tracing always
accuses user `1`. -/
noncomputable def accuseOneCode : FingerprintingCode 2 1 Unit where
  gen := PMF.pure (fun _ _ => false, ())
  trace := fun _ _ => PMF.pure (some 1)

/-- The pirate of user `0` that outputs the user's own codeword. -/
noncomputable def copyPirate₂ : Pirate 2 1 {0} :=
  fun cs => PMF.pure (cs ⟨0, Finset.mem_singleton_self 0⟩)

theorem accuseOneCode_tracingGame :
    tracingGame accuseOneCode {0} copyPirate₂ =
      PMF.pure (fun _ _ => false, fun _ => false, some 1) := by
  simp only [tracingGame, accuseOneCode, copyPirate₂, PMF.pure_bind, PMF.pure_map,
    submatrix_apply]

/-- A code that accuses user `1` falsely accuses with probability `1` against the coalition of
user `0`. -/
theorem accuseOneCode_soundnessErrorProb :
    soundnessErrorProb accuseOneCode {0} copyPirate₂ = 1 := by
  rw [soundnessErrorProb, accuseOneCode_tracingGame, PMF.toOuterMeasure_pure_apply, ite_eq_left,
    ENNReal.toReal_one]
  exact ⟨1, by decide, rfl⟩

/-- The same game is a combined failure: the word is feasible and the accused user is innocent. -/
theorem accuseOneCode_combinedErrorProb :
    combinedErrorProb accuseOneCode {0} copyPirate₂ = 1 := by
  rw [combinedErrorProb, accuseOneCode_tracingGame, PMF.toOuterMeasure_pure_apply, ite_eq_left,
    ENNReal.toReal_one]
  refine ⟨fun _ => ⟨0, Finset.mem_singleton_self 0, rfl⟩, ?_⟩
  rintro ⟨i, hi, h⟩
  rw [Finset.mem_singleton] at hi
  subst hi
  exact absurd (Option.some.inj h) (by decide)

theorem accuseOneCode_not_isFingerprintingSecureCombined {ε : ℝ} (hε : ε < 1) :
    ¬ IsFingerprintingSecureCombined accuseOneCode 2 ε := fun h => by
  have := h.2 {0} (Finset.singleton_nonempty 0) (by simp) copyPirate₂
  rw [accuseOneCode_combinedErrorProb] at this
  linarith

/-! ### Feasible words -/

/-- Two users and two columns: the users agree on column `0` and differ on column `1`. -/
def C₂ : Codebook 2 2 := ![![true, true], ![true, false]]

example : Feasible C₂ Finset.univ ![true, false] := by
  unfold Feasible C₂; decide

example : ¬ Feasible C₂ Finset.univ ![false, false] := by
  unfold Feasible C₂; decide

example : ¬ Feasible C₂ ∅ ![true, true] := by
  unfold Feasible C₂; decide

example : MarkingFeasible C₂ Finset.univ ![true, true] :=
  (feasible_iff_markingFeasible _ _ _).mp (by unfold Feasible C₂; decide)

example : ¬ MarkingFeasible C₂ {1} ![true, true] := fun h =>
  absurd ((feasible_iff_markingFeasible _ _ _).mpr h) (by unfold Feasible C₂; decide)

/-- User `0` alone and the word `(1, 0)`: column `0` is feasible and column `1` is not. -/
theorem card_feasibleColumns :
    (Finset.univ.filter fun j : Fin 2 =>
      ∃ i ∈ ({0} : Finset (Fin 2)), (![true, false] : Word 2) j = C₂ i j).card = 1 := by
  unfold C₂; decide

example : ErrorRobustFeasible (1 / 2) C₂ {0} ![true, false] := by
  rw [ErrorRobustFeasible, card_feasibleColumns]; norm_num

example : ¬ ErrorRobustFeasible (1 / 4) C₂ {0} ![true, false] := by
  rw [ErrorRobustFeasible, card_feasibleColumns]; norm_num

example : ¬ ErrorRobustFeasible 0 C₂ {0} ![true, false] := by
  rw [errorRobustFeasible_zero_iff]; unfold Feasible C₂; decide

/-! ### Bernoulli distribution and codebook generation -/

/-- The bias `1 / 4`. -/
noncomputable def quarter : unitInterval := ⟨1 / 4, by norm_num, by norm_num⟩

/-- The bias `1 / 3`. -/
noncomputable def third : unitInterval := ⟨1 / 3, by norm_num, by norm_num⟩

example : bernoulliPMF quarter false = ENNReal.ofReal (3 / 4) := by
  rw [bernoulliPMF_false]; norm_num [quarter]

/-- `bernoulliPMF` is Mathlib's Bernoulli distribution on `Bool`. -/
theorem toMeasure_bernoulliPMF (p : unitInterval) :
    (bernoulliPMF p).toMeasure = ProbabilityTheory.bernoulliMeasure true false p := by
  rw [MeasureTheory.Measure.ext_iff_singleton]
  intro b
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton b), bernoulliPMF_apply,
    ProbabilityTheory.bernoulliMeasure_apply p (measurableSet_singleton b)]
  cases b <;> simp [bernoulliMass, ENNReal.ofReal, unitInterval.toNNReal]
  case false => rw [Real.toNNReal_of_nonneg (sub_nonneg.mpr p.2.2)]; rfl
  case true => rw [Real.toNNReal_of_nonneg p.2.1]; rfl

/-- Rows `(1, 0)` and `(0, 0)` with column biases `1 / 4` and `1 / 3` have mass
`(1/4 · 2/3) · (3/4 · 2/3) = 1/12`. -/
theorem biasCodebookPMF_example :
    biasCodebookPMF ![quarter, third] ![![true, false], ![false, false]] =
      ENNReal.ofReal (1 / 12) := by
  rw [biasCodebookPMF_apply]
  simp only [Fin.prod_univ_two, bernoulliMass, Matrix.cons_val_zero, Matrix.cons_val_one,
    ite_true, Bool.false_eq_true, ite_false, unitInterval.coe_symm_eq, quarter, third]
  rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_mul (by norm_num)]
  norm_num

/-- `pmfIID μ d` is the product of `d` copies of `μ`. -/
theorem pmfIID_apply_eq_prod {α : Type*} (μ : PMF α) (d : ℕ) (f : Fin d → α) :
    pmfIID μ d f = ∏ j, μ (f j) := by
  induction d with
  | zero =>
    rw [pmfIID_zero, PMF.pure_apply, ite_eq_left (Subsingleton.elim _ _), Finset.univ_eq_empty,
      Finset.prod_empty]
  | succ d ih =>
    rw [pmfIID_succ, PMF.bind_apply, tsum_eq_single (f 0), PMF.map_apply,
      tsum_eq_single (Fin.tail f), ite_eq_left (Fin.cons_self_tail f).symm, ih, Fin.prod_univ_succ]
    · rfl
    · intro g hg
      exact ite_eq_right fun h => hg (by rw [h, Fin.tail_cons])
    · intro x hx
      rw [PMF.map_apply]
      convert mul_zero (μ x)
      exact tsum_eq_zero_iff.mpr fun g => ite_eq_right fun h => hx (by rw [h, Fin.cons_zero])

example : pmfIID (bernoulliPMF quarter) 2 ![true, false] =
    ENNReal.ofReal (1 / 4) * ENNReal.ofReal (3 / 4) := by
  rw [pmfIID_apply_eq_prod, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_zero, bernoulliPMF_true, bernoulliPMF_false]
  norm_num [quarter]

/-- Independent draws from a point mass are the constant vector. -/
theorem pmfIID_pure {α : Type*} (a : α) (d : ℕ) :
    pmfIID (PMF.pure a) d = PMF.pure fun _ => a := by
  ext f
  rw [pmfIID_apply_eq_prod, PMF.pure_apply]
  by_cases hf : f = fun _ => a
  · subst hf
    simp
  · rw [ite_eq_right hf]
    obtain ⟨j, hj⟩ : ∃ j, f j ≠ a := by
      by_contra! h
      exact hf (funext h)
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by rw [PMF.pure_apply, ite_eq_right hj])

/-- The key of `genFromBiasVectorDist` is the drawn bias vector, distributed as `biasDist`. -/
theorem genFromBiasVectorDist_map_snd {n d : ℕ} (biasDist : PMF (Fin d → unitInterval)) :
    (genFromBiasVectorDist (n := n) biasDist).map Prod.snd = biasDist := by
  rw [genFromBiasVectorDist_def, PMF.map_bind]
  simp_rw [PMF.map_comp]
  exact (congrArg biasDist.bind (funext fun p => PMF.map_const _ p)).trans (PMF.bind_pure _)

/-- Given a fixed bias vector, the codebook of `genFromBiasVectorDist` is drawn from
`biasCodebookPMF`. -/
theorem genFromBiasVectorDist_pure_map_fst {n d : ℕ} (p : Fin d → unitInterval) :
    (genFromBiasVectorDist (n := n) (PMF.pure p)).map Prod.fst = biasCodebookPMF p := by
  rw [genFromBiasVectorDist_def, PMF.pure_bind, PMF.map_comp]
  exact PMF.map_id _

/-- The key of `genFromIIDBiasDist` is `d` independent biases. -/
theorem genFromIIDBiasDist_map_snd {n d : ℕ} (μ : PMF unitInterval) :
    (genFromIIDBiasDist (n := n) (d := d) μ).map Prod.snd = pmfIID μ d :=
  genFromBiasVectorDist_map_snd _

/-- With a point-mass bias distribution, `genFromIIDBiasDist` draws every entry with that bias. -/
theorem genFromIIDBiasDist_pure_map_fst {n d : ℕ} (q : unitInterval) :
    (genFromIIDBiasDist (n := n) (d := d) (PMF.pure q)).map Prod.fst =
      biasCodebookPMF fun _ => q := by
  rw [genFromIIDBiasDist_def, pmfIID_pure]
  exact genFromBiasVectorDist_pure_map_fst _

/-! ### Tardos weights, scores and accusations -/

theorem tardosWeight_half_true : tardosWeight (1 / 2) true = 1 := by
  have h : ((1 : ℝ) - 1 / 2) / (1 / 2) = 1 := by norm_num
  rw [tardosWeight_true, h, Real.sqrt_one]

theorem tardosWeight_half_false : tardosWeight (1 / 2) false = -1 := by
  have h : ((1 / 2 : ℝ) / (1 - 1 / 2)) = 1 := by norm_num
  rw [tardosWeight_false, h, Real.sqrt_one]

/-- At bias `1 / 5` the two weights are `2` and `-1 / 2`, which tells the formulas apart. -/
theorem tardosWeight_fifth_true : tardosWeight (1 / 5) true = 2 := by
  rw [tardosWeight_true, show ((1 : ℝ) - 1 / 5) / (1 / 5) = 2 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]

theorem tardosWeight_fifth_false : tardosWeight (1 / 5) false = -(1 / 2) := by
  rw [tardosWeight_false, show ((1 / 5 : ℝ) / (1 - 1 / 5)) = (1 / 2) ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]

/-- Outside `(0, 1)` both weights are `0`. -/
theorem tardosWeight_eq_zero_of_notMem {p : ℝ} (hp : p ∉ Set.Ioo 0 1) (b : Bool) :
    tardosWeight p b = 0 := by
  rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at hp
  cases b
  · rw [tardosWeight_false, neg_eq_zero, Real.sqrt_eq_zero']
    rcases hp with hp | hp
    · exact div_nonpos_of_nonpos_of_nonneg hp (by linarith)
    · exact div_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  · rw [tardosWeight_true, Real.sqrt_eq_zero']
    rcases hp with hp | hp
    · exact div_nonpos_of_nonneg_of_nonpos (by linarith) hp
    · exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)

/-- Three columns; user `0` holds `(1, 0, 1)` and user `1` holds `(1, 1, 0)`. -/
def C₃ : Codebook 2 3 := ![![true, false, true], ![true, true, false]]

/-- The pirated word `(1, 1, 0)`. -/
def w₃ : Word 3 := ![true, true, false]

/-- Columns of bias `1 / 2`, where the weights are `1` and `-1`. -/
noncomputable def half : Fin 3 → ℝ := fun _ => 1 / 2

/-- Columns of biases `1 / 5`, `1 / 2` and `1 / 2`. -/
noncomputable def skewed : Fin 3 → ℝ := ![1 / 5, 1 / 2, 1 / 2]

/-- User `0` matches a `1` of the word and misses the other; column `2`, where the word is `0`,
does not count: score `1 - 1 = 0`. -/
theorem tardosScore_half_user0 : tardosScore half C₃ w₃ 0 = 0 := by
  simp only [tardosScore, Fin.sum_univ_three, C₃, w₃, half, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, ite_true,
    ite_false, Bool.false_eq_true, tardosWeight_half_true, tardosWeight_half_false]
  norm_num

theorem tardosScore_half_user1 : tardosScore half C₃ w₃ 1 = 2 := by
  simp only [tardosScore, Fin.sum_univ_three, C₃, w₃, half, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, ite_true,
    ite_false, Bool.false_eq_true, tardosWeight_half_true]
  norm_num

/-- With the bias `1 / 5` in column `0`, user `0` scores `2 - 1 = 1` and user `1` scores
`2 + 1 = 3`. -/
theorem tardosScore_skewed_user0 : tardosScore skewed C₃ w₃ 0 = 1 := by
  simp only [tardosScore, Fin.sum_univ_three, C₃, w₃, skewed, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, ite_true,
    ite_false, Bool.false_eq_true, tardosWeight_fifth_true, tardosWeight_half_false]
  norm_num

theorem tardosScore_skewed_user1 : tardosScore skewed C₃ w₃ 1 = 3 := by
  simp only [tardosScore, Fin.sum_univ_three, C₃, w₃, skewed, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, ite_true,
    ite_false, Bool.false_eq_true, tardosWeight_fifth_true, tardosWeight_half_true]
  norm_num

example : TardosAccuses half 1 C₃ w₃ 1 := by
  rw [tardosAccuses_iff, tardosScore_half_user1]; norm_num

example : ¬ TardosAccuses half 1 C₃ w₃ 0 := by
  rw [tardosAccuses_iff, tardosScore_half_user0]; norm_num

/-- The threshold is strict: a score equal to `Z` is no accusation. -/
example : ¬ TardosAccuses half 2 C₃ w₃ 1 := by
  rw [tardosAccuses_iff, tardosScore_half_user1]; exact lt_irrefl 2

example : TardosAccuses skewed 2 C₃ w₃ 1 ∧ ¬ TardosAccuses skewed 2 C₃ w₃ 0 := by
  rw [tardosAccuses_iff, tardosAccuses_iff, tardosScore_skewed_user0, tardosScore_skewed_user1]
  norm_num

#print axioms CSLibExt.Privacy.Fingerprinting.bernoulliPMF
#print axioms CSLibExt.Privacy.Fingerprinting.biasCodebookPMF
#print axioms CSLibExt.Privacy.Fingerprinting.genFromIIDBiasDist
#print axioms CSLibExt.Privacy.Fingerprinting.tracingGame
#print axioms CSLibExt.Privacy.Fingerprinting.feasible_iff_markingFeasible
#print axioms CSLibExt.Privacy.Fingerprinting.errorRobustFeasible_zero_iff
#print axioms trivialCode_isFingerprintingSecure
#print axioms trivialCode_isFingerprintingSecureCombined
#print axioms trivialCode_empty_coalition_soundness
#print axioms CSLibExt.Privacy.Fingerprinting.IsBUVFingerprintingSecure
#print axioms CSLibExt.Privacy.Fingerprinting.IsBUVFingerprintingSecure.isFingerprintingSecure
#print axioms trivialCode_not_isBUVFingerprintingSecure
#print axioms trivialCode_isBUVFingerprintingSecure_one
#print axioms trivialCode_isFingerprintingSecure_one
#print axioms not_isBUVFingerprintingSecure_zero
#print axioms pmfIID_apply_eq_prod
#print axioms toMeasure_bernoulliPMF

end CSLibExtTest.Privacy.FingerprintingCodeTests
