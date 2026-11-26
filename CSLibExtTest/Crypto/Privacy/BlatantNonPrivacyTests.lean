/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Privacy.BlatantNonPrivacy
public import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Tests for distortion and blatant non-privacy

* A subset-sum query on a database of three bits, and the empty query.
* Exact answers have distortion `0`, and a distortion bound can be weakened.
* For a deterministic mechanism, a point mass `diracProba` at each output, `BlatantlyNonPrivate`
  says that the adversary's candidate differs from the database in `o(n)` entries,
  `‖c - d‖₀ ∈ o(n)`.
* A mechanism whose answers have distortion below `1 / 2` with probability one is blatantly
  non-private, by rounding the answers to the singleton queries; so is the mechanism that
  releases the exact answers, and the one that releases the database.
* The mechanism that answers `0` to every query is not blatantly non-private.
* The mechanism that releases the database or its complement, each with probability `1 / 2`, is
  not blatantly non-private, although each of the two deterministic mechanisms it mixes is: the
  definition depends on the mechanism's randomness, not only on its possible outputs.
-/

@[expose] public section

namespace Cslib.Crypto.Privacy.BlatantNonPrivacyTests

open Asymptotics Filter MeasureTheory Cslib.Crypto.Privacy
open scoped ENNReal Topology

/-- The query `{0, 2}` on the database `(1, 0, 1)` counts two ones. -/
example : subsetSumQuery ![true, false, true] {0, 2} = 2 := by decide

/-- The empty query has answer `0`. -/
example {n : ℕ} (d : Fin n → Bool) : subsetSumQuery d ∅ = 0 := by simp [subsetSumQuery]

/-- The exact answers have distortion `0`. -/
example {n : ℕ} (d : Fin n → Bool) : HasDistortion d (fun q ↦ subsetSumQuery d q) 0 := by
  simp [HasDistortion]

/-- A distortion bound `E` implies every larger bound. -/
example {n : ℕ} {d : Fin n → Bool} {r : Finset (Fin n) → ℝ} {E E' : ℝ} (h : HasDistortion d r E)
    (hE : E ≤ E') : HasDistortion d r E' :=
  fun q ↦ (h q).trans hE

/-- The answer to a singleton query is the bit itself. -/
theorem subsetSumQuery_singleton {n : ℕ} (d : Fin n → Bool) (i : Fin n) :
    subsetSumQuery d {i} = (d i).toNat := by
  simp [subsetSumQuery]

/-- **Deterministic mechanisms.** For a mechanism that releases `f n d` on the database `d`,
blatant non-privacy says that some adversary's candidate differs from every family of databases
in `o(n)` entries, as in Definition 8.1 of Dwork and Roth. -/
theorem blatantlyNonPrivate_diracProba_iff {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    [∀ n, MeasurableSingletonClass (Ω n)] (f : ∀ n, (Fin n → Bool) → Ω n) :
    BlatantlyNonPrivate (fun n d ↦ diracProba (f n d)) ↔
      ∃ A : ∀ n, Ω n → Fin n → Bool, ∀ d : ∀ n, Fin n → Bool,
        (fun n ↦ (hammingDist (A n (f n (d n))) (d n) : ℝ)) =o[atTop] fun n ↦ (n : ℝ) := by
  have hdirac : ∀ n (x : Ω n) (S : Set (Ω n)), (diracProba x S : ℝ) = S.indicator 1 x := by
    intro n x S
    by_cases h : x ∈ S <;> simp [ProbabilityMeasure.coeFn_def, h]
  simp only [BlatantlyNonPrivate, hdirac]
  refine exists_congr fun A ↦ forall_congr' fun d ↦ ?_
  rw [isLittleO_iff]
  refine forall₂_congr fun ε hε ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have h0 := (h 0).eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
    filter_upwards [h0] with n hn
    by_cases hlt : ε * n < hammingDist (A n (f n (d n))) (d n)
    · simp [Set.indicator_of_mem (show f n (d n) ∈ {ω | ε * n < hammingDist (A n ω) (d n)}
        from hlt)] at hn
    · simpa [Real.norm_natCast] using not_lt.mp hlt
  · refine (superpolynomialDecay_zero atTop fun n : ℕ ↦ (n : ℝ)).congr' ?_
    filter_upwards [h] with n hn
    simp only [Real.norm_natCast] at hn
    exact (Set.indicator_of_notMem (show f n (d n) ∉ {ω | ε * n < hammingDist (A n ω) (d n)}
      from not_lt.mpr hn) _).symm

/-- **Distortion below `1 / 2` gives blatant non-privacy.** If, on every database, the answers
have distortion at most `E < 1 / 2` with probability one, rounding the answers to the singleton
queries reconstructs the database exactly. -/
theorem blatantlyNonPrivate_of_hasDistortion_lt_half
    (M : ∀ n, (Fin n → Bool) → ProbabilityMeasure (Finset (Fin n) → ℝ)) {E : ℝ} (hE : E < 1 / 2)
    (hM : ∀ n d, (M n d : Measure (Finset (Fin n) → ℝ)) {r | ¬ HasDistortion d r E} = 0) :
    BlatantlyNonPrivate M := by
  refine ⟨fun n r i ↦ decide (1 / 2 < r {i}), fun d ε hε ↦ ?_⟩
  have hround : ∀ n r, HasDistortion (d n) r E → (fun i ↦ decide (1 / 2 < r {i})) = d n := by
    intro n r hr
    funext i
    have h := abs_le.mp (hr {i})
    rw [subsetSumQuery_singleton] at h
    cases hd : d n i <;> simp only [hd, Bool.toNat_false, Bool.toNat_true] at h <;>
      simp only [decide_eq_true_eq, decide_eq_false_iff_not, not_lt] <;> push_cast at h <;>
      linarith [h.1, h.2]
  refine (superpolynomialDecay_zero atTop fun n : ℕ ↦ (n : ℝ)).congr fun n ↦ ?_
  have hsub : {r | ε * n < hammingDist (fun i ↦ decide (1 / 2 < r {i})) (d n)} ⊆
      {r | ¬ HasDistortion (d n) r E} := by
    intro r hr hdist
    simp only [Set.mem_ofPred_eq, hround n r hdist, hammingDist_self, Nat.cast_zero] at hr
    exact (mul_nonneg hε.le n.cast_nonneg).not_gt hr
  have h0 := measure_mono_null hsub (hM n (d n))
  simp only [ProbabilityMeasure.coeFn_def, h0, ENNReal.toNNReal_zero, NNReal.coe_zero,
    Pi.zero_apply]

/-- The mechanism that releases the exact answers is blatantly non-private. -/
example : BlatantlyNonPrivate fun n (d : Fin n → Bool) ↦
    diracProba fun q : Finset (Fin n) ↦ (subsetSumQuery d q : ℝ) := by
  refine blatantlyNonPrivate_of_hasDistortion_lt_half _ (E := 0) (by norm_num) fun n d ↦ ?_
  have : (fun q : Finset (Fin n) ↦ (subsetSumQuery d q : ℝ)) ∉
      {r | ¬ HasDistortion d r 0} := by
    simp [HasDistortion]
  simp [this]

/-- The mechanism that releases the database is blatantly non-private. -/
example : BlatantlyNonPrivate fun n (d : Fin n → Bool) ↦ diracProba d := by
  refine (blatantlyNonPrivate_diracProba_iff fun _ d ↦ d).mpr ⟨fun _ c ↦ c, fun d ↦ ?_⟩
  simp

/-- The mechanism that answers `0` to every query is not blatantly non-private: whatever the
adversary outputs from these answers, the complementary database differs from it everywhere. -/
example : ¬ BlatantlyNonPrivate fun n (_ : Fin n → Bool) ↦
    diracProba fun _ : Finset (Fin n) ↦ (0 : ℝ) := by
  rw [blatantlyNonPrivate_diracProba_iff]
  rintro ⟨A, hA⟩
  have h := hA fun n i ↦ !A n (fun _ ↦ 0) i
  have hd : ∀ n : ℕ, hammingDist (A n fun _ ↦ 0) (fun i ↦ !A n (fun _ ↦ 0) i) = n := by
    intro n
    simp [hammingDist]
  simp only [hd] at h
  refine isLittleO_irrefl ?_ h
  exact (eventually_ge_atTop 1).frequently.mono fun n hn ↦
    Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp hn)

/-- The mechanism that releases the complement of the database is blatantly non-private. -/
example : BlatantlyNonPrivate fun n (d : Fin n → Bool) ↦ diracProba fun i ↦ !d i := by
  refine (blatantlyNonPrivate_diracProba_iff fun _ d i ↦ !d i).mpr
    ⟨fun _ c i ↦ !c i, fun d ↦ ?_⟩
  simp

/-- **Randomized response on the whole database.** The law of the output that is `d` or its
complement, each with probability `1 / 2`. -/
noncomputable def keepOrFlip {n : ℕ} (d : Fin n → Bool) : ProbabilityMeasure (Fin n → Bool) :=
  ⟨(2⁻¹ : ℝ≥0∞) • Measure.dirac d + (2⁻¹ : ℝ≥0∞) • Measure.dirac fun i ↦ !d i,
    ⟨by simp [ENNReal.inv_two_add_inv_two]⟩⟩

/-- `keepOrFlip d` gives an event probability `1 / 2` for each of `d` and its complement that the
event contains. -/
theorem keepOrFlip_apply {n : ℕ} (d : Fin n → Bool) (S : Set (Fin n → Bool)) :
    (keepOrFlip d S : ℝ) =
      S.indicator (fun _ ↦ 1 / 2) d + S.indicator (fun _ ↦ 1 / 2) fun i ↦ !d i := by
  simp only [keepOrFlip, ProbabilityMeasure.mk_apply, add_apply, smul_apply, Measure.dirac_apply,
    smul_eq_mul]
  have half : (2⁻¹ : ℝ) + 2⁻¹ = 1 := by norm_num
  by_cases h₁ : d ∈ S <;> by_cases h₂ : (fun i ↦ !d i) ∈ S <;>
    simp [h₁, h₂, ENNReal.inv_two_add_inv_two, ENNReal.toNNReal_ofNat, half]

/-- A candidate is within `n / 4` of at most one of the all-`false` and the all-`true`
databases, as its distances to the two add up to `n`. -/
theorem quarter_lt_hammingDist {n : ℕ} (hn : 1 ≤ n) (c : Fin n → Bool) :
    (1 / 4 : ℝ) * n < hammingDist c (fun _ ↦ false) ∨
      (1 / 4 : ℝ) * n < hammingDist c (fun _ ↦ true) := by
  have key : hammingDist c (fun _ ↦ false) + hammingDist c (fun _ ↦ true) = n := by
    simp only [hammingDist, ne_eq, Bool.not_eq_false]
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]
  have key' : (hammingDist c (fun _ ↦ false) : ℝ) + hammingDist c (fun _ ↦ true) = n := by
    exact_mod_cast key
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  by_contra! h
  linarith [h.1, h.2]

/-- The mechanism `keepOrFlip` is not blatantly non-private: for each `n ≥ 1`, on the all-`false`
database or on the all-`true` one, every adversary fails with probability at least `1 / 2`. -/
example : ¬ BlatantlyNonPrivate fun n (d : Fin n → Bool) ↦ keepOrFlip d := by
  classical
  rintro ⟨A, hA⟩
  let u : ∀ n, Fin n → Bool := fun _ _ ↦ false
  let v : ∀ n, Fin n → Bool := fun _ _ ↦ true
  let F : ∀ n, (Fin n → Bool) → ℝ := fun n d ↦
    (keepOrFlip d {ω | (1 / 4 : ℝ) * n < hammingDist (A n ω) d} : ℝ)
  have hu : ∀ n, (fun i ↦ !u n i) = v n := fun n ↦ rfl
  have hv : ∀ n, (fun i ↦ !v n i) = u n := fun n ↦ rfl
  have hsum : ∀ n, 1 ≤ n → 1 ≤ F n (u n) + F n (v n) := by
    intro n hn
    simp only [F, keepOrFlip_apply, hu, hv]
    have i₁ := Set.indicator_nonneg (s := {ω | (1 / 4 : ℝ) * n < hammingDist (A n ω) (u n)})
      (f := fun _ ↦ (1 / 2 : ℝ)) (fun _ _ ↦ by norm_num)
    have i₂ := Set.indicator_nonneg (s := {ω | (1 / 4 : ℝ) * n < hammingDist (A n ω) (v n)})
      (f := fun _ ↦ (1 / 2 : ℝ)) (fun _ _ ↦ by norm_num)
    rcases quarter_lt_hammingDist hn (A n (u n)) with h₁ | h₁ <;>
      rcases quarter_lt_hammingDist hn (A n (v n)) with h₂ | h₂
    · rw [Set.indicator_of_mem (show u n ∈ _ from h₁),
        Set.indicator_of_mem (show v n ∈ _ from h₂)]
      linarith [i₁ (v n), i₂ (u n), i₂ (v n), i₁ (u n)]
    · rw [Set.indicator_of_mem (show u n ∈ _ from h₁),
        Set.indicator_of_mem (s := {ω | (1 / 4 : ℝ) * n < hammingDist (A n ω) (v n)})
          (show v n ∈ _ from h₂)]
      linarith [i₁ (v n), i₂ (u n), i₂ (v n), i₁ (u n)]
    · rw [Set.indicator_of_mem (s := {ω | (1 / 4 : ℝ) * n < hammingDist (A n ω) (v n)})
          (show u n ∈ _ from h₁),
        Set.indicator_of_mem (s := {ω | (1 / 4 : ℝ) * n < hammingDist (A n ω) (u n)})
          (show v n ∈ _ from h₂)]
      linarith [i₁ (v n), i₂ (u n), i₂ (v n), i₁ (u n)]
    · rw [Set.indicator_of_mem (s := {ω | (1 / 4 : ℝ) * n < hammingDist (A n ω) (v n)})
          (show u n ∈ _ from h₁),
        Set.indicator_of_mem (s := {ω | (1 / 4 : ℝ) * n < hammingDist (A n ω) (v n)})
          (show v n ∈ _ from h₂)]
      linarith [i₁ (v n), i₂ (u n), i₂ (v n), i₁ (u n)]
  let d : ∀ n, Fin n → Bool := fun n ↦ if 1 / 2 ≤ F n (u n) then u n else v n
  have hd : ∀ n, 1 ≤ n → 1 / 2 ≤ F n (d n) := by
    intro n hn
    by_cases h : 1 / 2 ≤ F n (u n)
    · rw [show d n = u n from ite_eq_left h]
      exact h
    · rw [show d n = v n from ite_eq_right h]
      linarith [hsum n hn]
  have h0 := ((hA d (1 / 4) (by norm_num)) 0).eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
  obtain ⟨n, hlt, hn⟩ := (h0.and (eventually_ge_atTop 1)).exists
  simp only [pow_zero, one_mul] at hlt
  exact (hd n hn).not_gt hlt

end Cslib.Crypto.Privacy.BlatantNonPrivacyTests
