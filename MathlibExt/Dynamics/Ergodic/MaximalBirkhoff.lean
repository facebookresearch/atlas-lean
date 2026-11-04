/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Dynamics.Ergodic.KingmanSigned.MaximalErgodic

/-!
# The maximal ergodic inequality with the empty Birkhoff sum

For `T : α → α` and `f : α → ℝ`, let `maxBirkhoff T f n x = max_{0 ≤ k ≤ n} S_k f x`, where
`S_k f = ∑_{j<k} f ∘ T^j` and `S_0 f = 0`, so `maxBirkhoff ≥ 0`. For measure-preserving `T` and
integrable `f` this file proves the maximal ergodic inequality `∫_{maxBirkhoff > 0} f dμ ≥ 0` and
the Hopf maximal inequality `a μ(E_a) ≤ ∫_{E_a} f dμ` for the level set
`E_a = {max_{k ≤ n} S_k (f - a) > 0}`.

The set `{maxBirkhoff T f n > 0}` equals Garsia's `{max_{1 ≤ k ≤ n} S_k f > 0}` for `n ≥ 1`
(`StatMech.Birkhoff.pos_maxBirkhoff_iff_pos_maxPartialSum`), so
`StatMech.Birkhoff.maximal_ergodic_inequality` is `StatMech.GarsiaMax.garsia_maximal_inequality`
(in `MathlibExt.Dynamics.Ergodic.KingmanSigned.MaximalErgodic`) in another form; the limiting form
is `MathlibExt.Dynamics.Ergodic.BirkhoffWanted.maximal_ergodic`.

## Main definitions

* `StatMech.Birkhoff.maxBirkhoff`: `max_{0 ≤ k ≤ n} S_k f`.
* `StatMech.Birkhoff.maximalLevelSet`: `{max_{k ≤ n} S_k (f - a) > 0}`.

## Main results

* `StatMech.Birkhoff.maximal_ergodic_inequality`: `0 ≤ ∫_{maxBirkhoff > 0} f dμ`.
* `StatMech.Birkhoff.hopf_maximal_inequality`: `a μ(E_a) ≤ ∫_{E_a} f dμ`.

## References

* A. M. Garsia, *A simple proof of E. Hopf's maximal ergodic theorem*, J. Math. Mech. 14
  (1965), 381–382.
* K. Petersen, *Ergodic Theory*, Cambridge (1983), Section 2.2.
-/

@[expose] public section

open MeasureTheory Filter Finset Function
open scoped Topology

namespace StatMech

namespace Birkhoff

variable {α : Type*} {T : α → α} {f : α → ℝ}

/-- The maximal Birkhoff sum `max_{0 ≤ k ≤ n} S_k f x`, including `S_0 f = 0`. -/
noncomputable def maxBirkhoff (T : α → α) (f : α → ℝ) (n : ℕ) (x : α) : ℝ :=
  (Finset.range (n + 1)).sup' (Finset.nonempty_range_iff.mpr n.succ_ne_zero)
    (fun k => birkhoffSum T f k x)

/-- Unfolding of `maxBirkhoff`. -/
theorem maxBirkhoff_eq_sup' (n : ℕ) (x : α) :
    maxBirkhoff T f n x =
      (Finset.range (n + 1)).sup' (Finset.nonempty_range_iff.mpr n.succ_ne_zero)
        (fun k => birkhoffSum T f k x) := rfl

/-- `S_k f x ≤ maxBirkhoff T f n x` for `k ≤ n`. -/
theorem birkhoffSum_le_maxBirkhoff {n k : ℕ} (hk : k ≤ n) (x : α) :
    birkhoffSum T f k x ≤ maxBirkhoff T f n x :=
  Finset.le_sup' (fun k => birkhoffSum T f k x) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))

/-- `maxBirkhoff T f n x ≥ 0`, since it includes `S_0 f = 0`. -/
theorem maxBirkhoff_nonneg (n : ℕ) (x : α) : 0 ≤ maxBirkhoff T f n x := by
  have h0 : birkhoffSum T f 0 x ≤ maxBirkhoff T f n x :=
    birkhoffSum_le_maxBirkhoff (Nat.zero_le n) x
  simpa [birkhoffSum_zero] using h0

/-- The maximum is attained at some `k ≤ n`. -/
theorem exists_eq_maxBirkhoff (n : ℕ) (x : α) :
    ∃ k ≤ n, birkhoffSum T f k x = maxBirkhoff T f n x := by
  obtain ⟨k, hk, hkeq⟩ :=
    Finset.exists_mem_eq_sup' (Finset.nonempty_range_iff.mpr n.succ_ne_zero)
      (fun k => birkhoffSum T f k x)
  exact ⟨k, Nat.lt_succ_iff.mp (Finset.mem_range.mp hk), hkeq.symm⟩

/-- `S_k f x ≤ f x + maxBirkhoff T f n (T x)` for `1 ≤ k ≤ n + 1`. -/
theorem birkhoffSum_le_add_maxBirkhoff {n k : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ n + 1) (x : α) :
    birkhoffSum T f k x ≤ f x + maxBirkhoff T f n (T x) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt (Nat.lt_of_lt_of_le Nat.zero_lt_one hk1)
  simp only [Nat.zero_add] at hk2 ⊢
  rw [congrFun (birkhoffSum_succ' T f m) x]
  simp only [Pi.add_apply, Function.comp_apply]
  have hm : m ≤ n := Nat.le_of_succ_le_succ hk2
  have : birkhoffSum T f m (T x) ≤ maxBirkhoff T f n (T x) :=
    birkhoffSum_le_maxBirkhoff hm (T x)
  linarith

/-- Garsia's comparison: where `maxBirkhoff T f n x > 0`, it is at most
`f x + maxBirkhoff T f n (T x)`. -/
theorem maxBirkhoff_le_add_of_pos {n : ℕ} {x : α} (hx : 0 < maxBirkhoff T f n x) :
    maxBirkhoff T f n x ≤ f x + maxBirkhoff T f n (T x) := by
  obtain ⟨k, hk, hkeq⟩ := exists_eq_maxBirkhoff n x
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [birkhoffSum_zero] at hkeq
    exact (lt_irrefl _ (hkeq ▸ hx))
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
  have hk2 : k ≤ n + 1 := Nat.le_succ_of_le hk
  calc maxBirkhoff T f n x = birkhoffSum T f k x := hkeq.symm
    _ ≤ f x + maxBirkhoff T f n (T x) := birkhoffSum_le_add_maxBirkhoff hk1 hk2 x

/-- `S_k (f - a) = S_k f - k a`. See also `StatMech.BirkhoffAE.birkhoffSum_sub_const` (same
statement under a measurable-space assumption). -/
theorem birkhoffSum_sub_const (a : ℝ) (k : ℕ) (x : α) :
    birkhoffSum T (fun y => f y - a) k x = birkhoffSum T f k x - k • a := by
  have hconst : (fun (_ : α) => a) ∘ T = fun (_ : α) => a := rfl
  have hsub := congrFun (congrFun (birkhoffSum_sub T f (fun _ => a)) k) x
  have hgoal : birkhoffSum T (fun y => f y - a) k x
      = birkhoffSum T f k x - birkhoffSum T (fun (_ : α) => a) k x := hsub
  rw [hgoal, birkhoffSum_of_comp_eq hconst]
  rfl

/-- For `n ≥ 1`, `maxBirkhoff T f n x > 0` iff Garsia's maximal sum
`StatMech.GarsiaMax.maxPartialSum T f n hn x = max_{1 ≤ k ≤ n} S_k f x` is positive: the two
maxima differ only by the term `S_0 f = 0`. -/
theorem pos_maxBirkhoff_iff_pos_maxPartialSum {n : ℕ} (hn : 1 ≤ n) (x : α) :
    0 < maxBirkhoff T f n x ↔ 0 < GarsiaMax.maxPartialSum T f n hn x := by
  constructor
  · intro h
    obtain ⟨k, hk, hkeq⟩ := exists_eq_maxBirkhoff n x
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [birkhoffSum_zero] at hkeq
      exact lt_irrefl _ (hkeq ▸ h)
    exact h.trans_le (hkeq ▸ GarsiaMax.birkhoffSum_le_maxPartialSum hn
      (Nat.one_le_iff_ne_zero.mpr hk0) hk x)
  · intro h
    obtain ⟨m, -, hm, hmeq⟩ := GarsiaMax.exists_eq_maxPartialSum hn x
    exact h.trans_le (hmeq ▸ birkhoffSum_le_maxBirkhoff hm x)

section MeasureTheory

variable [MeasurableSpace α] {μ : Measure α}

/-- `f ∘ T^[k]` is integrable for measure-preserving `T` and integrable `f`. -/
theorem integrable_comp_iterate (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) (k : ℕ) :
    Integrable (fun x => f (T^[k] x)) μ := by
  rw [← memLp_one_iff_integrable] at hf ⊢
  exact hf.comp_measurePreserving (hT.iterate k)

omit [MeasurableSpace α] in
/-- `maxBirkhoff T f n` as a pointwise supremum of functions. -/
theorem maxBirkhoff_eq_sup'_fun (n : ℕ) :
    (fun x => maxBirkhoff T f n x) =
      (Finset.range (n + 1)).sup' (Finset.nonempty_range_iff.mpr n.succ_ne_zero)
        (fun k => fun x => birkhoffSum T f k x) := by
  funext x
  rw [Finset.sup'_apply]
  rfl

/-- `maxBirkhoff T f n` is integrable. -/
theorem integrable_maxBirkhoff (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) (n : ℕ) :
    Integrable (fun x => maxBirkhoff T f n x) μ := by
  rw [maxBirkhoff_eq_sup'_fun]
  refine Finset.sup'_induction (p := fun g => Integrable g μ) _ _
    (fun _ hg _ hh => hg.sup hh) (fun k _ => ?_)
  exact
    MathlibExt.Probability.BirkhoffErgodicL1.integrable_birkhoffSum_of_measurePreserving hT hf k

/-- `maxBirkhoff T f n ∘ T` is integrable. -/
theorem integrable_maxBirkhoff_comp (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) (n : ℕ) :
    Integrable (fun x => maxBirkhoff T f n (T x)) μ := by
  have hM : Integrable (fun x => maxBirkhoff T f n x) μ := integrable_maxBirkhoff hT hf n
  rw [← memLp_one_iff_integrable] at hM ⊢
  exact hM.comp_measurePreserving hT

/-- `∫ maxBirkhoff T f n ∘ T = ∫ maxBirkhoff T f n` by invariance of `μ`. -/
theorem integral_maxBirkhoff_comp (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) (n : ℕ) :
    ∫ x, maxBirkhoff T f n (T x) ∂μ = ∫ x, maxBirkhoff T f n x ∂μ :=
  Kingman.integral_comp_measurePreserving T hT _
    (integrable_maxBirkhoff hT hf n).aestronglyMeasurable

/-- **Maximal ergodic inequality** (Hopf; Garsia's proof): `0 ≤ ∫_{maxBirkhoff T f n > 0} f dμ`.
See also `StatMech.GarsiaMax.garsia_maximal_inequality` and
`pos_maxBirkhoff_iff_pos_maxPartialSum`. -/
theorem maximal_ergodic_inequality (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) (n : ℕ) :
    0 ≤ ∫ x in {x | 0 < maxBirkhoff T f n x}, f x ∂μ := by
  set M : α → ℝ := fun x => maxBirkhoff T f n x with hM
  set MT : α → ℝ := fun x => maxBirkhoff T f n (T x) with hMT
  set E : Set α := {x | 0 < maxBirkhoff T f n x} with hE
  have hM_int : Integrable M μ := integrable_maxBirkhoff hT hf n
  have hMT_int : Integrable MT μ := integrable_maxBirkhoff_comp hT hf n
  have hMsub_int : Integrable (fun x => M x - MT x) μ := hM_int.sub hMT_int
  have hE_meas : NullMeasurableSet E μ :=
    nullMeasurableSet_lt aemeasurable_const hM_int.aestronglyMeasurable.aemeasurable
  have step1 : ∫ x in E, (M x - MT x) ∂μ ≤ ∫ x in E, f x ∂μ := by
    refine setIntegral_mono_ae_restrict hMsub_int.integrableOn hf.integrableOn ?_
    rw [EventuallyLE, ae_restrict_iff'₀ hE_meas]
    exact Eventually.of_forall fun x hx => by
      have := maxBirkhoff_le_add_of_pos (T := T) (f := f) (n := n) (x := x) hx
      simp only [hM, hMT]; linarith
  have step2 : ∫ x in E, (M x - MT x) ∂μ = (∫ x in E, M x ∂μ) - ∫ x in E, MT x ∂μ :=
    integral_sub hM_int.integrableOn hMT_int.integrableOn
  have hM_off : ∀ x, x ∉ E → M x = 0 := by
    intro x hx
    simp only [hE, Set.mem_ofPred_eq, not_lt] at hx
    exact le_antisymm hx (maxBirkhoff_nonneg n x)
  have step3 : ∫ x in E, M x ∂μ = ∫ x, M x ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hM_off
  have hMT_nonneg : 0 ≤ᵐ[μ] MT :=
    Eventually.of_forall fun x => maxBirkhoff_nonneg n (T x)
  have step4 : ∫ x in E, MT x ∂μ ≤ ∫ x, MT x ∂μ :=
    setIntegral_le_integral hMT_int hMT_nonneg
  have step5 : ∫ x, MT x ∂μ = ∫ x, M x ∂μ := integral_maxBirkhoff_comp hT hf n
  calc (0 : ℝ) = (∫ x, M x ∂μ) - ∫ x, M x ∂μ := by ring
    _ = (∫ x, M x ∂μ) - ∫ x, MT x ∂μ := by rw [step5]
    _ ≤ (∫ x in E, M x ∂μ) - ∫ x in E, MT x ∂μ := by rw [step3]; linarith [step4]
    _ = ∫ x in E, (M x - MT x) ∂μ := step2.symm
    _ ≤ ∫ x in E, f x ∂μ := step1

variable [IsFiniteMeasure μ]

/-- The level set `{x | max_{k ≤ n} S_k (f - a) x > 0}`. -/
def maximalLevelSet (T : α → α) (f : α → ℝ) (a : ℝ) (n : ℕ) : Set α :=
  {x | 0 < maxBirkhoff T (fun y => f y - a) n x}

/-- **Hopf's maximal inequality**: `a μ(E_a) ≤ ∫_{E_a} f dμ` for the maximal level set `E_a`. -/
theorem hopf_maximal_inequality (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) (a : ℝ)
    (n : ℕ) :
    a * (μ (maximalLevelSet T f a n)).toReal ≤ ∫ x in maximalLevelSet T f a n, f x ∂μ := by
  have hfa : Integrable (fun y => f y - a) μ := hf.sub (integrable_const a)
  have hmax : (0 : ℝ) ≤ ∫ x in maximalLevelSet T f a n, (f x - a) ∂μ :=
    maximal_ergodic_inequality hT hfa n
  have hsplit : ∫ x in maximalLevelSet T f a n, (f x - a) ∂μ
      = (∫ x in maximalLevelSet T f a n, f x ∂μ) - a * (μ (maximalLevelSet T f a n)).toReal := by
    rw [integral_sub hf.integrableOn (integrable_const a).integrableOn, setIntegral_const,
      smul_eq_mul, mul_comm, Measure.real]
  rw [hsplit] at hmax
  linarith

end MeasureTheory

end Birkhoff

end StatMech
