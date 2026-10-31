/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Dynamics.Ergodic.KingmanSigned.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.VectorMeasure.SetIntegral

/-!
# Garsia's maximal ergodic inequality

For a measure-preserving map `T` and an integrable `f`, let `M_N f = max_{1 ≤ n ≤ N} S_n f` be the
maximum of the first `N` Birkhoff sums `S_n f = ∑_{k<n} f ∘ T^k`. The maximal ergodic theorem of
Hopf, in Garsia's finite form, states `∫_{M_N f > 0} f dμ ≥ 0`. Garsia's proof compares `M_N f`
with `f + (M_N f ∘ T)⁺` and uses invariance of the integral.

## Main definitions

* `StatMech.GarsiaMax.maxPartialSum T f N hN`: the maximal Birkhoff sum `max_{1 ≤ n ≤ N} S_n f`.

## Main results

* `StatMech.GarsiaMax.garsia_maximal_inequality`: `0 ≤ ∫_{M_N f > 0} f dμ`.

`MathlibExt.Dynamics.Ergodic.BirkhoffWanted.maximal_ergodic` proves the limiting form
`0 ≤ ∫_{∃ n, S_n f > 0} f dμ` for measurable `f` on a finite measure space; the finite-`N` form
here needs no measurability of `f` and is what the proof of the pointwise ergodic theorem in
`MathlibExt.Dynamics.Ergodic.KingmanSigned.BirkhoffPointwise` uses.

## References

* A. M. Garsia, *A simple proof of E. Hopf's maximal ergodic theorem*, J. Math. Mech. 14
  (1965), 381–382.
-/

@[expose] public section

open MeasureTheory Filter Finset Function
open scoped Topology

namespace StatMech

namespace GarsiaMax

variable {α : Type*} {T : α → α} {f : α → ℝ}

/-- The maximal Birkhoff sum `max_{1 ≤ n ≤ N} ∑_{k<n} f (T^[k] x)` over the first `N` times. -/
noncomputable def maxPartialSum (T : α → α) (f : α → ℝ) (N : ℕ) (hN : 1 ≤ N) (x : α) : ℝ :=
  (Finset.Icc 1 N).sup' (by rw [Finset.nonempty_Icc]; exact hN)
    (fun n => birkhoffSum T f n x)

theorem birkhoffSum_le_maxPartialSum {N : ℕ} (hN : 1 ≤ N) {n : ℕ} (hn1 : 1 ≤ n) (hn2 : n ≤ N)
    (x : α) : birkhoffSum T f n x ≤ maxPartialSum T f N hN x :=
  Finset.le_sup' (fun n => birkhoffSum T f n x) (Finset.mem_Icc.mpr ⟨hn1, hn2⟩)

theorem exists_eq_maxPartialSum {N : ℕ} (hN : 1 ≤ N) (x : α) :
    ∃ n, 1 ≤ n ∧ n ≤ N ∧ birkhoffSum T f n x = maxPartialSum T f N hN x := by
  obtain ⟨n, hn, hneq⟩ :=
    Finset.exists_mem_eq_sup' (s := Finset.Icc 1 N)
      (by rw [Finset.nonempty_Icc]; exact hN) (fun n => birkhoffSum T f n x)
  obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
  exact ⟨n, hn1, hn2, hneq.symm⟩

theorem birkhoffSum_le_add_posPart_maxPartialSum {N : ℕ} (hN : 1 ≤ N) {n : ℕ}
    (hn1 : 1 ≤ n) (hn2 : n ≤ N) (x : α) :
    birkhoffSum T f n x ≤ f x + max (maxPartialSum T f N hN (T x)) 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt (Nat.lt_of_lt_of_le Nat.zero_lt_one hn1)
  simp only [Nat.zero_add] at hn2 ⊢
  rw [congrFun (birkhoffSum_succ' T f m) x, Pi.add_apply, Function.comp_apply]
  have key : birkhoffSum T f m (T x) ≤ max (maxPartialSum T f N hN (T x)) 0 := by
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0
      rw [birkhoffSum_zero]
      exact le_max_right _ _
    · have hmN : m ≤ N := Nat.le_of_succ_le_succ (Nat.le_succ_of_le hn2)
      calc birkhoffSum T f m (T x)
          ≤ maxPartialSum T f N hN (T x) :=
            birkhoffSum_le_maxPartialSum hN hmpos hmN (T x)
        _ ≤ max (maxPartialSum T f N hN (T x)) 0 := le_max_left _ _
  linarith

theorem maxPartialSum_le_add_posPart {N : ℕ} (hN : 1 ≤ N) (x : α) :
    maxPartialSum T f N hN x ≤ f x + max (maxPartialSum T f N hN (T x)) 0 := by
  obtain ⟨n, hn1, hn2, hneq⟩ := exists_eq_maxPartialSum hN x
  calc maxPartialSum T f N hN x = birkhoffSum T f n x := hneq.symm
    _ ≤ f x + max (maxPartialSum T f N hN (T x)) 0 :=
        birkhoffSum_le_add_posPart_maxPartialSum hN hn1 hn2 x

section MeasureTheory

variable [MeasurableSpace α] {μ : Measure α}

omit [MeasurableSpace α] in
theorem maxPartialSum_eq_sup'_fun {N : ℕ} (hN : 1 ≤ N) :
    (fun x => maxPartialSum T f N hN x) =
      (Finset.Icc 1 N).sup' (by rw [Finset.nonempty_Icc]; exact hN)
        (fun n => fun x => birkhoffSum T f n x) := by
  funext x
  rw [Finset.sup'_apply]
  rfl

theorem integrable_maxPartialSum (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) {N : ℕ}
    (hN : 1 ≤ N) : Integrable (fun x => maxPartialSum T f N hN x) μ := by
  rw [maxPartialSum_eq_sup'_fun hN]
  refine Finset.sup'_induction (p := fun g => Integrable g μ) _ _
    (fun _ hg _ hh => hg.sup hh) (fun n _ => ?_)
  exact MathlibExt.Probability.BirkhoffErgodicL1.integrable_birkhoffSum_of_measurePreserving hT hf n

theorem integrable_posPart_maxPartialSum (hT : MeasurePreserving T μ μ) (hf : Integrable f μ)
    {N : ℕ} (hN : 1 ≤ N) :
    Integrable (fun x => max (maxPartialSum T f N hN x) 0) μ :=
  (integrable_maxPartialSum hT hf hN).pos_part

theorem integrable_posPart_maxPartialSum_comp (hT : MeasurePreserving T μ μ)
    (hf : Integrable f μ) {N : ℕ} (hN : 1 ≤ N) :
    Integrable (fun x => max (maxPartialSum T f N hN (T x)) 0) μ := by
  exact hT.integrable_comp_of_integrable (integrable_posPart_maxPartialSum hT hf hN)

theorem integral_posPart_maxPartialSum_comp (hT : MeasurePreserving T μ μ) (hf : Integrable f μ)
    {N : ℕ} (hN : 1 ≤ N) :
    ∫ x, max (maxPartialSum T f N hN (T x)) 0 ∂μ
      = ∫ x, max (maxPartialSum T f N hN x) 0 ∂μ :=
  Kingman.integral_comp_measurePreserving T hT _
    (integrable_posPart_maxPartialSum hT hf hN).aestronglyMeasurable

/-- **Maximal ergodic theorem** (E. Hopf, 1954), in the finite form of A. M. Garsia, *A simple
proof of E. Hopf's maximal ergodic theorem*, 1965: for measure-preserving `T` and integrable `f`,
the integral of `f` over `{max_{1 ≤ n ≤ N} S_n f > 0}` is nonnegative. See also
`MathlibExt.Dynamics.Ergodic.BirkhoffWanted.maximal_ergodic`, the limiting form for measurable
`f`. -/
theorem garsia_maximal_inequality (hT : MeasurePreserving T μ μ) (hf : Integrable f μ)
    {N : ℕ} (hN : 1 ≤ N) :
    0 ≤ ∫ x in {x | 0 < maxPartialSum T f N hN x}, f x ∂μ := by
  set Mp : α → ℝ := fun x => max (maxPartialSum T f N hN x) 0 with hMp
  set MpT : α → ℝ := fun x => max (maxPartialSum T f N hN (T x)) 0 with hMpT
  set E : Set α := {x | 0 < maxPartialSum T f N hN x} with hE
  have hMp_int : Integrable Mp μ := integrable_posPart_maxPartialSum hT hf hN
  have hMpT_int : Integrable MpT μ := integrable_posPart_maxPartialSum_comp hT hf hN
  have hMsub_int : Integrable (fun x => Mp x - MpT x) μ := hMp_int.sub hMpT_int
  have hM_int : Integrable (fun x => maxPartialSum T f N hN x) μ :=
    integrable_maxPartialSum hT hf hN
  have hE_meas : NullMeasurableSet E μ :=
    nullMeasurableSet_lt aemeasurable_const hM_int.aestronglyMeasurable.aemeasurable
  have step1 : ∫ x in E, (Mp x - MpT x) ∂μ ≤ ∫ x in E, f x ∂μ := by
    refine setIntegral_mono_ae_restrict hMsub_int.integrableOn hf.integrableOn ?_
    rw [EventuallyLE, ae_restrict_iff'₀ hE_meas]
    refine Eventually.of_forall fun x hx => ?_
    have hkey := maxPartialSum_le_add_posPart (T := T) (f := f) (N := N) hN x
    have hxpos : (0 : ℝ) < maxPartialSum T f N hN x := hx
    have hMp_x : Mp x = maxPartialSum T f N hN x := by
      simp only [hMp]; exact max_eq_left (le_of_lt hxpos)
    simp only [hMp, hMpT] at *
    rw [hMp_x]; linarith
  have step2 : ∫ x in E, (Mp x - MpT x) ∂μ = (∫ x in E, Mp x ∂μ) - ∫ x in E, MpT x ∂μ :=
    integral_sub hMp_int.integrableOn hMpT_int.integrableOn
  have hMp_off : ∀ x, x ∉ E → Mp x = 0 := by
    intro x hx
    simp only [hE, Set.mem_ofPred_eq, not_lt] at hx
    simp only [hMp]; exact max_eq_right hx
  have step3 : ∫ x in E, Mp x ∂μ = ∫ x, Mp x ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hMp_off
  have hMpT_nonneg : 0 ≤ᵐ[μ] MpT :=
    Eventually.of_forall fun x => le_max_right _ _
  have step4 : ∫ x in E, MpT x ∂μ ≤ ∫ x, MpT x ∂μ :=
    setIntegral_le_integral hMpT_int hMpT_nonneg
  have step5 : ∫ x, MpT x ∂μ = ∫ x, Mp x ∂μ := integral_posPart_maxPartialSum_comp hT hf hN
  calc (0 : ℝ) = (∫ x, Mp x ∂μ) - ∫ x, Mp x ∂μ := by ring
    _ = (∫ x, Mp x ∂μ) - ∫ x, MpT x ∂μ := by rw [step5]
    _ ≤ (∫ x in E, Mp x ∂μ) - ∫ x in E, MpT x ∂μ := by rw [step3]; linarith [step4]
    _ = ∫ x in E, (Mp x - MpT x) ∂μ := step2.symm
    _ ≤ ∫ x in E, f x ∂μ := step1

end MeasureTheory

end GarsiaMax

end StatMech
