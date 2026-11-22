/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Martingale.OptionalStopping
public import Mathlib.Probability.Process.Stopping
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator

/-!
# Bounded optional stopping, conditional form

For a submartingale `f` and stopping times `L ≤ M` with `M` bounded, the
stopped value at the earlier time is almost surely at most the conditional
expectation of the stopped value at the later time given the σ-algebra
`ℱ_L` of the earlier stopping time:
`stoppedValue f L ≤ᵐ[μ] μ[stoppedValue f M | ℱ_L]`.

## Source

This formalizes the conditional half of the target
"Theorem (General form of optional stopping)" / `general_optional_stopping_bounded`
(Lecture 29, General optional stopping theorem section) of
`v1/Atlas/TheoryOfProbability/targets.yaml`: "If `L ≤ M` are stopping times
and `Y_{M ∧ n}` is a uniformly integrable submartingale, then
`EY_L ≤ EY_M` and `Y_L ≤ E(Y_M | ℱ_L)`." Its v1 formalization is
`v1/Atlas/TheoryOfProbability/code/GeneralOptionalStopping.lean`
(`general_optional_stopping_bounded`), where the statement is proved in full
for bounded `M`.

Only the conditional inequality is ported here, because the expectation
inequality `E[Y_L] ≤ E[Y_M]` is already in Mathlib as
`Submartingale.expected_stoppedValue_mono`, and the unbounded /
uniformly-integrable version (`general_optional_stopping` in v1) is left
unproved there and is not claimed here.

The conditional inequality is the part Mathlib does not have: Mathlib's
optional-sampling results (`stoppedValue_ae_eq_condExp_of_le` and friends)
give an *equality* for martingales, and `Submartingale.ae_le_condExp` gives
the inequality only for deterministic times. The proof below is the v1 proof
of the bounded theorem's second conjunct: reduce to deterministic times on
each set `{L = k}` by identifying the conditional expectation given `ℱ_L`
with the one given `ℱ_k` on that set.

## Main results

* `MeasureTheory.Submartingale.stoppedValue_le_condExp_stoppedValue`:
  for a submartingale `f` and stopping times `L ≤ M` with `M` bounded,
  `stoppedValue f L ≤ᵐ[μ] μ[stoppedValue f M | ℱ_L]`.
* `MeasureTheory.Supermartingale.condExp_stoppedValue_le_stoppedValue`:
  the dual inequality for supermartingales.
-/

@[expose] public section

open MeasureTheory Filter

namespace MeasureTheory

/-- Helper lemma: for any extended natural `a : ℕ∞` that is not `⊤`, coercing
`a.untopA : ℕ` back into `ℕ∞` recovers `a`. -/
private lemma coe_untopA_eq (a : ℕ∞) (ha : a ≠ ⊤) : (↑(a.untopA) : ℕ∞) = a := by
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp ha
  rw [← hn]
  simp only [WithTop.untopA, WithTop.untopD, WithTop.recTopCoe]
  rfl

/-- **Bounded optional stopping, conditional form.** If `f` is a submartingale
and `L ≤ M` are stopping times with `M` bounded above by a finite `N`, then
the stopped value at `L` is almost surely at most the conditional expectation
of the stopped value at `M` given the σ-algebra `ℱ_L` of the earlier stopping
time. -/
theorem Submartingale.stoppedValue_le_condExp_stoppedValue
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    {ℱ : Filtration ℕ m0}
    [SigmaFiniteFiltration μ ℱ]
    {f : ℕ → Ω → ℝ}
    {L M : Ω → ℕ∞}
    (hsub : Submartingale f ℱ μ)
    (hL : IsStoppingTime ℱ L)
    (hM : IsStoppingTime ℱ M)
    (hLM : L ≤ M)
    {N : ℕ} (hbdd : ∀ ω, M ω ≤ N)
    [SigmaFinite (μ.trim hL.measurableSpace_le)] :
    stoppedValue f L ≤ᵐ[μ] μ[stoppedValue f M | hL.measurableSpace] := by
  have h_sp_sub : Submartingale (stoppedProcess f M) ℱ μ := hsub.stoppedProcess hM
  have hL_bdd : ∀ ω, L ω ≤ N := fun ω => (hLM ω).trans (hbdd ω)
  have hL_ne_top : ∀ ω, L ω ≠ ⊤ := fun ω =>
    ne_top_of_le_ne_top (ne_top_of_le_ne_top (by simp) (hbdd ω)) (hLM ω)
  have h_sp_N : stoppedProcess f M N = stoppedValue f M := by
    funext ω
    exact stoppedProcess_eq_of_ge (hbdd ω)
  have h_key : ∀ᵐ ω ∂μ, ∀ k : ℕ, L ω = ↑k →
      stoppedProcess f M k ω ≤
        (μ[stoppedValue f M | hL.measurableSpace]) ω := by
    rw [ae_all_iff]
    intro k
    by_cases hkN : k ≤ N
    · have h_ineq_k : stoppedProcess f M k ≤ᵐ[μ] μ[stoppedValue f M | ℱ k] := by
        have := h_sp_sub.ae_le_condExp hkN
        rwa [h_sp_N] at this
      have h_ce_restrict :
          μ[stoppedValue f M | hL.measurableSpace]
            =ᵐ[μ.restrict {ω | L ω = ↑k}]
            μ[stoppedValue f M | ℱ k] :=
        condExp_ae_eq_restrict_of_measurableSpace_eq_on
          hL.measurableSpace_le (ℱ.le k) (hL.measurableSet_eq' k)
          (fun t => by rw [Set.inter_comm]; exact hL.measurableSet_inter_eq_iff t k)
      have h_restrict := (ae_restrict_iff'
        (ℱ.le _ _ (hL.measurableSet_eq k))).mp h_ce_restrict
      filter_upwards [h_restrict, h_ineq_k] with ω hω_ce hω_ineq hLk
      calc stoppedProcess f M k ω
          ≤ (μ[stoppedValue f M | ℱ k]) ω := hω_ineq
        _ = (μ[stoppedValue f M | hL.measurableSpace]) ω := (hω_ce hLk).symm
    · have hNk : N < k := Nat.lt_of_not_le hkN
      filter_upwards with ω hLk
      exfalso
      have : L ω ≤ ↑N := hL_bdd ω
      rw [hLk] at this
      exact Nat.not_lt.mpr (mod_cast this) hNk
  filter_upwards [h_key] with ω hω
  have h_sv_eq : stoppedValue f L ω = stoppedProcess f M (L ω).untopA ω := by
    simp only [stoppedValue]
    rw [stoppedProcess_eq_of_le ((coe_untopA_eq _ (hL_ne_top ω)).le.trans (hLM ω))]
  rw [h_sv_eq]
  exact hω _ (coe_untopA_eq _ (hL_ne_top ω)).symm

/-- **Bounded optional stopping, conditional form, supermartingale dual.**
If `f` is a supermartingale and `L ≤ M` are stopping times with `M` bounded,
then the conditional expectation of the stopped value at `M` given `ℱ_L` is
almost surely at most the stopped value at `L`. This follows from the
submartingale version applied to `-f`. -/
theorem Supermartingale.condExp_stoppedValue_le_stoppedValue
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    {ℱ : Filtration ℕ m0}
    [SigmaFiniteFiltration μ ℱ]
    {f : ℕ → Ω → ℝ}
    {L M : Ω → ℕ∞}
    (hsup : Supermartingale f ℱ μ)
    (hL : IsStoppingTime ℱ L)
    (hM : IsStoppingTime ℱ M)
    (hLM : L ≤ M)
    {N : ℕ} (hbdd : ∀ ω, M ω ≤ N)
    [SigmaFinite (μ.trim hL.measurableSpace_le)] :
    μ[stoppedValue f M | hL.measurableSpace] ≤ᵐ[μ] stoppedValue f L := by
  have hle := hsup.neg.stoppedValue_le_condExp_stoppedValue hL hM hLM hbdd
  have hnegL : stoppedValue (-f) L = -stoppedValue f L := by
    ext ω; simp [stoppedValue]
  have hnegM : stoppedValue (-f) M = -stoppedValue f M := by
    ext ω; simp [stoppedValue]
  rw [hnegL, hnegM] at hle
  have hce : μ[-stoppedValue f M | hL.measurableSpace] =ᵐ[μ]
      -μ[stoppedValue f M | hL.measurableSpace] :=
    condExp_neg _ _
  have hle' : -stoppedValue f L ≤ᵐ[μ]
      -μ[stoppedValue f M | hL.measurableSpace] :=
    (Filter.eventuallyLE_congr Filter.EventuallyEq.rfl hce).mp hle
  filter_upwards [hle'] with ω hω
  simp only [Pi.neg_apply] at hω
  exact neg_le_neg_iff.mp hω

end MeasureTheory
