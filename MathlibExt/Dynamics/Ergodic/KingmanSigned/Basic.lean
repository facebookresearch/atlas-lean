/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Subadditive
public import MathlibExt.Probability.BirkhoffErgodicL1

/-!
# Subadditive cocycles

A sequence `X n : α → ℝ` of integrable functions is a subadditive cocycle over a measure-preserving
map `T` if `X (m + n) ≤ X m + X n ∘ T^m` almost everywhere. Integrating, the expectations
`expSeq n = ∫ X n dμ` form a subadditive sequence, so by Fekete's lemma (`Subadditive.lim`)
`expSeq n / n` converges to its infimum `gamma`, the time constant. This is the setting of
Kingman's subadditive ergodic theorem, proved in `MathlibExt.Dynamics.Ergodic.KingmanSigned`.

## Main definitions

* `StatMech.Kingman.SubadditiveCocycle T μ X`: `X` is an integrable subadditive cocycle over `T`.
* `StatMech.Kingman.SubadditiveCocycle.expSeq X μ n`: the expectation `∫ X n dμ`.
* `StatMech.Kingman.SubadditiveCocycle.gamma h`: the time constant `lim expSeq n / n`.

## Main results

* `StatMech.Kingman.integral_comp_iterate`: `∫ g ∘ T^m dμ = ∫ g dμ` for measure-preserving `T`.
* `StatMech.Kingman.SubadditiveCocycle.subadditive_expSeq`: the expectations are subadditive.
* `StatMech.Kingman.SubadditiveCocycle.tendsto_expSeq_div`: `expSeq n / n → gamma` (Fekete).
* `StatMech.Kingman.SubadditiveCocycle.ae_le_birkhoffSum`: `X n ≤ ∑_{k<n} X 1 ∘ T^k` a.e.

## References

* J. F. C. Kingman, *The ergodic theory of subadditive stochastic processes*, J. Roy. Statist.
  Soc. Ser. B 30 (1968), 499–510.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace StatMech

namespace Kingman

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- The integral is invariant under a measure-preserving map: `∫ g ∘ T dμ = ∫ g dμ` for
a.e.-strongly measurable `g`. -/
theorem integral_comp_measurePreserving (T : α → α) (hT : MeasurePreserving T μ μ)
    (g : α → ℝ) (hg : AEStronglyMeasurable g μ) :
    ∫ x, g (T x) ∂μ = ∫ x, g x ∂μ := by
  rw [← hT.map_eq] at hg ⊢
  rw [integral_map hT.aemeasurable hg, hT.map_eq]

/-- The integral is invariant under iterates of a measure-preserving map:
`∫ g ∘ T^[m] dμ = ∫ g dμ` for a.e.-strongly measurable `g`. See also
`MathlibExt.Probability.BirkhoffErgodicL1.integral_comp_iterate_of_measurePreserving`, which
assumes `g` integrable. -/
theorem integral_comp_iterate (T : α → α) (hT : MeasurePreserving T μ μ)
    (g : α → ℝ) (hg : AEStronglyMeasurable g μ) (m : ℕ) :
    ∫ x, g (T^[m] x) ∂μ = ∫ x, g x ∂μ := by
  rw [← (hT.iterate m).map_eq] at hg ⊢
  rw [integral_map (hT.iterate m).aemeasurable hg, (hT.iterate m).map_eq]

/-- `X` is a subadditive cocycle over `T`: `T` preserves `μ`, every `X n` is integrable, and
`X (m + n) ≤ X m + X n ∘ T^[m]` almost everywhere. -/
structure SubadditiveCocycle (T : α → α) (μ : Measure α) (X : ℕ → α → ℝ) : Prop where
  /-- `T` preserves `μ`. -/
  measurePreserving : MeasurePreserving T μ μ
  /-- Every `X n` is integrable. -/
  integrable : ∀ n, Integrable (X n) μ
  /-- The cocycle inequality, almost everywhere. -/
  subadditive : ∀ m n, ∀ᵐ x ∂μ, X (m + n) x ≤ X m x + X n (T^[m] x)

namespace SubadditiveCocycle

variable {T : α → α} {X : ℕ → α → ℝ}

/-- The expectation `∫ X n dμ` of the `n`-th term. -/
noncomputable def expSeq (X : ℕ → α → ℝ) (μ : Measure α) (n : ℕ) : ℝ := ∫ x, X n x ∂μ

/-- The expectations of a subadditive cocycle are subadditive. -/
theorem expSeq_subadditive (h : SubadditiveCocycle T μ X) (m n : ℕ) :
    expSeq X μ (m + n) ≤ expSeq X μ m + expSeq X μ n := by
  have hint : ∫ x, X (m + n) x ∂μ ≤ ∫ x, (X m x + X n (T^[m] x)) ∂μ := by
    refine integral_mono_ae (h.integrable (m + n)) ?_ (h.subadditive m n)
    exact (h.integrable m).add
      ((h.measurePreserving.iterate m).integrable_comp_of_integrable (h.integrable n))
  calc expSeq X μ (m + n) = ∫ x, X (m + n) x ∂μ := rfl
    _ ≤ ∫ x, (X m x + X n (T^[m] x)) ∂μ := hint
    _ = (∫ x, X m x ∂μ) + ∫ x, X n (T^[m] x) ∂μ := by
        rw [integral_add (h.integrable m)]
        exact (h.measurePreserving.iterate m).integrable_comp_of_integrable (h.integrable n)
    _ = expSeq X μ m + expSeq X μ n := by
        rw [integral_comp_iterate T h.measurePreserving (X n)
          (h.integrable n).aestronglyMeasurable]
        rfl

/-- The expectations of a subadditive cocycle form a `Subadditive` sequence. -/
theorem subadditive_expSeq (h : SubadditiveCocycle T μ X) :
    Subadditive (expSeq X μ) := h.expSeq_subadditive

/-- Iterating subadditivity: `X n ≤ ∑_{k<n} X 1 ∘ T^[k]` almost everywhere, for all `n ≥ 1`. -/
theorem ae_le_birkhoffSum (h : SubadditiveCocycle T μ X) :
    ∀ᵐ x ∂μ, ∀ n, 1 ≤ n → X n x ≤ birkhoffSum T (X 1) n x := by
  have hstep : ∀ᵐ x ∂μ, ∀ n, X (n + 1) x ≤ X n x + X 1 (T^[n] x) := by
    rw [ae_all_iff]
    intro n
    exact h.subadditive n 1
  filter_upwards [hstep] with x hx
  intro n hn
  induction n with
  | zero => exact absurd hn (by norm_num)
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp [birkhoffSum_one]
    · calc X (k + 1) x ≤ X k x + X 1 (T^[k] x) := hx k
        _ ≤ birkhoffSum T (X 1) k x + X 1 (T^[k] x) := by gcongr; exact ih hk
        _ = birkhoffSum T (X 1) (k + 1) x := (congrFun (birkhoffSum_succ T (X 1) k) x).symm

/-- `∫ X n dμ ≤ n ∫ X 1 dμ` for `n ≥ 1`. -/
theorem expSeq_le_nsmul (h : SubadditiveCocycle T μ X) {n : ℕ} (hn : 1 ≤ n) :
    expSeq X μ n ≤ n • expSeq X μ 1 := by
  calc expSeq X μ n = ∫ x, X n x ∂μ := rfl
    _ ≤ ∫ x, birkhoffSum T (X 1) n x ∂μ := by
        refine integral_mono_ae (h.integrable n)
          (MathlibExt.Probability.BirkhoffErgodicL1.integrable_birkhoffSum_of_measurePreserving
            h.measurePreserving (h.integrable 1) n) ?_
        filter_upwards [h.ae_le_birkhoffSum] with x hx using hx n hn
    _ = ∑ i ∈ Finset.range n, ∫ x, X 1 (T^[i] x) ∂μ := by
        simp only [birkhoffSum]
        rw [integral_finsetSum]
        intro i _
        exact (h.measurePreserving.iterate i).integrable_comp_of_integrable (h.integrable 1)
    _ = ∑ _i ∈ Finset.range n, expSeq X μ 1 := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [integral_comp_iterate T h.measurePreserving (X 1)
          (h.integrable 1).aestronglyMeasurable]
        rfl
    _ = n • expSeq X μ 1 := by rw [Finset.sum_const, Finset.card_range]

/-- The time constant `lim_n (∫ X n dμ) / n = inf_n (∫ X n dμ) / n` (Fekete's lemma); it is
meaningful when `expSeq n / n` is bounded below. -/
noncomputable def gamma (h : SubadditiveCocycle T μ X) : ℝ :=
  (subadditive_expSeq h).lim

/-- Fekete's lemma for the expectations: `expSeq n / n → gamma` when bounded below. -/
theorem tendsto_expSeq_div (h : SubadditiveCocycle T μ X)
    (hbdd : BddBelow (Set.range fun n => expSeq X μ n / n)) :
    Tendsto (fun n => expSeq X μ n / n) atTop (𝓝 (gamma h)) :=
  (subadditive_expSeq h).tendsto_lim hbdd

/-- `gamma ≤ expSeq n / n` for every `n ≠ 0`. -/
theorem gamma_le_div (h : SubadditiveCocycle T μ X)
    (hbdd : BddBelow (Set.range fun n => expSeq X μ n / n)) {n : ℕ} (hn : n ≠ 0) :
    gamma h ≤ expSeq X μ n / n :=
  (subadditive_expSeq h).lim_le_div hbdd hn

/-- `gamma ≤ ∫ X 1 dμ`. -/
theorem gamma_le_expSeq_one (h : SubadditiveCocycle T μ X)
    (hbdd : BddBelow (Set.range fun n => expSeq X μ n / n)) :
    gamma h ≤ expSeq X μ 1 := by
  refine le_trans (gamma_le_div h hbdd (n := 1) one_ne_zero) ?_
  simp

/-- For a nonnegative cocycle, `expSeq n / n` is bounded below by `0`. -/
theorem bddBelow_of_nonneg (_h : SubadditiveCocycle T μ X)
    (hnn : ∀ n, 0 ≤ᵐ[μ] X n) :
    BddBelow (Set.range fun n => expSeq X μ n / n) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨n, rfl⟩
  have hX : 0 ≤ expSeq X μ n := integral_nonneg_of_ae (hnn n)
  positivity

end SubadditiveCocycle

end Kingman

end StatMech
