/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/








































































import Mathlib

open MeasureTheory Filter Topology

namespace StatMech

namespace Kingman

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}





theorem integral_comp_measurePreserving (T : α → α) (hT : MeasurePreserving T μ μ)
    (g : α → ℝ) (hg : AEStronglyMeasurable g μ) :
    ∫ x, g (T x) ∂μ = ∫ x, g x ∂μ := by
  rw [← hT.map_eq] at hg ⊢
  rw [integral_map hT.aemeasurable hg, hT.map_eq]


theorem integral_comp_iterate (T : α → α) (hT : MeasurePreserving T μ μ)
    (g : α → ℝ) (hg : AEStronglyMeasurable g μ) (m : ℕ) :
    ∫ x, g (T^[m] x) ∂μ = ∫ x, g x ∂μ := by
  rw [← (hT.iterate m).map_eq] at hg ⊢
  rw [integral_map (hT.iterate m).aemeasurable hg, (hT.iterate m).map_eq]









structure SubadditiveCocycle (T : α → α) (μ : Measure α) (X : ℕ → α → ℝ) : Prop where
  
  measurePreserving : MeasurePreserving T μ μ
  
  integrable : ∀ n, Integrable (X n) μ
  
  subadditive : ∀ m n, ∀ᵐ x ∂μ, X (m + n) x ≤ X m x + X n (T^[m] x)

namespace SubadditiveCocycle

variable {T : α → α} {X : ℕ → α → ℝ}


noncomputable def expSeq (X : ℕ → α → ℝ) (μ : Measure α) (n : ℕ) : ℝ := ∫ x, X n x ∂μ








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


theorem subadditive_expSeq (h : SubadditiveCocycle T μ X) :
    Subadditive (expSeq X μ) := h.expSeq_subadditive











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
        _ = birkhoffSum T (X 1) (k + 1) x := (birkhoffSum_succ T (X 1) k x).symm


theorem integrable_birkhoffSum (h : SubadditiveCocycle T μ X) (n : ℕ) :
    Integrable (fun x => birkhoffSum T (X 1) n x) μ := by
  simp only [birkhoffSum]
  refine integrable_finsetSum _ ?_
  intro i _
  exact (h.measurePreserving.iterate i).integrable_comp_of_integrable (h.integrable 1)



theorem expSeq_le_nsmul (h : SubadditiveCocycle T μ X) {n : ℕ} (hn : 1 ≤ n) :
    expSeq X μ n ≤ n • expSeq X μ 1 := by
  calc expSeq X μ n = ∫ x, X n x ∂μ := rfl
    _ ≤ ∫ x, birkhoffSum T (X 1) n x ∂μ := by
        refine integral_mono_ae (h.integrable n) (h.integrable_birkhoffSum n) ?_
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





noncomputable def gamma (h : SubadditiveCocycle T μ X) : ℝ :=
  (subadditive_expSeq h).lim








theorem tendsto_expSeq_div (h : SubadditiveCocycle T μ X)
    (hbdd : BddBelow (Set.range fun n => expSeq X μ n / n)) :
    Tendsto (fun n => expSeq X μ n / n) atTop (𝓝 (gamma h)) :=
  (subadditive_expSeq h).tendsto_lim hbdd


theorem gamma_le_div (h : SubadditiveCocycle T μ X)
    (hbdd : BddBelow (Set.range fun n => expSeq X μ n / n)) {n : ℕ} (hn : n ≠ 0) :
    gamma h ≤ expSeq X μ n / n :=
  (subadditive_expSeq h).lim_le_div hbdd hn


theorem gamma_le_expSeq_one (h : SubadditiveCocycle T μ X)
    (hbdd : BddBelow (Set.range fun n => expSeq X μ n / n)) :
    gamma h ≤ expSeq X μ 1 := by
  refine le_trans (gamma_le_div h hbdd (n := 1) one_ne_zero) ?_
  simp




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
