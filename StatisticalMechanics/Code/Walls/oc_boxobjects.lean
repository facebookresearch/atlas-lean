/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






































































import Code.FK.RussoDerivative
import Code.FK.FKQ2Sharp
import Code.FK.Comparison
import Code.Inequalities.IncreasingEvent

open scoped BigOperators
open Finset Set
open scoped Classical

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech
namespace Walls

open StatMech.FK

variable {V : Type*} [Fintype V] [DecidableEq V]












noncomputable def oc_theta (Gf : ℕ → SimpleGraph V) [∀ n, DecidableRel (Gf n).Adj]
    (Af : ℕ → Set (ConfigSpace (Sym2 V))) (n : ℕ) (β : ℝ) : ℝ :=
  fkProbOf (Gf n) β 2 (Af n)


noncomputable def oc_S (Gf : ℕ → SimpleGraph V) [∀ n, DecidableRel (Gf n).Adj]
    (Af : ℕ → Set (ConfigSpace (Sym2 V))) (n : ℕ) (β : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, oc_theta Gf Af k β

section Family

variable (Gf : ℕ → SimpleGraph V) [∀ n, DecidableRel (Gf n).Adj]
variable (Af : ℕ → Set (ConfigSpace (Sym2 V)))


theorem oc_theta_eq_fkProbOf (n : ℕ) (β : ℝ) :
    oc_theta Gf Af n β = fkProbOf (Gf n) β 2 (Af n) := rfl




@[simp] theorem oc_S_zero (β : ℝ) : oc_S Gf Af 0 β = 0 := by
  simp [oc_S]


theorem oc_S_succ (n : ℕ) (β : ℝ) :
    oc_S Gf Af (n + 1) β = oc_S Gf Af n β + oc_theta Gf Af n β := by
  simp [oc_S, Finset.sum_range_succ]







theorem oc_theta_nonneg {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (n : ℕ) :
    0 ≤ oc_theta Gf Af n β :=
  fkProbOf_nonneg (Gf n) hβ hβ1 (by norm_num) (Af n)


theorem oc_theta_le_one {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (n : ℕ) :
    oc_theta Gf Af n β ≤ 1 :=
  fkProbOf_le_one (Gf n) hβ hβ1 (by norm_num) (Af n)


theorem oc_theta_mem_Icc {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (n : ℕ) :
    oc_theta Gf Af n β ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨oc_theta_nonneg Gf Af hβ hβ1 n, oc_theta_le_one Gf Af hβ hβ1 n⟩




theorem oc_indicator_idem (n : ℕ) (ω : ConfigSpace (Sym2 V)) :
    ((Af n).indicator (fun _ => (1 : ℝ)) ω) * ((Af n).indicator (fun _ => (1 : ℝ)) ω)
      = (Af n).indicator (fun _ => (1 : ℝ)) ω := by
  rw [Set.indicator_apply]
  split_ifs <;> ring



theorem oc_indicator_zero_or_one (n : ℕ) (ω : ConfigSpace (Sym2 V)) :
    (Af n).indicator (fun _ => (1 : ℝ)) ω = 0
      ∨ (Af n).indicator (fun _ => (1 : ℝ)) ω = 1 := by
  rw [Set.indicator_apply]
  split_ifs
  · right; rfl
  · left; rfl




theorem oc_S_nonneg {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (n : ℕ) :
    0 ≤ oc_S Gf Af n β :=
  Finset.sum_nonneg (fun k _ => oc_theta_nonneg Gf Af hβ hβ1 k)


theorem oc_S_le_card {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (n : ℕ) :
    oc_S Gf Af n β ≤ (n : ℝ) := by
  calc oc_S Gf Af n β
      = ∑ k ∈ Finset.range n, oc_theta Gf Af k β := rfl
    _ ≤ ∑ _k ∈ Finset.range n, (1 : ℝ) :=
        Finset.sum_le_sum (fun k _ => oc_theta_le_one Gf Af hβ hβ1 k)
    _ = (n : ℝ) := by simp












theorem oc_hasDerivAt_theta {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (n : ℕ) :
    HasDerivAt (fun b => oc_theta Gf Af n b)
      ((∑ e ∈ (Gf n).edgeFinset,
          fkCov (Gf n) β 2 ((Af n).indicator (fun _ => (1 : ℝ))) (coord e))
        / (β * (1 - β))) β :=
  hasDerivAt_fkProbOf (Gf n) hβ hβ1 (by norm_num) (Af n)



theorem oc_hasDerivAt_S {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (n : ℕ) :
    HasDerivAt (fun b => oc_S Gf Af n b)
      (∑ k ∈ Finset.range n,
        (∑ e ∈ (Gf k).edgeFinset,
            fkCov (Gf k) β 2 ((Af k).indicator (fun _ => (1 : ℝ))) (coord e))
          / (β * (1 - β))) β := by
  apply HasDerivAt.fun_sum
  intro k _
  exact oc_hasDerivAt_theta Gf Af hβ hβ1 k


theorem oc_differentiableAt_theta {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (n : ℕ) :
    DifferentiableAt ℝ (fun b => oc_theta Gf Af n b) β :=
  (oc_hasDerivAt_theta Gf Af hβ hβ1 n).differentiableAt









theorem oc_theta_mono (hAf : ∀ n, IsIncreasing (Af n)) (n : ℕ)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₂1 : β₂ < 1) (hle : β₁ ≤ β₂) :
    oc_theta Gf Af n β₁ ≤ oc_theta Gf Af n β₂ := by
  have hβ₁1 : β₁ < 1 := lt_of_le_of_lt hle hβ₂1
  have hβ₂ : 0 < β₂ := lt_of_lt_of_le hβ₁ hle
  
  change fkProbOf (Gf n) β₁ 2 (Af n) ≤ fkProbOf (Gf n) β₂ 2 (Af n)
  unfold fkProbOf fkMean
  exact fkProb_stochastically_increasing (Gf n) hβ₁ hβ₁1 hβ₂ hβ₂1 hle (by norm_num)
    (hAf n)



theorem oc_S_mono (hAf : ∀ n, IsIncreasing (Af n)) (n : ℕ)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₂1 : β₂ < 1) (hle : β₁ ≤ β₂) :
    oc_S Gf Af n β₁ ≤ oc_S Gf Af n β₂ :=
  Finset.sum_le_sum (fun k _ => oc_theta_mono Gf Af hAf k hβ₁ hβ₂1 hle)




theorem oc_S_mono_scale {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1) :
    Monotone (fun n => oc_S Gf Af n β) := by
  intro m n hmn
  change oc_S Gf Af m β ≤ oc_S Gf Af n β
  unfold oc_S
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hmn)
    (fun k _ _ => oc_theta_nonneg Gf Af hβ hβ1 k)

end Family














structure oc_BoxFamily where
  
  theta : ℕ → ℝ → ℝ
  
  S : ℕ → ℝ → ℝ
  
  thetaDeriv : ℕ → ℝ → ℝ
  
  theta_nonneg : ∀ {β : ℝ}, 0 < β → β < 1 → ∀ n, 0 ≤ theta n β
  
  theta_le_one : ∀ {β : ℝ}, 0 < β → β < 1 → ∀ n, theta n β ≤ 1
  
  hasDerivAt_theta : ∀ {β : ℝ}, 0 < β → β < 1 → ∀ n,
    HasDerivAt (fun b => theta n b) (thetaDeriv n β) β
  
  theta_mono : ∀ n, ∀ {β₁ β₂ : ℝ}, 0 < β₁ → β₂ < 1 → β₁ ≤ β₂ → theta n β₁ ≤ theta n β₂
  
  S_succ : ∀ n β, S (n + 1) β = S n β + theta n β
  
  S_zero : ∀ β, S 0 β = 0







noncomputable def oc_boxFamily (Gf : ℕ → SimpleGraph V) [∀ n, DecidableRel (Gf n).Adj]
    (Af : ℕ → Set (ConfigSpace (Sym2 V))) (hAf : ∀ n, IsIncreasing (Af n)) :
    oc_BoxFamily where
  theta n β := oc_theta Gf Af n β
  S n β := oc_S Gf Af n β
  thetaDeriv n β :=
    (∑ e ∈ (Gf n).edgeFinset,
        fkCov (Gf n) β 2 ((Af n).indicator (fun _ => (1 : ℝ))) (coord e))
      / (β * (1 - β))
  theta_nonneg := fun {_β} hβ hβ1 n => oc_theta_nonneg Gf Af hβ hβ1 n
  theta_le_one := fun {_β} hβ hβ1 n => oc_theta_le_one Gf Af hβ hβ1 n
  hasDerivAt_theta := fun {_β} hβ hβ1 n => oc_hasDerivAt_theta Gf Af hβ hβ1 n
  theta_mono := fun n {_β₁ _β₂} hβ₁ hβ₂1 hle => oc_theta_mono Gf Af hAf n hβ₁ hβ₂1 hle
  S_succ n β := oc_S_succ Gf Af n β
  S_zero β := oc_S_zero Gf Af β







section Bundle

variable (Gf : ℕ → SimpleGraph V) [∀ n, DecidableRel (Gf n).Adj]
variable (Af : ℕ → Set (ConfigSpace (Sym2 V))) (hAf : ∀ n, IsIncreasing (Af n))


theorem oc_boxFamily_theta (n : ℕ) (β : ℝ) :
    (oc_boxFamily Gf Af hAf).theta n β = oc_theta Gf Af n β := rfl


theorem oc_boxFamily_S (n : ℕ) (β : ℝ) :
    (oc_boxFamily Gf Af hAf).S n β = oc_S Gf Af n β := rfl


theorem oc_boxFamily_S_eq_sum (n : ℕ) (β : ℝ) :
    (oc_boxFamily Gf Af hAf).S n β
      = ∑ k ∈ Finset.range n, (oc_boxFamily Gf Af hAf).theta k β := rfl


theorem oc_boxFamily_theta_mem_Icc {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (n : ℕ) :
    (oc_boxFamily Gf Af hAf).theta n β ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨(oc_boxFamily Gf Af hAf).theta_nonneg hβ hβ1 n,
   (oc_boxFamily Gf Af hAf).theta_le_one hβ hβ1 n⟩


theorem oc_boxFamily_theta_mono (n : ℕ) {β₁ β₂ : ℝ}
    (hβ₁ : 0 < β₁) (hβ₂1 : β₂ < 1) (hle : β₁ ≤ β₂) :
    (oc_boxFamily Gf Af hAf).theta n β₁ ≤ (oc_boxFamily Gf Af hAf).theta n β₂ :=
  (oc_boxFamily Gf Af hAf).theta_mono n hβ₁ hβ₂1 hle

end Bundle

end Walls
end StatMech
