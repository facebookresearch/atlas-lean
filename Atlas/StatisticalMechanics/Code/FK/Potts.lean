/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

























import Mathlib

open scoped BigOperators

namespace StatMech

namespace Potts

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]






def monoIndicator {q : ℕ} (σ : V → Fin q) : Sym2 V → ℝ :=
  Sym2.lift ⟨fun x y => if σ x = σ y then (1 : ℝ) else 0, by
    intro a b
    dsimp only
    by_cases h : σ a = σ b
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun he : σ b = σ a => h he.symm)]⟩

omit [Fintype V] [DecidableEq V] in
@[simp]
theorem monoIndicator_mk {q : ℕ} (σ : V → Fin q) (x y : V) :
    monoIndicator σ (s(x, y)) = if σ x = σ y then (1 : ℝ) else 0 :=
  Sym2.lift_mk _ _ _

omit [Fintype V] [DecidableEq V] in
theorem monoIndicator_nonneg {q : ℕ} (σ : V → Fin q) (e : Sym2 V) :
    0 ≤ monoIndicator σ e := by
  induction e with
  | _ x y => rw [monoIndicator_mk]; split <;> norm_num



def agreement {q : ℕ} (σ : V → Fin q) : ℝ :=
  ∑ e ∈ G.edgeFinset, monoIndicator σ e

omit [DecidableEq V] in
theorem agreement_nonneg {q : ℕ} (σ : V → Fin q) : 0 ≤ agreement G σ :=
  Finset.sum_nonneg fun e _ => monoIndicator_nonneg σ e



noncomputable def pottsWeight {q : ℕ} (β J : ℝ) (σ : V → Fin q) : ℝ :=
  Real.exp (β * J * agreement G σ)

omit [DecidableEq V] in
theorem pottsWeight_pos {q : ℕ} (β J : ℝ) (σ : V → Fin q) : 0 < pottsWeight G β J σ :=
  Real.exp_pos _

omit [DecidableEq V] in
theorem pottsWeight_nonneg {q : ℕ} (β J : ℝ) (σ : V → Fin q) : 0 ≤ pottsWeight G β J σ :=
  (pottsWeight_pos G β J σ).le


noncomputable def pottsZ (q : ℕ) (β J : ℝ) : ℝ :=
  ∑ σ : V → Fin q, pottsWeight G β J σ





theorem pottsZ_pos (q : ℕ) [NeZero q] (β J : ℝ) : 0 < pottsZ G q β J :=
  Finset.sum_pos (fun σ _ => pottsWeight_pos G β J σ) Finset.univ_nonempty

theorem pottsZ_ne_zero (q : ℕ) [NeZero q] (β J : ℝ) : pottsZ G q β J ≠ 0 :=
  (pottsZ_pos G q β J).ne'


noncomputable def pottsProb (q : ℕ) (β J : ℝ) (σ : V → Fin q) : ℝ :=
  pottsWeight G β J σ / pottsZ G q β J


theorem pottsProb_nonneg (q : ℕ) [NeZero q] (β J : ℝ) (σ : V → Fin q) :
    0 ≤ pottsProb G q β J σ :=
  div_nonneg (pottsWeight_nonneg G β J σ) (pottsZ_pos G q β J).le


theorem pottsProb_pos (q : ℕ) [NeZero q] (β J : ℝ) (σ : V → Fin q) :
    0 < pottsProb G q β J σ :=
  div_pos (pottsWeight_pos G β J σ) (pottsZ_pos G q β J)


theorem pottsProb_sum_eq_one (q : ℕ) [NeZero q] (β J : ℝ) :
    ∑ σ : V → Fin q, pottsProb G q β J σ = 1 := by
  unfold pottsProb
  rw [← Finset.sum_div]
  exact div_self (pottsZ_ne_zero G q β J)




noncomputable def pottsPMF (q : ℕ) [NeZero q] (β J : ℝ) : PMF (V → Fin q) :=
  PMF.ofFintype (fun σ => ENNReal.ofReal (pottsProb G q β J σ)) <| by
    rw [← ENNReal.ofReal_sum_of_nonneg fun σ _ => pottsProb_nonneg G q β J σ,
      pottsProb_sum_eq_one]
    simp

@[simp]
theorem pottsPMF_apply (q : ℕ) [NeZero q] (β J : ℝ) (σ : V → Fin q) :
    pottsPMF G q β J σ = ENNReal.ofReal (pottsProb G q β J σ) :=
  PMF.ofFintype_apply _ _

end Potts

end StatMech
