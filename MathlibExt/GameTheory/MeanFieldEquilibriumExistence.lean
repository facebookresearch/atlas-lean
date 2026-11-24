/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.MeanFieldEquilibrium
import MathlibExt.Analysis.Convex.KKM

/-!
# Existence of mean field equilibria

`exists_isMeanFieldEquilibrium` gives an equilibrium on a finite nonempty state space when
the cost of each state is Lipschitz in the population distribution. The proof applies the
Knaster–Kuratowski–Mazurkiewicz lemma to the sets of distributions at which a given state's
cost is at least the cost of every state in the support.
-/

@[expose] public section

namespace MathlibExt.GameTheory.MeanFieldEquilibriumWanted

open MathlibExt.GameTheory.MeanFieldEquilibrium
open Convexity

/-- A continuous cost on a simplex admits a distribution supported on cost minimizers. -/
private theorem exists_supported_on_minimizers {n : ℕ}
    (cost : StdSimplex ℝ (Fin (n + 1)) → Fin (n + 1) → ℝ)
    (hc : ∀ i, Continuous fun x => cost x i) :
    ∃ x : StdSimplex ℝ (Fin (n + 1)), ∀ j, x.weights j ≠ 0 → ∀ i, cost x j ≤ cost x i := by
  classical
  let C (i : Fin (n + 1)) : Set (StdSimplex ℝ (Fin (n + 1))) :=
    ⋂ j, {x | x.weights j = 0} ∪ {x | cost x j ≤ cost x i}
  have hclosed i : IsClosed (C i) := isClosed_iInter fun j =>
    (isClosed_eq (StdSimplex.continuous_weights_apply ℝ j) continuous_const).union
      (isClosed_le (hc j) (hc i))
  have hcover (x : StdSimplex ℝ (Fin (n + 1))) : ∃ i, 0 < x.weights i ∧ x ∈ C i := by
    obtain ⟨i, hi, hmax⟩ := x.weights.support.exists_max_image (cost x) x.support_weights_nonempty
    refine ⟨i, lt_of_le_of_ne (x.nonneg i) (Finsupp.mem_support_iff.mp hi).symm, ?_⟩
    exact Set.mem_iInter.mpr fun j => or_iff_not_imp_left.mpr fun hj =>
      hmax j (Finsupp.mem_support_iff.mpr hj)
  obtain ⟨x, hx⟩ := MathlibExt.Analysis.Convex.KKM.kkm_lemma C hclosed hcover
  exact ⟨x, fun j hj i => (Set.mem_iInter.mp (hx i) j).resolve_left hj⟩

/-- **Existence of mean field equilibria** (Lasry–Lions; Cardaliaguet, *Notes on Mean Field
Games*, Theorem 2.7 and Remark 2.8, for a finite state space `Q`). If `Q` is a nonempty finite
set and the cost is Lipschitz in the population distribution, `|F m₁ y - F m₂ y| ≤ K ∑ |m₁ - m₂|`
for probability vectors `m₁, m₂` (on a finite set the Kantorovich–Rubinstein distance `d₁` of the
source is equivalent to the `ℓ¹` distance), then a mean field equilibrium exists. -/
theorem exists_isMeanFieldEquilibrium {Q : Type*} [Fintype Q] [Nonempty Q]
    (F : (Q → ℝ) → Q → ℝ) (K : ℝ)
    (hF : ∀ m₁ m₂ : Q → ℝ, ((∀ y, 0 ≤ m₁ y) ∧ ∑ y, m₁ y = 1) →
      ((∀ y, 0 ≤ m₂ y) ∧ ∑ y, m₂ y = 1) → ∀ y, |F m₁ y - F m₂ y| ≤ K * ∑ z, |m₁ z - m₂ z|) :
    ∃ m : Q → ℝ, IsMeanFieldEquilibrium F m := by
  classical
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero (α := Q))
  let e : Q ≃ Fin (n + 1) := Fintype.equivFinOfCardEq hn
  let m (x : StdSimplex ℝ (Fin (n + 1))) (y : Q) := x.weights (e y)
  have hprob x : (∀ y, 0 ≤ m x y) ∧ ∑ y, m x y = 1 :=
    ⟨fun y => x.nonneg (e y), (e.sum_comp x.weights).trans x.total_of_fintype⟩
  have hm y : Continuous (fun x => m x y) := StdSimplex.continuous_weights_apply ℝ (e y)
  have hc y : Continuous (fun x => F (m x) y) := by
    refine continuous_iff_continuousAt.mpr fun x => tendsto_iff_dist_tendsto_zero.mpr ?_
    simp only [Real.dist_eq]
    refine squeeze_zero (fun _ => abs_nonneg _) (fun x' => hF _ _ (hprob x') (hprob x) y) ?_
    have h : Continuous (fun x' => K * ∑ z, |m x' z - m x z|) :=
      continuous_const.mul (continuous_finsetSum _ fun z _ => ((hm z).sub continuous_const).abs)
    simpa using h.continuousAt.tendsto (x := x)
  obtain ⟨x, hx⟩ := exists_supported_on_minimizers
    (fun x i => F (m x) (e.symm i)) (fun i => hc (e.symm i))
  refine ⟨m x, isMeanFieldEquilibrium_iff.mpr ⟨hprob x, fun y hy z => ?_⟩⟩
  simpa using hx (e y) hy (e z)

end MathlibExt.GameTheory.MeanFieldEquilibriumWanted
