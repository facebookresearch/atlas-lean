/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module
public import CSLibExt.MachineLearning.Backpropagation
import MathlibExt.Analysis.Approximation.UniversalApproximation
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Continuous
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Topology.MetricSpace.Basic
/-!
Crosswalk from `Net` layers (S1) to one-hidden-layer sums (S2):
`Net (oneHiddenWidths n m)` matches hidden width `m`.
`layer 0` matches `i` to `σ` of inner plus bias.
`layer 1` matches `h` to the sum of `c i * h i`.
`forward 2 x 0` matches the sum of `c i * σ` of inner plus bias.
`universal_approximation` is existence-only:
it gives no bound on the width `m` and no approximation rate.
-/
@[expose] public section
namespace Cslib.MachineLearning.OneHiddenLayerNet
open Cslib.MachineLearning.Backpropagation
abbrev oneHiddenWidths (n m : ℕ) : ℕ → ℕ
  | 0 => n
  | 1 => m
  | _ => 1
noncomputable def oneHiddenLayerNet (n m : ℕ) (σ : ℝ → ℝ)
    (W : Fin m → EuclideanSpace ℝ (Fin n)) (b c : Fin m → ℝ) :
    Net (oneHiddenWidths n m) where
  layer := fun k => match k with
    | 0 => fun x => WithLp.toLp 2 (fun i => σ (@inner ℝ _ _ (W i) x + b i))
    | 1 => fun h => WithLp.toLp 2 (fun _ : Fin 1 => ∑ i, c i * h i)
    | _n + 2 => fun x => x
theorem forward_oneHiddenLayerNet (n m : ℕ) (σ : ℝ → ℝ)
    (W : Fin m → EuclideanSpace ℝ (Fin n)) (b c : Fin m → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    (oneHiddenLayerNet n m σ W b c).forward 2 x 0 =
      ∑ i, c i * σ (@inner ℝ _ _ (W i) x + b i) := by
  simp only [Net.forward, oneHiddenLayerNet]
theorem universal_approximation_net {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (_hK : IsCompact K) {σ : ℝ → ℝ} (_hσ : Continuous σ)
    (_hnp : ¬ ∃ p : Polynomial ℝ, ∀ x, σ x = p.eval x)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (_hf : ContinuousOn f K)
    {ε : ℝ} (_hε : 0 < ε) :
    ∃ (m : ℕ) (W : Fin m → EuclideanSpace ℝ (Fin n)) (b c : Fin m → ℝ),
      ∀ x ∈ K, |f x - (oneHiddenLayerNet n m σ W b c).forward 2 x 0| < ε := by
  have hS2 := MetaMathlibExt.universal_approximation _hK _hσ _hnp _hf _hε
  cases hS2 with
  | intro m h1 =>
    cases h1 with
    | intro c h2 =>
      cases h2 with
      | intro W h3 =>
        cases h3 with
        | intro b h4 =>
          exact ⟨m, W, b, c, fun x hx => by
            have hxh := h4 x hx
            have hL1 := forward_oneHiddenLayerNet n m σ W b c x
            rw [← hL1] at hxh
            exact hxh⟩
theorem relu_not_polynomial : ¬ ∃ p : Polynomial ℝ, ∀ x : ℝ, max x 0 = p.eval x := by
  intro h
  cases h with
  | intro p hp =>
    have h0 : ∀ x : ℝ, x ≤ 0 → p.eval x = 0 := by
      intro x hx
      have hmax : max x 0 = 0 := max_eq_right hx
      have hpx := hp x
      rw [hmax] at hpx
      exact hpx.symm
    have hmem : ∀ n : ℕ, (Neg.neg ∘ (Nat.cast : ℕ → ℝ)) n ∈ {x | p.IsRoot x} := by
      intro n
      change p.IsRoot ((Neg.neg ∘ (Nat.cast : ℕ → ℝ)) n)
      have hle : (Neg.neg ∘ (Nat.cast : ℕ → ℝ)) n ≤ 0 := by
        change (-(n : ℝ) : ℝ) ≤ 0
        exact neg_nonpos.mpr (Nat.cast_nonneg n)
      exact h0 _ hle
    have hi : Function.Injective (Neg.neg ∘ (Nat.cast : ℕ → ℝ)) :=
      neg_injective (G := ℝ).comp (Nat.cast_injective (R := ℝ))
    have hInf : {x | p.IsRoot x}.Infinite :=
      Set.infinite_of_injective_forall_mem hi hmem
    have hp0 : p = 0 := Polynomial.eq_zero_of_infinite_isRoot p hInf
    have h1 := hp 1
    have hmax1 : max (1 : ℝ) 0 = 1 := max_eq_left (zero_le_one (α := ℝ))
    rw [hmax1, hp0, Polynomial.eval_zero] at h1
    exact one_ne_zero h1
theorem continuous_relu : Continuous fun x : ℝ => max x 0 := by
  exact continuous_id'.max continuous_const
end Cslib.MachineLearning.OneHiddenLayerNet
