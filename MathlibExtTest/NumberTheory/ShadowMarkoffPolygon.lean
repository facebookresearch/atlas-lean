/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.ShadowMarkoffPolygon

/-! # Tests for the cone of nonnegative shadow Markoff trees -/

open MetaMathlibExt

-- A nonnegative integer dilation, including zero, stays in the cone.
example (n : ℕ) (v : Fin 3 → ℤ) (hv : ∀ s ∈ shadowMarkoffTree v, 0 ≤ s.1 ∧ 0 ≤ s.2) :
    ∀ s ∈ shadowMarkoffTree (fun i => (n : ℤ) * v i), 0 ≤ s.1 ∧ 0 ≤ s.2 := by
  obtain ⟨V, hV⟩ := exists_polygon_shadowMarkoffTree_nonneg_iff
  obtain ⟨t, ht, p, hp, heq⟩ := (hV v).mp hv
  apply (hV _).mpr
  refine ⟨n * t, mul_nonneg (Nat.cast_nonneg _) ht, p, hp, ?_⟩
  funext i
  simpa [Pi.smul_apply, mul_assoc] using congrArg (fun f : Fin 3 → ℚ => n * f i) heq

-- The root (0,1,0) is nonnegative, but the branch 0,1,0,1 has shadow -10.
example :
    let V := exists_polygon_shadowMarkoffTree_nonneg_iff.choose
    ¬ ∃ t : ℚ, 0 ≤ t ∧ ∃ p ∈ convexHull ℚ (V : Set (Fin 3 → ℚ)), ![0, 1, 0] = t • p := by
  have hV := exists_polygon_shadowMarkoffTree_nonneg_iff.choose_spec
  intro V h
  let v : Fin 3 → ℤ := ![0, 1, 0]
  have hv : (fun i => (v i : ℚ)) = ![0, 1, 0] := by
    funext i
    fin_cases i <;> rfl
  have hall := (hV v).mpr (by rw [hv]; exact h)
  let s := shadowMarkoffMutate 1 (shadowMarkoffMutate 0
    (shadowMarkoffMutate 1 (shadowMarkoffMutate 0 (shadowMarkoffRoot v))))
  have hs : s ∈ shadowMarkoffTree v :=
    Or.inr ⟨1, .mutate 1 (.mutate 0 .start (by decide)) (by decide)⟩
  have hneg : s.2 1 = -10 := by
    norm_num [s, v, shadowMarkoffRoot, shadowMarkoffMutate, Function.update,
      Finset.sum_erase_eq_sub, Fin.sum_univ_three]
  exact (by decide : ¬ (0 : ℚ) ≤ -10) (hneg ▸ (hall s hs).2 1)
