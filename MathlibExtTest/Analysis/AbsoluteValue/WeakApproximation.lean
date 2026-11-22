/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.AbsoluteValue.WeakApproximation
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.NumberTheory.Ostrowski

@[expose] public section

-- `exactSource` consumer with the original binders.
example {K : Type*} [Field K] {ι : Type*} [Finite ι]
    {v : ι → AbsoluteValue K ℝ} (hv : ∀ i, (v i).IsNontrivial)
    (hne : Pairwise fun i j => ¬(v i).IsEquiv (v j))
    (a : ι → K) {ε : ℝ} (hε : 0 < ε) : ∃ x : K, ∀ i, v i (x - a i) < ε :=
  AbsoluteValue.exists_forall_sub_lt_of_pairwise_not_isEquiv hv hne a hε

-- Boundary: a single index, where pairwise inequivalence is vacuous.
example (a : Fin 1 → ℚ) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : ℚ, ∀ i, Rat.AbsoluteValue.real (x - a i) < ε :=
  AbsoluteValue.exists_forall_sub_lt_of_pairwise_not_isEquiv (K := ℚ) (ι := Fin 1)
    (v := fun _ => Rat.AbsoluteValue.real)
    (fun _ => ⟨2, by norm_num, by rw [Rat.AbsoluteValue.real_eq_abs]; norm_num⟩)
    (fun i j hij => (hij (Subsingleton.elim i j)).elim) a hε
