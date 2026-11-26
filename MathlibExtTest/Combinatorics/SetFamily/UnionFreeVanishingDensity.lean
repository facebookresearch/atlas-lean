/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SetFamily.UnionFreeVanishingDensity
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Data.Fintype.Powerset

open MathlibExt.Combinatorics.UnionFreeFamiliesErdosProblem447Wanted

-- Two singletons together with their union are not union-free.
example : ¬ IsUnionFree ({{0}, {1}, {0, 1}} : Finset (Finset (Fin 2))) := by
  unfold IsUnionFree
  decide

-- A chain is union-free: the union of two members of a chain is one of them.
example : IsUnionFree ({∅, {0}, {0, 1}, {0, 1, 2}} : Finset (Finset (Fin 3))) := by
  unfold IsUnionFree
  decide

-- The middle layer of the subsets of a four-element set is union-free.
example : IsUnionFree ((Finset.univ : Finset (Finset (Fin 4))).filter (·.card = 2)) := by
  unfold IsUnionFree
  decide

-- Three of the four subsets of a two-element set form a union-free family, so the maximum is
-- at least three.
example : 3 ≤ maxUnionFreeSize 2 := by
  refine le_csSup ⟨Fintype.card (Finset (Fin 2)), ?_⟩ ⟨{∅, {0}, {1}}, ?_, by decide⟩
  · rintro k ⟨F, -, rfl⟩
    exact Finset.card_le_univ F
  · unfold IsUnionFree
    decide

-- The main theorem in ratio form: the density of the largest union-free family tends to zero.
example : Filter.Tendsto (fun n : ℕ => (maxUnionFreeSize n : ℝ) / 2 ^ n) Filter.atTop
    (nhds 0) :=
  maxUnionFreeSizeLittleO_holds.tendsto_div_nhds_zero

-- The main theorem with an explicit constant: for every `ε > 0`, eventually at most `ε 2^n`.
example {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop, (maxUnionFreeSize n : ℝ) ≤ ε * 2 ^ n := by
  filter_upwards [maxUnionFreeSizeLittleO_holds.bound hε] with n hn
  rwa [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)] at hn
