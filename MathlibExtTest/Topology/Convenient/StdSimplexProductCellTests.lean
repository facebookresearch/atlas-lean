/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.Topology.Convenient.StdSimplexProductCell

@[expose] public section

/-!
# ProductCell coordinate regression for `n = m = 1`

Direct coordinate checks of the public `shuffleCell` fiber-sum API on the concrete
shuffle with first projection `[0, 1, 1]` and second projection `[0, 0, 1]`, applied to
the uniform `1 / 3` point of `Δ^2`. First-factor fibers are `{0}` / `{1, 2}` and
second-factor fibers are `{0, 1}` / `{2}`, so the expected coordinates are `1 / 3`,
`2 / 3` and `2 / 3`, `1 / 3`. A `Convexity.StdSimplex.map` fiber-sum regression would
break these equalities. Distinctness of the two first-factor coordinates guards against
a constant-map collapse. Each proof uses only the public fiber theorems plus decidable
filter sets; no implementation definition is restated and no injectivity theorem is used.

Reuse map (exact base `0934ed2d8f2fc9a20653f44d5af295d301a48cbe`):
- `shuffleCell_fst_fiber`, `shuffleCell_snd_fiber` (`StdSimplexProductCell.lean`): `reuse`.
- `Fin.sum_univ_three`, `Finset.sum_singleton`, `Finset.sum_pair` (pinned Mathlib): `reuse`.
- Point/filter/`decide` idioms from `StdSimplexMinimalFaceTests` / canonical
  `Convexity.StdSimplex`: `reuse`.
- No `generalize` or `local` entry: this file adds only concrete regression examples.

Nonclaims: no gluing, coverage, range equivalence, `SSet`, `DeltaGenerated`, or
model-category result.
-/

set_option autoImplicit false

noncomputable section

namespace MathlibExtTest.Topology.Convenient.StdSimplexProductCellTests

/-- First projection `[0, 1, 1] : Fin 3 → Fin 2`. -/
private def projA11 : Fin 3 → Fin 2 := fun i => if i = 0 then 0 else 1

/-- Second projection `[0, 0, 1] : Fin 3 → Fin 2`. -/
private def projB11 : Fin 3 → Fin 2 := fun i => if i = 2 then 1 else 0

/-- Concrete `n = m = 1` shuffle with projections `[0, 1, 1]` / `[0, 0, 1]`. -/
private def S11 : ProdSimplexShuffle 1 1 :=
  { projA := projA11
    projB := projB11
    monoA := by decide
    monoB := by decide
    firstA := by decide
    lastA := by decide
    firstB := by decide
    lastB := by decide
    step := by decide }

/-- Uniform `1 / 3` point of `Δ^2`. -/
private noncomputable def sThird : Convexity.StdSimplex ℝ (Fin 3) where
  weights := Finsupp.equivFunOnFinite.symm (fun _ => (1 / 3 : ℝ))
  nonneg m := by
    have h : (0 : ℝ) ≤ 1 / 3 := by norm_num
    exact h
  total := by
    have h : (∑ _ : Fin 3, (1 / 3 : ℝ)) = 1 := by
      rw [Fin.sum_univ_three]
      norm_num
    rwa [Finsupp.sum_fintype _ _ (fun _ => rfl)]

/-- Unfolding equation for the uniform-point coordinates. -/
@[simp] private theorem sThird_val (i : Fin 3) : sThird.weights i = (1 / 3 : ℝ) :=
  rfl

/-- First-factor coordinate at `0`: fiber `{0}`, so the value is `1 / 3`. -/
private theorem fst_zero :
    (shuffleCell S11 sThird).1.weights 0 = 1 / 3 := by
  have h := shuffleCell_fst_fiber S11 sThird 0
  have hfilter : Finset.univ.filter (fun k : Fin 3 => S11.projA k = 0) = {0} := by
    decide
  rw [h, hfilter, Finset.sum_singleton]
  exact sThird_val _

/-- First-factor coordinate at `1`: fiber `{1, 2}`, so the value is `2 / 3`. -/
private theorem fst_one :
    (shuffleCell S11 sThird).1.weights 1 = 2 / 3 := by
  have h := shuffleCell_fst_fiber S11 sThird 1
  have hfilter : Finset.univ.filter (fun k : Fin 3 => S11.projA k = 1) = {1, 2} := by
    decide
  rw [h, hfilter, Finset.sum_pair (by decide : (1 : Fin 3) ≠ 2)]
  show (1 / 3 : ℝ) + 1 / 3 = 2 / 3
  norm_num

/-- Second-factor coordinate at `0`: fiber `{0, 1}`, so the value is `2 / 3`. -/
private theorem snd_zero :
    (shuffleCell S11 sThird).2.weights 0 = 2 / 3 := by
  have h := shuffleCell_snd_fiber S11 sThird 0
  have hfilter : Finset.univ.filter (fun k : Fin 3 => S11.projB k = 0) = {0, 1} := by
    decide
  rw [h, hfilter, Finset.sum_pair (by decide : (0 : Fin 3) ≠ 1)]
  show (1 / 3 : ℝ) + 1 / 3 = 2 / 3
  norm_num

/-- Second-factor coordinate at `1`: fiber `{2}`, so the value is `1 / 3`. -/
private theorem snd_one :
    (shuffleCell S11 sThird).2.weights 1 = 1 / 3 := by
  have h := shuffleCell_snd_fiber S11 sThird 1
  have hfilter : Finset.univ.filter (fun k : Fin 3 => S11.projB k = 1) = {2} := by
    decide
  rw [h, hfilter, Finset.sum_singleton]
  exact sThird_val _

/-- The two first-factor coordinates are distinct (`1 / 3 ≠ 2 / 3`). -/
example :
    (shuffleCell S11 sThird).1.weights 0 ≠
      (shuffleCell S11 sThird).1.weights 1 := by
  rw [fst_zero, fst_one]
  norm_num

end MathlibExtTest.Topology.Convenient.StdSimplexProductCellTests
