/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Fintype.BigOperators
import MathlibExt.Combinatorics.Additive.ConsecutiveZeroSum

/-!
# Consecutive orthogonal blocks over `ZMod 2`

The first `2 ^ a` columns form a sequence of length equal to the order of the group
`Fin a → ZMod 2`. A consecutive zero sum in that group vanishes in every row.
-/

namespace MetaMathlibExt

/-- **A block of consecutive coordinates orthogonal to $a$ vectors of $\mathbb{Z}_2^m$.** Let
$\mathbb{Z}_2 = \mathbb{Z}/2\mathbb{Z}$, let $2^a \le m$ and let
$v_1, \dots, v_a \in \mathbb{Z}_2^m$, with coordinates indexed by $\{0, \dots, m - 1\}$. Then there
are indices $s \le t$ in $\{0, \dots, m - 1\}$ such that $\sum_{j = s}^{t} (v_i)_j = 0$ in
$\mathbb{Z}_2$ for every $i$; that is, the nonzero vector whose ones occupy exactly the positions
$s, \dots, t$ is orthogonal to every $v_i$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Lemma 3.2 (`integers-2024-A38-lem-3-2`). -/
public theorem exists_consecutive_orthogonal {a m : ℕ} (hm : 2 ^ a ≤ m)
    (v : Fin a → Fin m → ZMod 2) :
    ∃ s t : Fin m, s ≤ t ∧ ∀ i, ∑ j ∈ Finset.Icc s t, v i j = 0 := by
  have hblock := (consecutive_constant_eq_card (Fin a → ZMod 2)).1.2
  rw [Fintype.card_fun, ZMod.card, Fintype.card_fin] at hblock
  obtain ⟨s, t, hst, w, hw, hsum⟩ := hblock (fun j i => v i (j.castLE hm))
  refine ⟨s.castLE hm, t.castLE hm, hst, fun i => ?_⟩
  rw [← Fin.map_castLEEmb_Icc s t hm, Finset.sum_map]
  have hrow := congrFun hsum i
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply] at hrow
  exact (Finset.sum_congr rfl fun j hj => by
    simp [show w j = 1 from hw j hj]).trans hrow

end MetaMathlibExt
