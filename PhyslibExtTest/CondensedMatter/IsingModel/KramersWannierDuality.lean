/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.KramersWannierDuality

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.KramersWannierDuality`

* `K4` has `4` vertices and `6` edges.
* The duality hypothesis `tanh β* = e^{-2β}` of `isingZ_self_dual_K4` holds for every `β > 0` with
  `β* = artanh (e^{-2β}) > 0`; the theorem then gives the explicit duality relation on `K₄` with
  `2⁴ = 16` and `|E| = 6` substituted.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.KramersWannierDuality

open _root_.StatMech _root_.StatMech.Ising

-- `K₄` has six edges.
example : (K4).edgeFinset.card = 6 := by decide

/-- For `β > 0`, the dual temperature `β* = artanh (e^{-2β})` is well defined and positive. -/
lemma exp_neg_two_mul_mem {β : ℝ} (hβ : 0 < β) : Real.exp (-2 * β) ∈ Set.Ioo 0 1 :=
  ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (by linarith)⟩

-- The duality hypothesis is satisfiable: `tanh (artanh (e^{-2β})) = e^{-2β}`.
example {β : ℝ} (hβ : 0 < β) :
    Real.tanh (Real.artanh (Real.exp (-2 * β))) = Real.exp (-2 * β) := by
  have h := exp_neg_two_mul_mem hβ
  exact Real.tanh_artanh ⟨by linarith [h.1], h.2⟩

-- The dual inverse temperature is positive.
example {β : ℝ} (hβ : 0 < β) : 0 < Real.artanh (Real.exp (-2 * β)) :=
  Real.artanh_pos (exp_neg_two_mul_mem hβ)

-- Kramers–Wannier duality on `K₄` at `β = 1`, with every hypothesis discharged and the constants
-- evaluated.
example :
    isingZ K4 (Real.artanh (Real.exp (-2))) 0
      = 16 * Real.cosh (Real.artanh (Real.exp (-2))) ^ 6 / (Real.exp 6 * 2) * isingZ K4 1 0 := by
  have h := exp_neg_two_mul_mem (β := 1) one_pos
  have htemp : Real.tanh (Real.artanh (Real.exp (-2 * 1))) = Real.exp (-2 * 1) :=
    Real.tanh_artanh ⟨by linarith [h.1], h.2⟩
  have hK := isingZ_self_dual_K4 1 _ htemp
  have hE : (K4).edgeFinset.card = 6 := by decide
  rw [hE] at hK
  simp only [Fintype.card_fin, mul_one] at hK
  norm_num at hK ⊢
  exact hK

end PhyslibExtTest.CondensedMatter.IsingModel.KramersWannierDuality
