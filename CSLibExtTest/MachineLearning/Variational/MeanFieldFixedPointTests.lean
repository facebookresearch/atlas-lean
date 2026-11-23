/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Variational.MeanFieldFixedPoint

/-!
# Mean-field fixed-point map tests

Closed checks: the approximate-iteration error bound on a set, the contraction and the unique
fixed point of `m ↦ tanh (U m + h)` on `ℝ³` for `‖U‖ ≤ 1 / 2`, the fixed-point equation
`artanh m = U m + h`, and the instantiated error bound. A boundary probe: with `U = 0` the fixed
point is `tanh h`, and it lies strictly inside the cube. The definitions are real-valued and not
executable.
-/

namespace Cslib.MachineLearning.Variational

open Set Real
open scoped NNReal

local notation "E3" => EuclideanSpace ℝ (Fin 3)

example {C : Set ℝ} {T Tstar : ℝ → ℝ} {ζ : ℝ} {x₀ xhat : ℝ} (hT : MapsTo T C C)
    (hTstar : LipschitzOnWith (1 / 2) Tstar C) (hfix : Tstar xhat = xhat) (hxhat : xhat ∈ C)
    (hζ : ∀ x ∈ C, dist (T x) (Tstar x) ≤ ζ) (hx₀ : x₀ ∈ C) (k : ℕ) :
    dist (T^[k] x₀) xhat ≤ ((1 / 2 : ℝ≥0) : ℝ) ^ k * dist x₀ xhat +
      ζ * (1 - ((1 / 2 : ℝ≥0) : ℝ) ^ k) / (1 - ((1 / 2 : ℝ≥0) : ℝ)) :=
  dist_iterate_le_of_dist_le' (by norm_num) hT hTstar hfix hxhat hζ hx₀ k

example (U : E3 →L[ℝ] E3) (h : E3) (hU : ‖U‖₊ ≤ 1 / 2) :
    ContractingWith (1 / 2) (meanFieldMap U h) :=
  contractingWith_meanFieldMap h (by norm_num) hU

example (U : E3 →L[ℝ] E3) (h : E3) (hU : ‖U‖₊ ≤ 1 / 2) :
    ∃! m : E3, meanFieldMap U h m = m :=
  existsUnique_meanFieldMap_eq_self h (by norm_num) hU

example (U : E3 →L[ℝ] E3) (h m : E3) (hm : meanFieldMap U h m = m) (i : Fin 3) :
    m i ∈ Ioo (-1) 1 ∧ artanh (m i) = (U m) i + h i :=
  have hm' := (meanFieldMap_eq_self_iff U h m).1 hm
  ⟨hm'.1 i, hm'.2 i⟩

/-- Boundary probe: with no coupling the fixed point is `tanh h`, strictly inside the cube. -/
example (h : E3) : meanFieldMap 0 h (meanFieldMap 0 h 0) = meanFieldMap 0 h 0 := by
  ext i; simp

example (h : E3) (i : Fin 3) : |meanFieldMap 0 h 0 i| < 1 :=
  abs_meanFieldMap_apply_lt_one 0 h 0 i

example (U : E3 →L[ℝ] E3) (h : E3) (hU : ‖U‖₊ ≤ 1 / 2) {m : E3}
    (hm : meanFieldMap U h m = m) {T : E3 → E3} {ζ : ℝ}
    (hζ : ∀ x, dist (T x) (meanFieldMap U h x) ≤ ζ) (x₀ : E3) (k : ℕ) :
    dist (T^[k] x₀) m ≤ ((1 / 2 : ℝ≥0) : ℝ) ^ k * dist x₀ m +
      ζ * (1 - ((1 / 2 : ℝ≥0) : ℝ) ^ k) / (1 - ((1 / 2 : ℝ≥0) : ℝ)) :=
  dist_iterate_le_of_dist_le_meanFieldMap (by norm_num) hU hm (mapsTo_univ T univ)
    (mem_univ m) (fun x _ => hζ x) (mem_univ x₀) k

#print axioms dist_iterate_le_of_dist_le
#print axioms dist_iterate_le_of_dist_le'
#print axioms lipschitzWith_tanh
#print axioms meanFieldMap
#print axioms meanFieldMap_apply
#print axioms abs_meanFieldMap_apply_lt_one
#print axioms contractingWith_meanFieldMap
#print axioms meanFieldMap_eq_self_iff
#print axioms existsUnique_meanFieldMap_eq_self
#print axioms dist_iterate_le_of_dist_le_meanFieldMap

end Cslib.MachineLearning.Variational
