/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.LeeYang.LeeYangAsano

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.LeeYang.LeeYangAsano`

* `IsMultiAffine` and `PolydiscStable` hold for `p(z) = (1 + z₀)(1 + z₁)` on two variables, its
  Asano contraction `asanoContract p 0 1` is `1 + z₀`, and `asanoContract_stable` applies;
* `PolydiscStable` fails for `1 + 2 z₀` (zero at `-1/2`);
* `asano_quadratic_contraction` for `(1 + t)²`;
* the Lee–Yang circle theorem `finiteGraph_hasLeeYangCircle` on the triangle
  `⊤ : SimpleGraph (Fin 3)` (not a matching) at `β = 1` and on the complete graph on four vertices
  at `β = 0`, and the derived consequence that the triangle's Lee–Yang polynomial does not vanish
  at `z = 2`.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.LeeYang.LeeYangAsano

open _root_.StatMech _root_.StatMech.LeeYang _root_.StatMech.LeeYang Polynomial

/-- The product `(1 + z₀)(1 + z₁)` of two independent single-site factors. -/
noncomputable def twoFactor (z : Fin 2 → ℂ) : ℂ := (1 + z 0) * (1 + z 1)

/-- `1 + w` has no zero in the open unit disk. -/
lemma one_add_ne_zero_of_norm_lt {w : ℂ} (hw : ‖w‖ < 1) : 1 + w ≠ 0 := by
  intro h
  have : w = -1 := by linear_combination h
  rw [this, norm_neg, norm_one] at hw
  exact lt_irrefl _ hw

/-- `twoFactor` is affine in each variable. -/
lemma twoFactor_multiAffine : IsMultiAffine twoFactor := by
  intro i z t
  fin_cases i <;> simp [twoFactor] <;> ring

/-- `twoFactor` has no zero in the open unit polydisc. -/
lemma twoFactor_stable : PolydiscStable twoFactor := fun _ hz =>
  mul_ne_zero (one_add_ne_zero_of_norm_lt (hz 0)) (one_add_ne_zero_of_norm_lt (hz 1))

/-- The Asano contraction of `(1 + z₀)(1 + z₁)` in `z₀, z₁` is `1 + z₀`. -/
lemma asanoContract_twoFactor : asanoContract twoFactor 0 1 = fun z => 1 + z 0 := by
  funext z
  simp [asanoContract, twoFactor]
  ring

-- Asano's lemma applied: `1 + z₀` is polydisc stable.
example : PolydiscStable (fun z : Fin 2 → ℂ => 1 + z 0) := by
  rw [← asanoContract_twoFactor]
  exact asanoContract_stable twoFactor twoFactor_multiAffine twoFactor_stable (by decide)

-- `PolydiscStable` is not trivial: `1 + 2 z₀` vanishes at `z₀ = -1/2`.
example : ¬ PolydiscStable (fun z : Fin 2 → ℂ => 1 + 2 * z 0) := by
  intro h
  refine h (fun _ => -1 / 2) (fun _ => ?_) (by norm_num)
  rw [norm_div, norm_neg, norm_one, Complex.norm_ofNat]
  norm_num

-- The one-variable Asano lemma for `(1 + t)² = 1 + 2t + t²`.
example (z : ℂ) (hz : ‖z‖ < 1) : (1 : ℂ) + 1 * z ≠ 0 := by
  refine asano_quadratic_contraction 1 2 1 z (fun t ht => ?_) hz
  have h1 := one_add_ne_zero_of_norm_lt ht
  have : (1 : ℂ) + 2 * t + 1 * t ^ 2 = (1 + t) * (1 + t) := by ring
  rw [this]
  exact mul_ne_zero h1 h1

-- The Lee–Yang circle theorem for the triangle at `β = 1`.
example : HasLeeYangCircle (⊤ : SimpleGraph (Fin 3)) 1 :=
  finiteGraph_hasLeeYangCircle _ zero_le_one

-- The Lee–Yang circle theorem for the complete graph on four vertices at `β = 0`.
example : HasLeeYangCircle (⊤ : SimpleGraph (Fin 4)) 0 :=
  finiteGraph_hasLeeYangCircle _ le_rfl

-- Consequence: the triangle's Lee–Yang polynomial at `β = 1` does not vanish at `z = 2`.
example : (leeYangComplexPolynomial (⊤ : SimpleGraph (Fin 3)) 1).eval 2 ≠ 0 := by
  intro h
  have := finiteGraph_hasLeeYangCircle (⊤ : SimpleGraph (Fin 3)) zero_le_one 2 h
  norm_num at this

end PhyslibExtTest.CondensedMatter.IsingModel.LeeYang.LeeYangAsano
