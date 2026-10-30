/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.Coding
public import CSLibExtTest.Complexity.BooleanFunctions.OSSS

/-!
# Tests for arithmetic coding on `ConfigSpace E`

Tests for `CSLibExt.Complexity.BooleanFunctions.Coding` on `{0, 1}^Bool` with the ordering
`finTwoEquiv : Fin 2 ≃ Bool` (`0 ↦ false`, `1 ↦ true`):

* `prefixSet` at small inputs (`decide`);
* `condProbBit` and `condNorm` for the inhomogeneous product weight `μInh = weight νInh`
  (`P(ω true) = 1/3`, `P(ω false) = 3/4`), and `condProbBit_true_add_false`;
* non-vacuity of the chain rule `codeProb_eq_mass` and of `volume_codeFibre`: the hypotheses
  (strict positivity, total mass `1`) are proved for `μInh`, and the conclusions are evaluated at
  the all-true configuration, of mass `1/4`;
* `codeMap_eq_iff` for the uniform weight, where every threshold is `1/2`: the code of the point
  `u = (3/4, 3/4)` is the all-true configuration and the code of `(1/4, 3/4)` is not;
* `stoppingTime` and `eval_determined_by_queried` for `andTree`.
-/

@[expose] public section

namespace StatMechTest.BooleanFunctions

open StatMech StatMech.OSSS StatMech.OSSS.Monotonic StatMech.OSSS.Coding MeasureTheory

/-- The ordering of the coordinates of `{0, 1}^Bool` used in these tests. -/
abbrev σTwo : Fin 2 ≃ Bool := finTwoEquiv

example : prefixSet (σTwo : Fin 2 → Bool) 0 = ∅ := by decide
example : prefixSet (σTwo : Fin 2 → Bool) 1 = {false} := by decide
example : prefixSet (σTwo : Fin 2 → Bool) 2 = {false, true} := by decide

/-! ## Conditional bit probabilities for an inhomogeneous weight -/

/-- The product weight of `νInh` as a function on configurations. -/
noncomputable abbrev μInh : ConfigSpace Bool → ℝ := weight νInh

/-- `μInh` is strictly positive. -/
lemma μInh_pos (ω : ConfigSpace Bool) : 0 < μInh ω := by
  simp only [μInh, weight, Fintype.prod_bool]
  cases ω true <;> cases ω false <;> norm_num [νInh]

/-- `μInh` has total mass `1`. -/
lemma μInh_sum : ∑ ω, μInh ω = 1 := by
  simp [μInh, weight, sum_configSpace_bool, νInh]; norm_num

example (η : ConfigSpace Bool) : condNorm μInh ∅ η = 1 := by rw [condNorm_empty, μInh_sum]

example : condNorm μInh Finset.univ (fun _ => true) = 1 / 4 := by
  rw [condNorm_univ]; simp [μInh, weight, νInh]; norm_num

/-- With nothing revealed, the bit at `true` is `1` with probability `1/3`. -/
lemma condProbBit_μInh_empty (η : ConfigSpace Bool) : condProbBit μInh ∅ η true true = 1 / 3 := by
  simp [condProbBit, condNorm, Agree, μInh, weight, sum_configSpace_bool, νInh]; norm_num

example (η : ConfigSpace Bool) : condProbBit μInh ∅ η true false = 2 / 3 := by
  have h := condProbBit_true_add_false μInh ∅ η true (by rw [condNorm_empty, μInh_sum]; norm_num)
  rw [condProbBit_μInh_empty] at h; linarith

/-- Revealing the independent coordinate `false` does not change the bit probability at `true`. -/
example (η : ConfigSpace Bool) : condProbBit μInh {false} η true true = 1 / 3 := by
  cases h : η false <;>
    simp [condProbBit, condNorm, Agree, μInh, weight, sum_configSpace_bool, νInh, h] <;> norm_num

/-! ## The chain rule and the volume of a code fibre -/

/-- `codeProb_eq_mass` at the all-true configuration: `P(false = 1) · P(true = 1 | false = 1)`
is its mass `3/4 · 1/3 = 1/4`. -/
example : (∏ t : Fin 2, condProbBit μInh (prefixSet (σTwo : Fin 2 → Bool) (t : ℕ)) (fun _ => true)
      ((σTwo : Fin 2 → Bool) t) true) = 1 / 4 := by
  rw [codeProb_eq_mass μInh μInh_pos μInh_sum σTwo (fun _ => true)]
  simp [μInh, weight, νInh]; norm_num

example : (volume (codeFibre μInh σTwo (fun _ => true))).toReal = 1 / 4 := by
  rw [volume_codeFibre μInh μInh_pos μInh_sum]
  simp [μInh, weight, νInh]; norm_num

example (x : ConfigSpace Bool) :
    codeFibre μInh σTwo x = Set.univ.pi (codeInterval μInh (σTwo : Fin 2 → Bool) x) :=
  codeFibre_eq_box μInh μInh_pos σTwo x

/-! ## The code map for the uniform weight -/

/-- The uniform weight on `{0, 1}^Bool`. -/
noncomputable abbrev μUnif : ConfigSpace Bool → ℝ := fun _ => 1 / 4

/-- For the uniform weight every threshold is `1/2`. -/
lemma thr_μUnif (x : ConfigSpace Bool) (t : Fin 2) :
    thr μUnif (σTwo : Fin 2 → Bool) x t = 1 / 2 := by
  have h1 : prefixSet (σTwo : Fin 2 → Bool) 1 = {false} := by decide
  fin_cases t
  · change condProbBit μUnif (prefixSet (σTwo : Fin 2 → Bool) 0) x false false = 1 / 2
    rw [prefixSet_zero]
    simp [condProbBit, condNorm, Agree, sum_configSpace_bool]
    norm_num
  · change condProbBit μUnif (prefixSet (σTwo : Fin 2 → Bool) 1) x true false = 1 / 2
    rw [h1]
    cases hx : x false <;>
      simp [condProbBit, condNorm, Agree, sum_configSpace_bool, hx] <;> norm_num

example : codeMap μUnif (σTwo : Fin 2 → Bool) (fun _ => 3 / 4) = fun _ => true := by
  rw [codeMap_eq_iff]
  intro t
  rw [thr_μUnif]; norm_num

example : codeMap μUnif (σTwo : Fin 2 → Bool) ![1 / 4, 3 / 4] ≠ fun _ => true := by
  rw [Ne, codeMap_eq_iff]
  intro h
  have h0 := h 0
  rw [thr_μUnif] at h0
  norm_num at h0

/-! ## Stopping time and determination by the queried coordinates -/

example : stoppingTime andTree (fun _ => true) = 2 := by decide
example : stoppingTime andTree (fun x => !x) = 1 := by decide

/-- On a configuration with `ω true = false`, `andTree` reads only `true`, so changing the value
at `false` does not change its output. -/
example : andTree.eval (fun _ => false) = andTree.eval (fun x => !x) :=
  eval_determined_by_queried andTree (fun x => !x) (fun _ => false) (by decide)

end StatMechTest.BooleanFunctions
