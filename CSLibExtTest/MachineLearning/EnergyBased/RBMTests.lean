/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.EnergyBased.RBM

@[expose] public section

/-!
# Tests for restricted Boltzmann machine conditionals
-/

set_option autoImplicit false

open Cslib.MachineLearning.RBM

namespace CSLibExtTest.MachineLearning.EnergyBased.RBMTests

/-- The binary indicator values used by the score. -/
example : bit true = 1 ∧ bit false = 0 := by
  simp [bit]

/-- Hidden conditional factorization, as an example. -/
example {m k : ℕ} (a : Fin m → ℝ) (b : Fin k → ℝ)
    (W : Fin m → Fin k → ℝ) (v : Fin m → Bool) (h : Fin k → Bool) :
    condHidden a b W v h =
      ∏ j, if h j then Real.sigmoid (hiddenLogit b W v j)
        else 1 - Real.sigmoid (hiddenLogit b W v j) :=
  condHidden_eq_prod_sigmoid a b W v h

/-- Visible conditional factorization, as an example. -/
example {m k : ℕ} (a : Fin m → ℝ) (b : Fin k → ℝ)
    (W : Fin m → Fin k → ℝ) (v : Fin m → Bool) (h : Fin k → Bool) :
    condVisible a b W v h =
      ∏ i, if v i then Real.sigmoid (visibleLogit a W h i)
        else 1 - Real.sigmoid (visibleLogit a W h i) :=
  condVisible_eq_prod_sigmoid a b W v h

/-- With no visible coordinates, one zero-bias hidden coordinate set to `true`
has conditional mass `Real.sigmoid 0`. -/
example : condHidden (m := 0) (k := 1) (fun _ => 0) (fun _ => 0)
    (fun _ _ => 0) (fun _ => true) (fun _ => true) = Real.sigmoid 0 := by
  rw [condHidden_eq_prod_sigmoid]
  simp [hiddenLogit, bit]

/-- With an empty hidden layer, the hidden conditional is the empty product. -/
example {m : ℕ} (a : Fin m → ℝ) (b : Fin 0 → ℝ)
    (W : Fin m → Fin 0 → ℝ) (v : Fin m → Bool) (h : Fin 0 → Bool) :
    condHidden a b W v h = 1 := by
  rw [condHidden_eq_prod_sigmoid]
  simp

end CSLibExtTest.MachineLearning.EnergyBased.RBMTests
