/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.LeeYang.LeeYangPolynomial

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.LeeYang.LeeYangPolynomial`

* `minusSpinCount` at the all-plus and all-minus configurations of three sites;
* `leeYangPolynomial` of the edgeless graph on one vertex is `1 + X`;
* `eval_leeYangPolynomial_at_fugacity` at zero field on the single edge: the value at `z = 1` is the
  partition function `isingZ`;
* `leeYangComplexPolynomial_ne_zero` on the triangle.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.LeeYang.LeeYangPolynomial

open _root_.StatMech _root_.StatMech.LeeYang Polynomial

-- The all-minus configuration on three sites has three minus spins.
example : minusSpinCount (fun _ : Fin 3 => false) = 3 := by decide

-- The all-plus configuration has none.
example : minusSpinCount (fun _ : Fin 3 => true) = 0 := by decide

-- A configuration with one minus spin.
example : minusSpinCount (![true, false, true] : ConfigSpace (Fin 3)) = 1 := by decide

-- Without edges the interaction weight is `1`.
example (β : ℝ) (s : ConfigSpace (Fin 3)) :
    zeroFieldInteractionWeight (⊥ : SimpleGraph (Fin 3)) β s = 1 := by
  unfold zeroFieldInteractionWeight
  rw [Finset.sum_eq_zero fun e he => by simp at he]
  simp

-- On one isolated vertex the Lee–Yang polynomial is `1 + X` (zero at `z = -1`).
example (β : ℝ) : leeYangPolynomial (⊥ : SimpleGraph (Fin 1)) β = 1 + X := by
  unfold leeYangPolynomial
  rw [← (Equiv.funUnique (Fin 1) Bool).symm.sum_comp, Fintype.sum_bool]
  simp only [zeroFieldInteractionWeight]
  rw [Finset.sum_eq_zero fun e he => by simp at he, Finset.sum_eq_zero fun e he => by simp at he]
  simp [minusSpinCount, Equiv.funUnique]

-- At zero field (`z = e^0 = 1`) the polynomial evaluates to the partition function.
example (β : ℝ) :
    (leeYangPolynomial (⊤ : SimpleGraph (Fin 2)) β).eval 1 =
      Ising.isingZ (⊤ : SimpleGraph (Fin 2)) β 0 := by
  have h := eval_leeYangPolynomial_at_fugacity (⊤ : SimpleGraph (Fin 2)) β 0
  simpa using h

-- The complex Lee–Yang polynomial of the triangle is not the zero polynomial.
example (β : ℝ) : leeYangComplexPolynomial (⊤ : SimpleGraph (Fin 3)) β ≠ 0 :=
  leeYangComplexPolynomial_ne_zero _ β

end PhyslibExtTest.CondensedMatter.IsingModel.LeeYang.LeeYangPolynomial
