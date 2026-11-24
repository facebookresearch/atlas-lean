/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Basic.Real.Basic

@[expose] public section

/-!
# The Leontief input–output system

In a finite input–output economy, `A i j` is the input of sector `i` needed per unit of sector
`j`'s output. Gross output `x` meets final demand `d` when it covers intermediate demand plus
final demand, `x = A x + d` (`IsGrossOutput`). This holds exactly when `(1 - A) x = d`
(`isGrossOutput_iff`). No invertibility or sign condition is assumed; a closed production loop
(`A = 1`) shows that the solution need not be unique without a productivity condition.

## Main results

* `MathlibExt.Economics.InputOutput.isGrossOutput_iff`

## References

* W. Leontief, *Input-Output Economics*, 2nd ed., Oxford University Press (1986).
* R. E. Miller, P. D. Blair, *Input-Output Analysis: Foundations and Extensions*, 2nd ed.,
  Cambridge University Press (2009), Chapter 2 (the balance equation `x = A x + f` and the
  Leontief inverse).

Atlas roadmap target AP06.T01.
-/

namespace MathlibExt.Economics.InputOutput

open Matrix

/-- Leontief balance condition: gross output `x` covers intermediate demand `A x` plus final
demand `d`. Here `A i j` is the input of sector `i` needed per unit of sector `j`'s output.
This is only the balance equation; the economic sign conditions (nonnegative `A`, `d`, and
`x`) are separate hypotheses where results need them. -/
def IsGrossOutput {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (d x : ι → ℝ) : Prop :=
  x = A *ᵥ x + d

/-- **Leontief system.** Gross output satisfies `x = A x + d` exactly when it solves
`(1 - A) x = d`. No invertibility or sign condition is needed. -/
theorem isGrossOutput_iff {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ}
    {d x : ι → ℝ} :
    IsGrossOutput A d x ↔ (1 - A) *ᵥ x = d := by
  unfold IsGrossOutput
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_iff_eq_add']

end MathlibExt.Economics.InputOutput
