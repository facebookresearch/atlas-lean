/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.HeckeOperator.CoeffCommute

@[expose] public section

/-- exactSource consumer: commutation of the `T`-type coefficient operators,
with the original binders. -/
example (k : ℤ) {p q : ℕ} (hpq : Nat.Coprime p q) (a : ℕ → ℂ) :
    ModularForm.coeffHeckeT k p (ModularForm.coeffHeckeT k q a) =
      ModularForm.coeffHeckeT k q (ModularForm.coeffHeckeT k p a) :=
  ModularForm.coeffHeckeT_comm_of_coprime k hpq a

/-- exactSource consumer: `T`- and `U`-type coefficient operators commute. -/
example (k : ℤ) {p q : ℕ} (hpq : Nat.Coprime p q) (a : ℕ → ℂ) :
    ModularForm.coeffHeckeT k p (ModularForm.coeffHeckeU q a) =
      ModularForm.coeffHeckeU q (ModularForm.coeffHeckeT k p a) :=
  ModularForm.coeffHeckeT_coeffHeckeU_comm_of_coprime k hpq a

/-- Boundary: coprimality matters. At `p = q = 2`, weight `2`, the
operators `T 2` and `U 2` disagree at index `1` on the indicator of `1`. -/
example :
    ModularForm.coeffHeckeT 2 2 (ModularForm.coeffHeckeU 2 (fun m => if m = 1 then 1 else 0)) 1 ≠
      ModularForm.coeffHeckeU 2 (ModularForm.coeffHeckeT 2 2
        (fun m => if m = 1 then 1 else 0)) 1 := by
  simp [ModularForm.coeffHeckeT_apply, ModularForm.coeffHeckeU_apply]

/-- Boundary: coprimality matters for `coeffHeckeT_comm_of_coprime`. At the non-coprime indices
`2` and `4`, weight `2`, the operators `T 2` and `T 4` disagree at index `2` on the
indicator of `1` (the values are `4` and `0`). -/
example :
    ModularForm.coeffHeckeT 2 2 (ModularForm.coeffHeckeT 2 4 (fun m => if m = 1 then 1 else 0)) 2 ≠
      ModularForm.coeffHeckeT 2 4 (ModularForm.coeffHeckeT 2 2
        (fun m => if m = 1 then 1 else 0)) 2 := by
  norm_num [ModularForm.coeffHeckeT_apply]

/-- Composite coprime indices, where the prime-index `ModularForm.coeffHeckeT_comm` does not
apply: `T 4` and `T 9` commute. -/
example (k : ℤ) (a : ℕ → ℂ) :
    ModularForm.coeffHeckeT k 4 (ModularForm.coeffHeckeT k 9 a) =
      ModularForm.coeffHeckeT k 9 (ModularForm.coeffHeckeT k 4 a) :=
  ModularForm.coeffHeckeT_comm_of_coprime k (by decide) a

/-- Composite coprime indices, where the prime-index `ModularForm.coeffHeckeT_coeffHeckeU_comm`
does not apply: `T 4` and `U 9` commute. -/
example (k : ℤ) (a : ℕ → ℂ) :
    ModularForm.coeffHeckeT k 4 (ModularForm.coeffHeckeU 9 a) =
      ModularForm.coeffHeckeU 9 (ModularForm.coeffHeckeT k 4 a) :=
  ModularForm.coeffHeckeT_coeffHeckeU_comm_of_coprime k (by decide) a
