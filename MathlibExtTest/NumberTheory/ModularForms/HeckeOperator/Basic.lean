/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.HeckeOperator.Basic

@[expose] public section

/-- exactSource consumer: commutation of the `T`-type coefficient operators,
with the original binders. -/
example (k : ℤ) {p q : ℕ} (hpq : Nat.Coprime p q) (a : ℕ → ℂ) :
    ModularForm.coeffHeckeT k p (ModularForm.coeffHeckeT k q a) =
      ModularForm.coeffHeckeT k q (ModularForm.coeffHeckeT k p a) :=
  ModularForm.coeffHeckeT_comm k hpq a

/-- exactSource consumer: `T`- and `U`-type coefficient operators commute. -/
example (k : ℤ) {p q : ℕ} (hpq : Nat.Coprime p q) (a : ℕ → ℂ) :
    ModularForm.coeffHeckeT k p (ModularForm.coeffHeckeU q a) =
      ModularForm.coeffHeckeU q (ModularForm.coeffHeckeT k p a) :=
  ModularForm.coeffHeckeT_coeffHeckeU_comm k hpq a

/-- Boundary: coprimality matters. At `p = q = 2`, weight `2`, the
operators `T 2` and `U 2` disagree at index `1` on the indicator of `1`. -/
example :
    ModularForm.coeffHeckeT 2 2 (ModularForm.coeffHeckeU 2 (fun m => if m = 1 then 1 else 0)) 1 ≠
      ModularForm.coeffHeckeU 2 (ModularForm.coeffHeckeT 2 2
        (fun m => if m = 1 then 1 else 0)) 1 := by
  simp [ModularForm.coeffHeckeT_apply, ModularForm.coeffHeckeU_apply]

/-- The `T`-type operator on functions is the `U`-type sum plus the diagonal term. -/
example (k : ℤ) (p : ℕ) (f : UpperHalfPlane → ℂ) :
    ModularForm.heckeT k p f =
      ModularForm.heckeU k p f + SlashAction.map k (ModularForm.heckeDiagMatrix p) f :=
  ModularForm.heckeT_eq_heckeU_add k p f
