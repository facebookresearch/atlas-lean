/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-
Modifications copyright (c) 2026 Meta Platforms, Inc. and affiliates.
-/
/-
Ported from TauCetiProject/TauCeti at
62bbc0596dc3539d488232e4e924a338548ea0a9:
TauCeti/Data/Fin/Basic.lean
Public source: https://github.com/TauCetiProject/TauCeti
The original contributors' copyright, author and Apache License 2.0
notice is retained above. Modification notice: use the explicitly
listed MathlibExt ports for this complete SBI dependency closure;
retain the mathematical declarations and original names. Identity-scalar
multilinear maps and endomorphism-application lemmas use the pinned
Mathlib API; the finite-coordinate port keeps only its four needed lemmas.
-/
module

public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Algebra.Group.End
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Group.Fin.Basic

/-!
# Only the finite cyclic-coordinate lemmas needed by the Connes complex

The source's unrelated parent-table, interval and permutation-classification
sections are omitted. These four complete source lemmas compute terminal
partial products, contraction of adjacent coordinates and powers of the
cyclic rotation.
-/

public section

open Function Equiv Finset

namespace Fin

/-- The final partial product is the product of all the entries. -/
@[to_additive /-- The final partial sum is the sum of all the entries. -/]
theorem partialProd_last {M : Type*} [CommMonoid M] {n : ℕ} (f : Fin n → M) :
    partialProd f (last n) = ∏ i, f i := by
  rw [partialProd, val_last]
  rw [(List.take_eq_self_iff _).mpr (by simp), prod_ofFn]

/-- Multiplying two adjacent entries of a tuple does not change the product of all its
entries. -/
@[to_additive (attr := simp)
  /-- Adding two adjacent entries of a tuple does not change the sum of all its entries. -/]
theorem prod_contractNth_castSucc {M : Type*} [CommMonoid M] {n : ℕ} (j : Fin (n + 1))
    (g : Fin (n + 2) → M) : ∏ k, contractNth j.castSucc (· * ·) g k = ∏ k, g k := by
  have hlast : j.castSucc.succ.succAbove (last (n + 1)) = last (n + 2) :=
    succAbove_of_le_castSucc _ _ (by simp [le_def]; omega)
  rw [← partialProd_last, ← partialProd_last, partialProd_contractNth, Function.comp_apply,
    hlast]

/-- The value of a power of the cyclic permutation `finRotate n`: it adds `k` modulo `n`. -/
theorem coe_finRotate_pow {n : ℕ} (k : ℕ) (c : Fin n) :
    ((finRotate n ^ k) c : ℕ) = (c + k) % n := by
  induction k with
  | zero => simp [Nat.mod_eq_of_lt c.isLt]
  | succ k ih =>
    have : NeZero n := ⟨Nat.pos_iff_ne_zero.mp c.pos⟩
    rw [pow_succ', Equiv.Perm.mul_apply, finRotate_apply, val_add, ih, val_one',
      ← Nat.add_mod, ← add_assoc]

/-- The cyclic successor of a non-last index `i.castSucc` of `Fin (n + 1)` is `i.succ`. -/
theorem finRotate_castSucc {n : ℕ} (i : Fin n) : finRotate (n + 1) i.castSucc = i.succ :=
  finRotate_of_lt i.isLt

end Fin
