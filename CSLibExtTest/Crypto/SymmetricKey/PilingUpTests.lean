/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Crypto.SymmetricKey.PilingUp
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Piling-up lemma tests

Concrete instances (`decide` checks and numeric examples) and axiom audits for
`Cslib.Crypto.SymmetricKey.PilingUp`. Imports the production module; no new API.
-/

open scoped BigOperators

namespace Cslib.Crypto.SymmetricKey.PilingUp

/-! ## Numeric instances against L4 -/

/-- Two-bit numeric instance against L4. -/
example : (((jointPMF ![coin34, coin14]).map (xorAll 2)) false).toReal
  = 3 / 8 := by
  have h := pilingUp 2 ![coin34, coin14] (by norm_num)
  rw [Fin.prod_univ_two] at h
  have h0 : (![coin34, coin14] : Fin 2 → PMF Bool) 0 = coin34 :=
    Matrix.cons_val_zero _ _
  have h1 : (![coin34, coin14] : Fin 2 → PMF Bool) 1 = coin14 :=
    Matrix.cons_val_one _ _
  rw [h0, h1, bias_coin34, bias_coin14] at h
  norm_num at h ⊢
  linarith [h]

/-- Three-bit numeric instance against L4. -/
example : (((jointPMF ![coin34, coin34, coin34]).map (xorAll 3)) false).toReal
  = 9 / 16 := by
  have h := pilingUp 3 ![coin34, coin34, coin34] (by norm_num)
  rw [Fin.prod_univ_three] at h
  have h0 : (![coin34, coin34, coin34] : Fin 3 → PMF Bool) 0 = coin34 :=
    Matrix.cons_val_zero _ _
  have h1 : (![coin34, coin34, coin34] : Fin 3 → PMF Bool) 1 = coin34 := by
    exact Matrix.cons_val_one _ _
  have h2 : (![coin34, coin34, coin34] : Fin 3 → PMF Bool) 2 = coin34 := by
    rfl
  rw [h0, h1, h2, bias_coin34] at h
  norm_num at h ⊢
  linarith [h]

/-! ## Toy-SPN concrete instances -/

-- Parity on small vectors.
example : parity (fun i : Fin 2 => i = 0) (fun _ => true) = true := by decide
example : parity (fun i : Fin 2 => i = 0) (fun i => i = 1) = false := by decide
example : parity (fun _ : Fin 3 => true) (fun i => i = 0 || i = 1) = false := by decide
example : parity (fun _ : Fin 3 => true) (fun i => i = 0) = true := by decide

-- Transported mask computed explicitly.
example : transportMask mask0 swap2 = (fun i : Fin 2 => i = 1) := by decide

-- One-round trail: identity block, swap, zero key.
example :
  errBit mask0 (fun i : Fin 2 => i = 0) (transportMask mask0 swap2)
  ((fun z => z) (xorVec (fun i : Fin 2 => i = 0) (fun _ => false)))
  = true := by decide

-- Two-round trail: identity then negation blocks, swap, zero keys.
example :
  errBit mask0 (fun i : Fin 2 => i = 1)
  (transportMask mask0 swap2)
  ((fun z : Fin 2 → Bool => fun i => !(z i))
  (xorVec (fun i : Fin 2 => i = 1) (fun _ => false)))
  = false := by decide

-- Full two-round telescope on closed data.
example :
  ((List.range 2).map (fun i =>
  errBit mask0
  (if i = 0 then (fun j : Fin 2 => j = 0) else (fun j : Fin 2 => j = 1))
  (transportMask mask0 swap2)
  ((if i = 0 then (fun z : Fin 2 → Bool => z)
  else (fun z : Fin 2 → Bool => fun j => !(z j)))
  (xorVec
  (if i = 0 then (fun j : Fin 2 => j = 0)
  else (fun j : Fin 2 => j = 1))
  (fun _ => false))))).foldr Bool.xor false
  = (parity mask0 (fun j : Fin 2 => j = 0)
  ^^ parity mask0 (fun j : Fin 2 => j = 1)) := by decide

/-- No key-only correction can replace mask transport (regression test). -/
example : ¬ ∃ c : Fin 2 → Bool, ∀ x k : Fin 2 → Bool,
  parity mask0 (xorVec x k)
  = (parity mask0 (permute swap2 (xorVec x k)) ^^ parity c k) := by decide

-- The transported identity holds on the first separating input.
example : parity (transportMask mask0 swap2)
  ((fun z : Fin 2 → Bool => z)
  (xorVec (fun i : Fin 2 => i = 0) (fun _ => false)))
  = parity mask0
  (permute swap2 ((fun z : Fin 2 → Bool => z)
  (xorVec (fun i : Fin 2 => i = 0) (fun _ => false)))) := by decide

-- The untransported parity differs from the permuted parity there.
example : parity mask0 (xorVec (fun i : Fin 2 => i = 0) (fun _ => false))
  ≠ parity mask0
  (permute swap2 (xorVec (fun i : Fin 2 => i = 0) (fun _ => false))) := by decide

/-! ## Axiom audits -/

#print axioms Cslib.Crypto.SymmetricKey.PilingUp.correlation_xor
#print axioms Cslib.Crypto.SymmetricKey.PilingUp.pilingUp
#print axioms Cslib.Crypto.SymmetricKey.PilingUp.trail_telescope
#print axioms Cslib.Crypto.SymmetricKey.PilingUp.trail_bias_matsui
#print axioms Cslib.Crypto.SymmetricKey.PilingUp.trail_bias_correlation

end Cslib.Crypto.SymmetricKey.PilingUp
