/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The permanent is #P-complete (Valiant)

Source:
L. G. Valiant, "The complexity of computing the permanent", Theoretical Computer Science 8
(1979), 189-201.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes
public import Mathlib.Data.Fintype.Perm

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.PermanentSharpPComplete

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# The permanent is #P-complete (Valiant)

The permanent of a 0-1 matrix, as a function from bitstrings (decoding to a dimension `n` and a
list of `n^2` entries `0` or `1`, malformed inputs giving `0`), is `#P`-complete: it is in `#P`
and every `#P` function is computable from it by a polynomial-time oracle computation.
`SharpPComplete` is the oracle-completeness notion of the shared file.
-/


/-- The permanent of a 0-1 matrix, from a bitstring decoding `(n, entries)` in row-major order. -/
noncomputable def permFun (x : List Bool) : ℕ :=
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := ℕ × List ℕ) x with
  | some (n, entries) =>
    if entries.length = n * n ∧ ∀ e ∈ entries, e ≤ 1 then
      (Finset.univ : Finset (Equiv.Perm (Fin n))).sum (fun σ =>
        (Finset.univ : Finset (Fin n)).prod
          (fun i => entries.getD (i.val * n + (σ i).val) 0))
    else 0
  | none => 0

/-- **The permanent is #P-complete (Valiant).** Source: L. G. Valiant, "The complexity of
computing the permanent", Theoretical Computer Science 8 (1979), 189-201. -/
public theorem_wanted permanent_sharpP_complete :
    SharpPComplete permFun

end MetaMathlibExt.Complexity.KeyTheorems.PermanentSharpPComplete
