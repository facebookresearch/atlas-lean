/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TENSOR RANK over a prime field is NP-complete

Source:
J. Håstad, "Tensor rank is NP-complete", Journal of Algorithms 11(4) (1990), 644-654,
doi:10.1016/0196-6774(90)90014-6 (the rank of a three-dimensional tensor over any finite field
is NP-complete to decide; over the rationals it is NP-hard);
C. J. Hillar and L.-H. Lim, "Most tensor problems are NP-hard", Journal of the ACM 60(6)
(2013), 1-39, doi:10.1145/2512329, Section 8 ("tensor rank is NP-hard over Q and
NP-complete over finite fields" [Håstad 1990]).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.ZMod.Defs
public import CSLibExt.Complexity.Algebraic.MatrixMultiplicationExponent

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TensorRankPrimeField

open Cslib.Complexity.Algebraic.MatrixMultiplicationExponent (HasTrilinearRankAtMost)

/-!
# TENSOR RANK over a prime field is NP-complete

Fix a prime `p` and the field `𝔽_p = ZMod p`. INSTANCE: a three-dimensional tensor
`T ∈ 𝔽_p^{n₁ × n₂ × n₃}` and an integer `r`. QUESTION: is the rank of `T` at most `r`, i.e. is
`T` a sum of `r` rank-one tensors `u ⊗ v ⊗ w` (`u ∈ 𝔽_p^{n₁}`, `v ∈ 𝔽_p^{n₂}`, `w ∈ 𝔽_p^{n₃}`)?

Håstad proves NP-completeness over every finite field, each field giving its own decision
problem; this module states it for the prime fields `ZMod p`, one decision problem per prime
`p`. The tensor is given as `n₁` slices, each `n₂` rows of `n₃` entries, every entry a natural
number below `p` naming an element of `ZMod p`; all three dimensions are read off the listed
entries. "Rank at most `r`" is the repository's `HasTrilinearRankAtMost` (CSLibExt, matrix
multiplication exponents): a list of at most `r` rank-one terms whose coefficient sum is `T`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the tensor, as a list of `n₁` slices of `n₂` rows of `n₃` entries, and the
bound `r`. -/
abbrev TensorRankPrimeFieldInstance := List (List (List ℕ)) × ℕ

/-- The first dimension `n₁`: the number of slices. -/
def dim₁ (i : TensorRankPrimeFieldInstance) : ℕ := i.1.length

/-- The second dimension `n₂`: the number of rows of the first slice. -/
def dim₂ (i : TensorRankPrimeFieldInstance) : ℕ := (i.1.headD []).length

/-- The third dimension `n₃`: the length of the first row of the first slice. -/
def dim₃ (i : TensorRankPrimeFieldInstance) : ℕ := ((i.1.headD []).headD []).length

/-- The entry `T[a][b][c]`, as a natural number. -/
def entry (i : TensorRankPrimeFieldInstance) (a b c : ℕ) : ℕ :=
  ((i.1.getD a []).getD b []).getD c 0

/-- Well-formedness of an instance for the prime `p`: every slice has `n₂` rows, every row has
`n₃` entries, and every entry is below `p`. -/
def WellFormed (p : ℕ) (i : TensorRankPrimeFieldInstance) : Prop :=
  ∀ s ∈ i.1, s.length = dim₂ i ∧ ∀ row ∈ s, row.length = dim₃ i ∧ ∀ x ∈ row, x < p

/-- The tensor of the instance as a coefficient function over `ZMod p`. -/
def tensor (p : ℕ) (i : TensorRankPrimeFieldInstance) :
    Fin (dim₁ i) → Fin (dim₂ i) → Fin (dim₃ i) → ZMod p :=
  fun a b c => ((entry i a b c : ℕ) : ZMod p)

/-- The tensor has rank at most `r` over `ZMod p`: it is the sum of at most `r` rank-one
tensors `u ⊗ v ⊗ w`. -/
def TensorRankPrimeFieldFeasible (p : ℕ) (i : TensorRankPrimeFieldInstance) : Prop :=
  HasTrilinearRankAtMost (tensor p i) i.2

open Classical in
/-- TENSOR RANK over `ZMod p` as a decision problem over bitstrings. -/
noncomputable def tensorRankPrimeFieldDec (p : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TensorRankPrimeFieldInstance) x with
  | some i => decide (WellFormed p i ∧ TensorRankPrimeFieldFeasible p i)
  | none => false

/-- **TENSOR RANK over the prime field `ZMod p` is NP-complete, for every prime `p`.** Source:
Håstad (1990); Hillar and Lim (2013), Section 8. -/
public theorem_wanted tensorRankPrimeField_npComplete (p : ℕ) (hp : p.Prime) :
    tensorRankPrimeFieldDec p ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (tensorRankPrimeFieldDec p)

end MetaMathlibExt.Complexity.NPComplete.TensorRankPrimeField
