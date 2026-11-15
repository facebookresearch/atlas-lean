/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# D-VECTOR COVERING is NP-complete

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, web edition
(2000), problem MAXIMUM D-VECTOR COVERING (decision version);
S. F. Assmann, D. S. Johnson, D. J. Kleitman and J. Y.-T. Leung, "On a dual version of the
one-dimensional bin packing problem", Journal of Algorithms 5(4) (1984), 502-525,
doi:10.1016/0196-6774(84)90004-x (bin covering, the case `d = 1`; the paper was not available,
and its NP-hardness result is the one recorded by J. Csirik, J. B. G. Frenk, M. Labbé and
S. Zhang, "Two simple algorithms for bin covering", Acta Cybernetica 14(1) (1999), 13-25).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Field.Rat
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DVectorCovering

/-!
# D-VECTOR COVERING is NP-complete

INSTANCE: a positive integer `d`, a finite list `X = (x₁, …, x_N)` of vectors in `[0, 1]^d`
with rational components (repetitions allowed), and a positive integer `K`.
QUESTION: is there a partition of the positions `{1, …, N}` of `X` into subsets `S₁, …, Sₘ` such
that at least `K` of them are unit covers, where `S` is a unit cover if, for every `i ≤ d`, the
sum of the `i`-th components of the vectors `x_j`, `j ∈ S`, is at least `1`?

This is the decision version of MAXIMUM D-VECTOR COVERING of Crescenzi and Kann. The
dimension `d` is part of the instance, so every fixed `d ≥ 1` is a special case. For `d = 1` the
problem is bin covering (fill as many bins of size `1` as possible to level at least `1`), which
Assmann, Johnson, Kleitman and Leung (1984) proved NP-hard (as recorded by Csirik, Frenk, Labbé
and Zhang, 1999): an instance of 3-PARTITION with `3m` sizes summing to `mB` has a solution iff
the sizes divided by `B` admit `m` unit covers. Membership in NP: the partition is a
certificate.

Crescenzi and Kann write "Set `X` of vectors"; this module states the list (multiset) variant,
in which equal vectors may repeat. Its case `d = 1` is exactly bin covering as Csirik, Frenk,
Labbé and Zhang define it ("a list `L = (a₁, a₂, …, aₙ)` of items with size `s(aᵢ)`", normalized
to bin capacity `1`), the problem that Assmann et al. proved NP-hard.

A partition into `m` subsets is a map `f` from positions to `Fin m`, the subset `Sⱼ` being the
preimage of `j`. Empty preimages are not unit covers (`d ≥ 1`), so allowing them does not change
the count. A vector is a list of `d` components; a component is a pair
`(numerator, denominator)` with a positive denominator and the numerator at most the
denominator. Numbers use the binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the dimension `d`, the vectors of `X` (each a list of `d` components
`(numerator, denominator)`), and the bound `K`. -/
abbrev DVectorCoveringInstance := ℕ × List (List (ℕ × ℕ)) × ℕ

/-- The rational number `p / q` encoded by the pair `(p, q)`. -/
def toRat (q : ℕ × ℕ) : ℚ := (q.1 : ℚ) / (q.2 : ℚ)

/-- Well-formedness of an instance: `d` is positive, every vector has `d` components, each in
`[0, 1]` with a positive denominator, and `K` is positive. -/
def WellFormed (i : DVectorCoveringInstance) : Prop :=
  0 < i.1 ∧ (∀ x ∈ i.2.1, x.length = i.1 ∧ ∀ q ∈ x, 0 < q.2 ∧ q.1 ≤ q.2) ∧ 0 < i.2.2

/-- The `t`-th component of the vector at position `j` of `X`. -/
def component (i : DVectorCoveringInstance) (j : Fin i.2.1.length) (t : ℕ) : ℚ :=
  toRat ((i.2.1.get j).getD t (0, 1))

/-- The vectors at the positions in `S` form a unit cover: for every coordinate `t < d`, their
`t`-th components sum to at least `1`. -/
def IsUnitCover (i : DVectorCoveringInstance) (S : Finset (Fin i.2.1.length)) : Prop :=
  ∀ t < i.1, 1 ≤ ∑ j ∈ S, component i j t

open Classical in
/-- Some partition of `X` into subsets `S₀, …, Sₘ₋₁` (the preimages of a map `f` from positions
to `Fin m`) has at least `K` unit covers among its subsets. -/
def DVectorCoveringFeasible (i : DVectorCoveringInstance) : Prop :=
  ∃ (m : ℕ) (f : Fin i.2.1.length → Fin m),
    i.2.2 ≤ (Finset.univ.filter fun s : Fin m =>
      IsUnitCover i (Finset.univ.filter fun j => f j = s)).card

open Classical in
/-- D-VECTOR COVERING as a decision problem over bitstrings. -/
noncomputable def dVectorCoveringDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DVectorCoveringInstance) x with
  | some i => decide (WellFormed i ∧ DVectorCoveringFeasible i)
  | none => false

/-- **D-VECTOR COVERING (list of vectors) is NP-complete.** Source: Crescenzi and Kann, MAXIMUM
D-VECTOR COVERING; Assmann, Johnson, Kleitman and Leung (1984). -/
public theorem_wanted dVectorCovering_npComplete :
    dVectorCoveringDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L dVectorCoveringDec

end MetaMathlibExt.Complexity.NPComplete.DVectorCovering
