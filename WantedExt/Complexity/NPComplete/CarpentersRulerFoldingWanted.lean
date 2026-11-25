/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CARPENTER'S RULER FOLDING is NP-complete

Source:
J. Hopcroft, D. Joseph and S. Whitesides, "On the movement of robot arms in 2-dimensional bounded
regions", SIAM Journal on Computing 14 (1985), 315-333, doi:10.1137/0214025 (conference version:
Proc. 23rd Annual Symposium on Foundations of Computer Science (FOCS 1982), 280-289,
doi:10.1109/SFCS.1982.29);
G. Călinescu and A. Dumitrescu, "The carpenter's ruler folding problem", in *Combinatorial and
Computational Geometry*, MSRI Publications 52, Cambridge University Press (2005), 155-166
(introduction: the problem "was first posed in [Hopcroft et al. 1985], where the authors proved
that the problem is NP-complete using a reduction from the NP-complete problem PARTITION").
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CarpentersRulerFolding

/-!
# CARPENTER'S RULER FOLDING is NP-complete

INSTANCE: a nonempty sequence of positive integer link lengths `l₁, …, lₙ` (`n ≥ 1`; a carpenter's
ruler: rigid links joined end to end by hinges) and a positive integer `K`.
QUESTION: can the ruler be folded, each hinge either straight or folded completely (angle `0` or
`180` degrees), so that its folded length is at most `K`?

On the line, a folding chooses a direction `±1` for every link: the joints sit at the positions
`p₀ = 0` and `pⱼ = pⱼ₋₁ ± lⱼ`, and the folded ruler occupies the interval from the least to the
greatest joint position, so its folded length is `maxⱼ pⱼ - minⱼ pⱼ`. The folded length is at most
`K` exactly when every two joint positions differ by at most `K` (`RulerFoldingFeasible`). The
direction of the first link is immaterial (reversing all directions mirrors the folding).

Hopcroft, Joseph and Whitesides prove the problem NP-complete by a reduction from PARTITION; it is
NP-complete in the ordinary sense (a pseudo-polynomial dynamic program exists), so link lengths
and `K` use the canonical binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the link lengths, in order along the ruler, and the bound `K`. -/
abbrev CarpentersRulerFoldingInstance := List ℕ × ℕ

/-- The position of joint `j` when link `t` points right (`dirs[t] = true`) or left: the signed
sum of the first `j` links (joint `0` at position `0`). -/
def jointPos (lengths : List ℕ) (dirs : List Bool) (j : ℕ) : ℤ :=
  ((List.zipWith (fun l d => if d then (l : ℤ) else -(l : ℤ)) lengths dirs).take j).sum

/-- Well-formedness of an instance: the ruler has at least one link, every link length is
positive, and `0 < K`. -/
def WellFormed (i : CarpentersRulerFoldingInstance) : Prop :=
  i.1 ≠ [] ∧ (∀ l ∈ i.1, 0 < l) ∧ 0 < i.2

/-- Some choice of a direction for every link places all joints within an interval of length at
most `K`. -/
def RulerFoldingFeasible (i : CarpentersRulerFoldingInstance) : Prop :=
  ∃ dirs : List Bool, dirs.length = i.1.length ∧
    ∀ j ≤ i.1.length, ∀ j' ≤ i.1.length, jointPos i.1 dirs j - jointPos i.1 dirs j' ≤ i.2

open Classical in
/-- CARPENTER'S RULER FOLDING as a decision problem over bitstrings. -/
noncomputable def carpentersRulerFoldingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CarpentersRulerFoldingInstance) x with
  | some i => decide (WellFormed i ∧ RulerFoldingFeasible i)
  | none => false

/-- **CARPENTER'S RULER FOLDING is NP-complete.** Source: Hopcroft, Joseph and Whitesides (1985);
Călinescu and Dumitrescu (2005). -/
public theorem_wanted carpentersRulerFolding_npComplete :
    carpentersRulerFoldingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L carpentersRulerFoldingDec

end MetaMathlibExt.Complexity.NPComplete.CarpentersRulerFolding
