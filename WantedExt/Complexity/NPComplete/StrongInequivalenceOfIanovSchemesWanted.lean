/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STRONG INEQUIVALENCE OF IANOV SCHEMES is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [PO16] STRONG INEQUIVALENCE OF
IANOV SCHEMES, p. 276 (references [Constable, Hunt, and Sahni, 1974] and [Rutledge, 1964];
transformation from 3SAT);
R. L. Constable, H. B. Hunt III and S. Sahni, "On the computational complexity of program
scheme equivalence", SIAM Journal on Computing 9 (1980), 396-416, doi:10.1137/0209031
(journal version of the 1974 Cornell report GJ cites: strong equivalence of single variable
program schemes is NP-complete);
J. D. Rutledge, "On Ianov's program schemata", Journal of the ACM 11 (1964), 1-9,
doi:10.1145/321203.321204 (membership in NP, per GJ).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.StrongInequivalenceOfIanovSchemes

/-!
# STRONG INEQUIVALENCE OF IANOV SCHEMES is NP-complete

INSTANCE: finite sets `F` and `P` of function and predicate symbols, a single variable `x`,
and two Ianov schemes over `F`, `P` and `x`, each a sequence `I₁, I₂, …, Iₘ` of instructions
of the form `x ← f(x)`, `if p(x) then goto Iⱼ else goto Iₖ`, and `halt`, where `f ∈ F` and
`p ∈ P`.
QUESTION: are the two given Ianov schemes not strongly equivalent, i.e., is there a domain
set `D`, an interpretation of each `f ∈ F` as a function `f : D → D`, an interpretation of
each `p ∈ P` as a function `p : D → {T, F}`, and an initial value `x₀ ∈ D` for `x`, such that
either both schemes halt with different final values for `x` or one halts and the other
doesn't?

The symbols are `f₀, …, f_{|F|-1}` and `p₀, …, p_{|P|-1}`; interpretations are families
indexed by `ℕ`, of which only the indices below `|F|` and `|P|` occur. A scheme is its
instruction list: `(0, r, 0, 0)` is `x ← f_r(x)`, `(1, r, j, k)` is
`if p_r(x) then goto Iⱼ else goto Iₖ` (targets numbered from `1` as in the source), and
`(2, 0, 0, 0)` is `halt`. Execution starts at `I₁` with `x = x₀`; after `x ← f(x)` control
passes to the next instruction; a scheme halts when control reaches a `halt`. A well-formed
scheme is nonempty, its jump targets lie in `1, …, m`, and its last instruction is not an
assignment, so control never leaves `I₁, …, Iₘ`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An Ianov scheme: its instruction list `I₁, …, Iₘ` (see the module docstring). -/
abbrev IanovScheme := List (ℕ × ℕ × ℕ × ℕ)

/-- An instance: `|F|`, `|P|`, and the two schemes. -/
abbrev StrongInequivalenceOfIanovSchemesInstance := ℕ × ℕ × IanovScheme × IanovScheme

/-- A scheme over `nF` function symbols and `nP` predicate symbols: nonempty, every
instruction is `x ← f_r(x)` with `r < nF`, `if p_r(x) then goto Iⱼ else goto Iₖ` with `r < nP`
and `1 ≤ j, k ≤ m`, or `halt`, and no assignment is the last instruction. -/
def IsScheme (nF nP : ℕ) (S : IanovScheme) : Prop :=
  S ≠ [] ∧
    ∀ c < S.length,
      (∃ r < nF, S[c]? = some (0, r, 0, 0) ∧ c + 1 < S.length) ∨
        (∃ r < nP, ∃ j k, S[c]? = some (1, r, j, k) ∧
          1 ≤ j ∧ j ≤ S.length ∧ 1 ≤ k ∧ k ≤ S.length) ∨
        S[c]? = some (2, 0, 0, 0)

/-- Well-formedness of an instance: both schemes are schemes over `F` and `P`. -/
def WellFormed (i : StrongInequivalenceOfIanovSchemesInstance) : Prop :=
  IsScheme i.1 i.2.1 i.2.2.1 ∧ IsScheme i.1 i.2.1 i.2.2.2

/-- One execution step on a configuration `(c, x)`, where `c` is the `0`-based index of the
current instruction `I_{c+1}`: an assignment applies its function and moves to the next
instruction, a test jumps to `Iⱼ` (index `j - 1`) or `Iₖ`, and a halted configuration is
fixed. -/
def step {D : Type} (S : IanovScheme) (F : ℕ → D → D) (P : ℕ → D → Bool) (cx : ℕ × D) :
    ℕ × D :=
  match S[cx.1]? with
  | some (0, r, _, _) => (cx.1 + 1, F r cx.2)
  | some (1, r, j, k) => (if P r cx.2 then j - 1 else k - 1, cx.2)
  | _ => cx

/-- Started at `I₁` with `x = x₀`, the scheme halts with final value `v`. -/
def HaltsWith {D : Type} (S : IanovScheme) (F : ℕ → D → D) (P : ℕ → D → Bool) (x₀ v : D) :
    Prop :=
  ∃ n : ℕ, S[((step S F P)^[n] (0, x₀)).1]? = some (2, 0, 0, 0) ∧
    ((step S F P)^[n] (0, x₀)).2 = v

/-- The two schemes are not strongly equivalent: under some domain, interpretation and
initial value, both halt with different final values, or exactly one of them halts. -/
def StrongInequivalenceOfIanovSchemesFeasible
    (i : StrongInequivalenceOfIanovSchemesInstance) : Prop :=
  ∃ (D : Type) (F : ℕ → D → D) (P : ℕ → D → Bool) (x₀ : D),
    (∃ v w, HaltsWith i.2.2.1 F P x₀ v ∧ HaltsWith i.2.2.2 F P x₀ w ∧ v ≠ w) ∨
      ((∃ v, HaltsWith i.2.2.1 F P x₀ v) ∧ ¬ ∃ w, HaltsWith i.2.2.2 F P x₀ w) ∨
      ((¬ ∃ v, HaltsWith i.2.2.1 F P x₀ v) ∧ ∃ w, HaltsWith i.2.2.2 F P x₀ w)

open Classical in
/-- STRONG INEQUIVALENCE OF IANOV SCHEMES as a decision problem over bitstrings. -/
noncomputable def strongInequivalenceOfIanovSchemesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := StrongInequivalenceOfIanovSchemesInstance) x with
  | some i => decide (WellFormed i ∧ StrongInequivalenceOfIanovSchemesFeasible i)
  | none => false

/-- **STRONG INEQUIVALENCE OF IANOV SCHEMES is NP-complete.** Source: Garey and Johnson
(1979), [PO16]; Constable, Hunt and Sahni (1980); Rutledge (1964). -/
public theorem_wanted strongInequivalenceOfIanovSchemes_npComplete :
    strongInequivalenceOfIanovSchemesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L strongInequivalenceOfIanovSchemesDec

end MetaMathlibExt.Complexity.NPComplete.StrongInequivalenceOfIanovSchemes
