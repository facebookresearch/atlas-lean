/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM COMPATIBLE CHARACTER SET for binary characters: definitions

Source:
W. H. E. Day and D. Sankoff, "Computational complexity of inferring phylogenies by
compatibility", Systematic Zoology 35(2) (1986), 224-229, doi:10.2307/2413432 (the four basic
variants of the compatibility problem, cladistic or qualitative and binary or unconstrained
characters, are NP-complete; this is the qualitative binary variant);
G. F. Estabrook, C. S. Johnson Jr. and F. R. McMorris, "A mathematical foundation for the
analysis of cladistic character compatibility", Mathematical Biosciences 29 (1976), 181-187,
doi:10.1016/0025-5564(76)90035-3 (binary characters fit one tree iff they are pairwise
compatible).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Bioinformatics.Phylogenetics.Splits

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumCompatibleBinaryCharacters

open Cslib.Bioinformatics.Phylogenetics.Splits (FourGametes)

/-- An instance: the number `n` of species, the columns of the character matrix (column `j`
lists the states of character `j` on the species), and the bound `K`. -/
abbrev MaximumCompatibleBinaryCharactersInstance := ℕ × List (List Bool) × ℕ

/-- The characters of the instance, one per column. -/
abbrev Character (i : MaximumCompatibleBinaryCharactersInstance) : Type := Fin i.2.1.length

/-- Character `j` as a function from the species `Fin n` to states. -/
def character (i : MaximumCompatibleBinaryCharactersInstance) (j : Character i) :
    Fin i.1 → Bool :=
  fun s => (i.2.1.get j).getD s false

/-- Well-formedness of an instance: there are at least two species, and every column has one
state per species. -/
def WellFormed (i : MaximumCompatibleBinaryCharactersInstance) : Prop :=
  2 ≤ i.1 ∧ ∀ col ∈ i.2.1, col.length = i.1

/-- Some set of at least `K` characters, no two of which show all four gametes. -/
def MaximumCompatibleBinaryCharactersFeasible
    (i : MaximumCompatibleBinaryCharactersInstance) : Prop :=
  ∃ S : Finset (Character i), i.2.2 ≤ S.card ∧
    ∀ j ∈ S, ∀ k ∈ S, ¬ FourGametes (character i j) (character i k)

open Classical in
/-- MAXIMUM COMPATIBLE CHARACTER SET for binary characters as a decision problem over
bitstrings. -/
noncomputable def maximumCompatibleBinaryCharactersDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaximumCompatibleBinaryCharactersInstance) x with
  | some i => decide (WellFormed i ∧ MaximumCompatibleBinaryCharactersFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MaximumCompatibleBinaryCharacters
