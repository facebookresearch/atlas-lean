/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Regular expressions with squaring: universality is EXPSPACE-complete

Source:
A. R. Meyer and L. J. Stockmeyer, "The equivalence problem for regular expressions with
squaring requires exponential space", Proceedings of the Thirteenth Annual Symposium on
Switching and Automata Theory (1972), 125-129. (The exponential-time word problem in
Stockmeyer-Meyer (STOC 1973) is membership, not universality.)
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes


@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.RegexSquaringEXPSPACEComplete

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# Regular expressions with squaring: universality is EXPSPACE-complete

Universality of regular expressions with squaring is `EXPSPACE`-complete. Regular expressions
are encoded in postfix token form over the natural numbers: `0` empty, `1` epsilon, `2`/`3` the
two characters, `4` concatenation, `5` union, `6` star, `7` squaring (`L·L`). The language is
evaluated on a stack of languages; the question is whether the result is every bitstring.
-/


/-- Kleene star of a language of bitstrings. -/
def starLang (S : Set (List Bool)) : Set (List Bool) :=
  {w | ∃ l : List (List Bool), w = l.flatten ∧ ∀ u ∈ l, u ∈ S}

/-- Concatenation of two languages of bitstrings. -/
def concatLang (S T : Set (List Bool)) : Set (List Bool) :=
  {w | ∃ u v, w = u ++ v ∧ u ∈ S ∧ v ∈ T}

/-- Evaluate a postfix regular-expression token list on a stack of languages. -/
noncomputable def evalPostfix : List ℕ → List (Set (List Bool)) → Option (Set (List Bool))
  | [], [S] => some S
  | [], _ => none
  | 0 :: rest, stack => evalPostfix rest (∅ :: stack)
  | 1 :: rest, stack => evalPostfix rest ({[]} :: stack)
  | 2 :: rest, stack => evalPostfix rest ({[false]} :: stack)
  | 3 :: rest, stack => evalPostfix rest ({[true]} :: stack)
  | 4 :: rest, S :: T :: stack => evalPostfix rest (concatLang T S :: stack)
  | 5 :: rest, S :: T :: stack => evalPostfix rest (Set.union T S :: stack)
  | 6 :: rest, S :: stack => evalPostfix rest (starLang S :: stack)
  | 7 :: rest, S :: stack => evalPostfix rest (concatLang S S :: stack)
  | _, _ => none

open Classical in
/-- Universality of a postfix regular expression with squaring. -/
noncomputable def regexUnivDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := List ℕ) x with
  | some toks => decide (evalPostfix toks [] = some Set.univ)
  | none => false

/-- **Regular expressions with squaring: universality is EXPSPACE-complete.** Source: A. R.
Meyer and L. J. Stockmeyer, "The equivalence problem for regular expressions with squaring
requires exponential space", Proceedings of the Thirteenth Annual Symposium on Switching
and Automata Theory (1972), 125-129. (The exponential-time word problem in Stockmeyer-
Meyer (STOC 1973) is membership, not universality.) -/
public theorem_wanted regex_squaring_expspace_complete :
    regexUnivDec ∈ EXPSPACE ∧ ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
      L ∈ EXPSPACE → Cslib.CookLevin.PolyManyOneRed L regexUnivDec

end MetaMathlibExt.Complexity.KeyTheorems.RegexSquaringEXPSPACEComplete
