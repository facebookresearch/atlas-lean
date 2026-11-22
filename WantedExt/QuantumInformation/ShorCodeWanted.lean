/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import CSLibExt.Coding.ShorCode

/-!
# Shor's code has distance three (wanted)

## Sources

J. Preskill, *Lecture Notes for Physics 229: Quantum Information and Computation*, Chapter 7
(Caltech, 1998; https://www.preskill.caltech.edu/ph229/notes/chap7.pdf), Sections 7.1 and 7.3.1.

D. Gottesman, *Stabilizer codes and quantum error correction*, PhD thesis, Caltech (1997),
arXiv:quant-ph/9705052, Section 3.1.
-/

@[expose] public section

open scoped Matrix
open Cslib.CodingTheory.CSS Cslib.CodingTheory.Shor Cslib.CodingTheory.QuantumCode

namespace Cslib.CodingTheory.ShorCodeWanted

/-- **Shor's code has distance three.** Every Pauli operator `X^a Z^b` on nine qubits of weight at
most two satisfies `⟨x̄| X^a Z^b |ȳ⟩ = λ δ_{xy}` for some scalar `λ` and the two Shor codewords
`x, y ∈ F₂` (which have equal norms), and some Pauli operator of weight three violates this. By
the definition of J. Preskill, Ph219 lecture notes, Chapter 7, equation (7.34) (the distance is
the minimum weight of a violating Pauli operator), Shor's code is a `[[9, 1, 3]]` code
(D. Gottesman, PhD thesis (1997), Section 3.1: "The distance of this code is in fact three"); by
Preskill's Section 7.3.1 it corrects any error on one qubit. The weight-three half is proved as
`Cslib.CodingTheory.Shor.shorCodeword_violation_weight_three`. -/
theorem_wanted shorCodeword_distance_three :
    (∀ a b : Fin 9 → ZMod 2, pauliWeight a b < 3 → ∃ l : ℂ, ∀ x y : ZMod 2,
      star (shorCodeword x) ⬝ᵥ (pauli a b *ᵥ shorCodeword y) = if x = y then l else 0) ∧
    ∃ a b : Fin 9 → ZMod 2, pauliWeight a b = 3 ∧ ¬ ∃ l : ℂ, ∀ x y : ZMod 2,
      star (shorCodeword x) ⬝ᵥ (pauli a b *ᵥ shorCodeword y) = if x = y then l else 0

end Cslib.CodingTheory.ShorCodeWanted
