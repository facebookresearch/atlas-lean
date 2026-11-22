/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import CSLibExt.Coding.QuantumCodeDistance

/-!
# Dimension of a stabilizer code (wanted)

A stabilizer code is the common `+1` eigenspace of an abelian subgroup `S` of the `n`-qubit Pauli
group with `-I ∉ S`. If `S` has `r` independent generators, the code has dimension `2 ^ (n - r)`:
each new generator halves the dimension, because some Pauli operator commutes with the previous
generators and anticommutes with it.

Here the generators are `M j = c j • X^{a j} Z^{b j}` with `M j * M j = 1` and pairwise commuting.
The vectors `(a j, b j) ∈ F₂ⁿ × F₂ⁿ` are linearly independent over `F₂`; this says both that no
generator is a product of the others and that no nonempty product of generators is a scalar, so
in particular `-I ∉ S`. Commutation forces `r ≤ n`, so `n - r` is not truncated.

## Sources

J. Preskill, *Lecture Notes for Physics 229: Quantum Information and Computation*, Chapter 7
(Caltech, 1998; https://www.preskill.caltech.edu/ph229/notes/chap7.pdf), Section 7.9.1,
equations (7.117)–(7.120).

D. Gottesman, *Stabilizer codes and quantum error correction*, PhD thesis, Caltech (1997),
arXiv:quant-ph/9705052, Section 3.2.
-/

@[expose] public section

open scoped Matrix
open Cslib.CodingTheory.CSS

namespace Cslib.CodingTheory.StabilizerCodeWanted

/-- **Dimension of a stabilizer code.** Let `M j = c j • X^{a j} Z^{b j}` (`j < r`) be Pauli
operators on `n` qubits, up to scalars, with `M j * M j = 1`, pairwise commuting, and with
`(a j, b j)` linearly independent over `F₂`. Then the common `+1` eigenspace
`{ψ | M j ψ = ψ for all j}` has dimension `2 ^ (n - r)` (J. Preskill, Ph219 lecture notes,
Chapter 7, Section 7.9.1: "If `S` has `n - k` generators, we can show that the code space `H_S`
has dimension `2^k`"; D. Gottesman, PhD thesis (1997), Section 3.2). -/
theorem_wanted finrank_stabilizerCode {n r : ℕ} (a b : Fin r → Fin n → ZMod 2) (c : Fin r → ℂ)
    (hsq : ∀ j, (c j • pauli (a j) (b j)) * (c j • pauli (a j) (b j)) = 1)
    (hcomm : ∀ j k, Commute (c j • pauli (a j) (b j)) (c k • pauli (a k) (b k)))
    (hind : LinearIndependent (ZMod 2) fun j => (a j, b j)) :
    Module.finrank ℂ
        (⨅ j, LinearMap.ker (Matrix.toLin' (c j • pauli (a j) (b j)) - LinearMap.id) :
          Submodule ℂ ((Fin n → ZMod 2) → ℂ)) =
      2 ^ (n - r)

end Cslib.CodingTheory.StabilizerCodeWanted
