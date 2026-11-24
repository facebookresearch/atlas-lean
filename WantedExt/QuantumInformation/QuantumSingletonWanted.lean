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
# The quantum Singleton bound (wanted)

An `[[n, k, d]]` quantum code with `k ≥ 1` satisfies `n - k ≥ 2 (d - 1)`. Preskill proves it by
maximally entangling the code with a `k`-qubit reference system, splitting the `n` qubits into two
blocks of `d - 1` qubits and the rest, and combining the subadditivity of the von Neumann entropy
with the fact that no block of `d - 1` qubits carries information about the encoded state.

## Source

J. Preskill, *Lecture Notes for Physics 229: Quantum Information and Computation*, Chapter 7
(Caltech, 1998; https://www.preskill.caltech.edu/ph229/notes/chap7.pdf), Section 7.8.3,
equations (7.103)–(7.112).
-/

@[expose] public section

open scoped Matrix
open Cslib.CodingTheory.QuantumCode

namespace Cslib.CodingTheory.QuantumSingletonWanted

/-- **The quantum Singleton bound.** Let `P` be the orthogonal projector onto a code of dimension
`2 ^ k`, with `k ≥ 1`, in the space of `n` qubits, and suppose the code has distance at least `d`:
every Pauli operator `X^a Z^b` of weight less than `d` satisfies `P X^a Z^b P = c P`. Then
`k + 2 (d - 1) ≤ n`, that is `n - k ≥ 2 (d - 1)` (J. Preskill, Ph219 lecture notes, Chapter 7,
Section 7.8.3, equation (7.103), proved there through equations (7.105)–(7.112)). -/
theorem_wanted quantum_singleton_bound {n k d : ℕ}
    (P : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) (hP : Pᴴ = P) (hPP : P * P = P)
    (hk : 1 ≤ k) (hdim : Module.finrank ℂ (LinearMap.range (Matrix.toLin' P)) = 2 ^ k)
    (hd : HasDistanceAtLeast P d) :
    k + 2 * (d - 1) ≤ n

end Cslib.CodingTheory.QuantumSingletonWanted
