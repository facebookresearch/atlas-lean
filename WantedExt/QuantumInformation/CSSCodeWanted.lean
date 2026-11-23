/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import CSLibExt.Coding.CSSCode
public import MathlibExt.QuantumInformation.Finite.KnillLaflamme
public import Mathlib.InformationTheory.Hamming

/-!
# CSS codes correct `⌊(d - 1) / 2⌋` errors (wanted)

## Source

A. R. Calderbank and P. W. Shor, *Good quantum error-correcting codes exist*, Phys. Rev. A 54
(1996), 1098–1105 (arXiv:quant-ph/9512032), Section III (statement before equation (5)) and
Section IV.
-/

@[expose] public section

open scoped Matrix
open Cslib.CodingTheory Cslib.CodingTheory.LinearCode Cslib.CodingTheory.CSS
  MathlibExt.QuantumInformation.Finite.KnillLaflamme

namespace Cslib.CodingTheory.CSSWanted

/-- **CSS codes correct `⌊(d - 1) / 2⌋` errors.** Let `C₂ ⊆ C₁ ⊆ F₂ⁿ` be binary linear codes such
that every nonzero word of `C₁` and every nonzero word of `C₂^⊥` has Hamming weight at least
`d`. Let `P` be the orthogonal projector onto the CSS code `Q_{C₁, C₂}`, the span of the
codewords `|c_w⟩` with `w ∈ C₂^⊥`. Then every Pauli error `X^a Z^b` acting on at most
`t = ⌊(d - 1) / 2⌋` qubits (that is, `2 |supp a ∪ supp b| + 1 ≤ d`) is correctable on the code,
all by one recovery channel (A. R. Calderbank and P. W. Shor, Phys. Rev. A 54 (1996), Section III:
"if `C₁` and `C₂^⊥` have minimum distance `d`, then the quantum code `Q_{C₁,C₂}` can correct
`t = ⌊(d-1)/2⌋` errors", proved in Section IV). Calderbank and Shor allow an arbitrary
decoherence of the `t` qubits; its Kraus operators are linear combinations of such Pauli
operators, and correctable families are closed under linear combinations (E. Knill and
R. Laflamme, Phys. Rev. A 55 (1997), Theorem 3.1), so the Pauli form is equivalent. -/
theorem_wanted isCorrectable_css {n d : ℕ} (C₁ C₂ : LinearCode (ZMod 2) (Fin n))
    [DecidablePred (· ∈ C₁)] (hC : C₂ ≤ C₁)
    (hd₁ : ∀ c ∈ C₁, c ≠ 0 → d ≤ hammingNorm c)
    (hd₂ : ∀ c ∈ dual C₂, c ≠ 0 → d ≤ hammingNorm c)
    (P : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) (hP : Pᴴ = P) (hPP : P * P = P)
    (hrange : LinearMap.range (Matrix.toLin' P) =
      Submodule.span ℂ (codeword C₁ '' (dual C₂ : Set (Fin n → ZMod 2)))) :
    IsCorrectable P (fun e : {e : (Fin n → ZMod 2) × (Fin n → ZMod 2) //
        2 * (Finset.univ.filter fun i => e.1 i ≠ 0 ∨ e.2 i ≠ 0).card + 1 ≤ d} =>
      pauli e.1.1 e.1.2)

end Cslib.CodingTheory.CSSWanted
