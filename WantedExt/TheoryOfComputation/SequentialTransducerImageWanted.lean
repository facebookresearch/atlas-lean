/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Regular languages are preserved under forward sequential transduction

Source: Berstel, "Transductions and Context-Free Languages" (1979), Chapter II, Theorem 2.1.
Source: Sakarovitch, "Elements of Automata Theory" (2009), Chapter IV, Proposition IV.2.5.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Automata.Transducers.Sequential
public import Cslib.Computability.Languages.RegularLanguage

@[expose] public section

namespace Cslib.Automata.SequentialTransducerImageWanted

open scoped Computability

/-!
# Regular languages are preserved under forward sequential transduction

The forward image of a regular language under a finite-state sequential transducer over
a finite input alphabet is regular: an `ε`-NFA over the output alphabet expands each
transducer transition into the word it outputs. The finite input alphabet hypothesis is
essential and sharp. Without it the statement is false: given any nonregular
`K : Language Out`, take `In := {w // w ∈ K}` with a one-state accepting transducer
that emits each input letter's underlying word, and the regular language of one-letter
inputs; its image is exactly `K`. With `[Finite In]` and `[Finite State]` the transducer
has only finitely many transitions, initial outputs, and final outputs, so only finitely
many output words ever occur and the expanding `ε`-NFA construction applies. This is
the forward-image counterpart of the proved preimage theorem
`SequentialTransducer.isRegular_preimage` in
`CSLibExt/Computability/Automata/Transducers/Sequential.lean`, which handles inverse
transduction; the forward direction needs the expanding `ε`-NFA construction and is
recorded here as wanted.
-/

/-- **Regular languages are preserved under forward sequential transduction.** Source:
Berstel, "Transductions and Context-Free Languages" (1979), Chapter II, Theorem 2.1. -/
public theorem_wanted sequential_transducer_image_isRegular {State In Out : Type*}
    [Finite State] [Finite In] (S : SequentialTransducer State In Out) {L : Language In}
    (hL : L.IsRegular) :
    Language.IsRegular ({ys : List Out | ∃ xs ∈ L, S.Translates xs ys} : Language Out)

end Cslib.Automata.SequentialTransducerImageWanted
