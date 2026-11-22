/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Downward Löwenheim–Skolem
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.ModelTheory.Semantics

@[expose] public section

namespace Cslib.Logic.DownwardLSWanted

open FirstOrder FirstOrder.Language

/-- Downward Löwenheim–Skolem: every theory in a countable language with an infinite
model has a countably infinite model. The countability of the language is necessary:
a language with uncountably many constants together with axioms saying every two
distinct constants are unequal has an infinite model but no countable model. The
upward direction is Mathlib's
`FirstOrder.Language.Theory.exists_large_model_of_infinite_model` (used directly; no
CSLibExt wrapper is kept, since a wrapper added no conclusion).
Source: H. Enderton, A Mathematical Introduction to Logic, 2nd ed., Academic Press, 2001,
§2.7; L. Löwenheim, "Über Möglichkeiten im Relativkalkül", Mathematische Annalen 76, 1915,
447-470; T. Skolem, "Logisch-kombinatorische Untersuchungen über die Erfüllbarkeit oder
Beweisbarkeit mathematischer Sätze nebst einem Theorem über dichte Mengen", Skrifter utgit
av Videnskapsselskapet i Kristiania, 1920. -/
public theorem_wanted downward_lowenheim_skolem {L : FirstOrder.Language} [Countable L.Symbols]
    {T : L.Theory}
    (h : ∃ M : Type, ∃ _ : L.Structure M, Infinite M ∧ Theory.Model (M := M) T) :
    ∃ N : Type, ∃ _ : L.Structure N, Countable N ∧ Infinite N ∧ Theory.Model (M := N) T

end Cslib.Logic.DownwardLSWanted
