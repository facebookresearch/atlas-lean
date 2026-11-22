/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Tests for Rabin and Streett automata and parity conversions
-/
module

public import CSLibExt.Computability.Automata.NA.RabinStreett

/-!
# Tests for Rabin and Streett automata and parity conversions

A one-state parity automaton with priority `2` (even): its Rabin, Streett,
and Muller presentations accept the same language, and a one-pair Rabin
automaton converts to Muller with the same language.
-/

@[expose] public section

namespace Cslib.Automata.NA.RabinStreett.Tests

open ωAcceptor

/-- One state, all transitions present, priority `2` everywhere. -/
def twoParity : Parity Unit Bool where
  Tr _ _ _ := True
  start := {()}
  priority _ := 2

/-- The Rabin presentation of the parity automaton accepts the same language. -/
example : language twoParity.toRabin = language twoParity :=
  Parity.language_toRabin twoParity

/-- The Streett presentation of the parity automaton accepts the same language. -/
example : language twoParity.toStreett = language twoParity :=
  Parity.language_toStreett twoParity

/-- The Muller presentation of the parity automaton accepts the same language. -/
example : language twoParity.toMuller = language twoParity :=
  Parity.language_toMuller twoParity

/-- One Rabin pair: visit `()` infinitely often, visit nothing finitely often. -/
def oneRabin : Rabin Unit Bool where
  Tr _ _ _ := True
  start := {()}
  accept := {({()} , ∅)}

/-- The Muller presentation of the one-pair Rabin automaton accepts the same language. -/
example : language oneRabin.toMuller = language oneRabin :=
  Rabin.language_toMuller oneRabin

end Cslib.Automata.NA.RabinStreett.Tests
