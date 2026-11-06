/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fin.VecNotation

/-! Little-endian packing of 64-bit words into one natural number, for fast finite tables. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Little-endian packing of 64-bit words into one natural number. -/
def generatedFeasibleAmbientTenthPack (ws : List ℕ) : ℕ := ws.foldr (fun w acc => w + acc *
    18446744073709551616) 0

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
