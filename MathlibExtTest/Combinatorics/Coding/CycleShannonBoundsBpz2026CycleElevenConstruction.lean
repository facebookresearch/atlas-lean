/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Coding.CycleShannonBoundsBpz2026CycleElevenConstruction
import Mathlib.Data.Fin.VecNotation

/-! # Regression tests for the eleven-cycle construction -/

namespace MathlibExt.Combinatorics.Coding.CycleShannonBoundsWanted

open MathlibExt.Combinatorics.Coding.CycleGraphCode

-- Compute coordinate differences directly on the encoded base data.
private def closeCode (x y : Fin 1331) : Bool :=
  [1, 11, 121].all fun p => ((x.val / p % 11 + 12 - y.val / p % 11) % 11 ≤ 2)

-- 131 = 10 + 11 · 0 + 121 · 1; reversing the digit order changes the word.
example : bpzC11Decode 131 = ![10, 0, 1] := by
  decide +kernel

set_option maxRecDepth 4096 in
example : bpzC11BaseWords.length = 148 ∧ bpzC11AuxWords.length = 148 ∧
    bpzC11BaseWords.Pairwise (fun x y => closeCode x y = false) ∧
    bpzC11AuxWords.Pairwise (fun x y => closeCode x y = false) := by
  decide +kernel

-- Each endpoint's closed neighbourhood in the starting code consists of its own parent.
example : bpzC11Ports.length = 3 ∧ (bpzC11Ports.map Prod.fst).Nodup ∧
    bpzC11Ports.all (fun (p, a) => (p != a) &&
      (bpzC11BaseWords.filter (closeCode p) == [p]) &&
      (bpzC11BaseWords.filter (closeCode a) == [p])) = true ∧
    bpzC11Ports.Pairwise (fun p q =>
      closeCode p.1 q.1 = false ∧ closeCode p.1 q.2 = false ∧
      closeCode p.2 q.1 = false ∧ closeCode p.2 q.2 = false) := by
  decide +kernel

private def hits (f : Fin 1331 × Fin 1331 → Fin 1331) (x : Fin 1331) : Bool :=
  bpzC11Ports.any fun p => closeCode x (f p)

example : (bpzC11AuxWords.filter (hits Prod.fst)).length = 3 ∧
    (bpzC11AuxWords.filter (hits Prod.snd)).length = 3 ∧
    (bpzC11AuxWords.filter fun x => hits Prod.fst x && hits Prod.snd x).length = 0 ∧
    (bpzC11AuxWords.filter fun x => !hits Prod.fst x && !hits Prod.snd x).length = 142 := by
  decide +kernel

-- The square of the small tuple from Example 1: one core pair, two horizontal words
-- and two vertical words. Check the words themselves, not the profile formula.
private def c5Square : Finset (Fin 2 → ZMod 5) :=
  {![2, 2], ![1, 0], ![3, 4], ![4, 1], ![0, 3]}

example : IsCycleCode 5 c5Square ∧ c5Square.card = 5 := by
  rw [isCycleCode_iff_eq_of_confusable]
  decide +kernel

-- Check the profile arithmetic independently of the dimension-174 existence theorem.
example : bpzC11Pi2 = ⟨21913, 852, 21904, 20200⟩ := by
  decide +kernel

example : bpzC11Pi58.code.toNat =
    882221744100632005674769618013933735011419532711315494280102505401018850276155712572128940587489665742428394773529899847139897 := by
  decide +kernel

example : ∃ A : Finset (Fin 174 → ZMod 11), IsCycleCode 11 A ∧ A.card = bpzC11Pi58.code.toNat :=
  bpz2026CycleElevenConstruction

end MathlibExt.Combinatorics.Coding.CycleShannonBoundsWanted
