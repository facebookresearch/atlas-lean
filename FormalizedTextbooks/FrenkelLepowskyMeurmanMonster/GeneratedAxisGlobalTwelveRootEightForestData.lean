/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fin.VecNotation
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthForestWords

/-! Exact binary column data for the four root-eight forest letters: the canonical transport
conjugates of the two reduced Mathieu words, the point mover and the mate orientation
(Höhn–Seysen, arXiv:2508.01037, §3.2). Only finite arithmetic is stated here; the identification
with the binary actions of genuine stabilizer elements is proved separately. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Forward hyperbolic binary columns of the four root-eight forest letters. -/
def rootEightForestColumns : Fin 4 → Fin 24 → ℕ :=
  ![![13963912, 4527759, 4, 6465074, 9090586, 8850811, 16364961, 7537410, 9016124, 8554110,
    14656746, 10394817, 6370387, 12434620, 3202926, 5389394, 13281548, 4920909, 4719439, 1353183,
    503904, 635088, 13669500, 6689006],
  ![5963784, 4980751, 4, 4325377, 1970336, 2724080, 2695312, 3616992, 2693552, 1966800, 46080,
    2048, 40960, 8192, 26624, 12288, 3540992, 1769472, 2754560, 4130816, 1048576, 2097152,
    4194304, 9437396],
  ![6135975, 9574634, 11539973, 9442920, 10170603, 5522747, 11201427, 4800098, 912146, 2906843,
    8939064, 9373083, 8627585, 3023053, 288297, 10707607, 16622762, 16320978, 370994, 15796467,
    15537351, 9371802, 3256655, 2808848],
  ![9407975, 14058880, 4, 3553620, 7214, 2406842, 13284829, 12851706, 2138892, 13795370, 11283494,
    7094004, 268200, 7018128, 14016112, 4131297, 9342438, 15405149, 9212348, 9321819, 2011353,
    9438215, 12925591, 13341852]]

/-- The same columns as lists, indexed by natural numbers. -/
def rootEightForestLetterColsNat : ℕ → List ℕ
  | 0 => [
    13963912, 4527759, 4, 6465074, 9090586, 8850811, 16364961, 7537410, 9016124, 8554110,
    14656746, 10394817, 6370387, 12434620, 3202926, 5389394, 13281548, 4920909, 4719439, 1353183,
    503904, 635088, 13669500, 6689006]
  | 1 => [
    5963784, 4980751, 4, 4325377, 1970336, 2724080, 2695312, 3616992, 2693552, 1966800, 46080,
    2048, 40960, 8192, 26624, 12288, 3540992, 1769472, 2754560, 4130816, 1048576, 2097152,
    4194304, 9437396]
  | 2 => [
    6135975, 9574634, 11539973, 9442920, 10170603, 5522747, 11201427, 4800098, 912146, 2906843,
    8939064, 9373083, 8627585, 3023053, 288297, 10707607, 16622762, 16320978, 370994, 15796467,
    15537351, 9371802, 3256655, 2808848]
  | 3 => [
    9407975, 14058880, 4, 3553620, 7214, 2406842, 13284829, 12851706, 2138892, 13795370, 11283494,
    7094004, 268200, 7018128, 14016112, 4131297, 9342438, 15405149, 9212348, 9321819, 2011353,
    9438215, 12925591, 13341852]
  | _ => []

/-- The binary columns of a root-eight forest letter. -/
def rootEightForestLetterCols (g : Fin 4) : List ℕ := rootEightForestLetterColsNat g.val

set_option maxRecDepth 100000 in
-- The column lists are the column tables.
theorem rootEightForestLetterCols_eq : ∀ g : Fin 4,
    rootEightForestLetterCols g = List.ofFn (rootEightForestColumns g) := by
  decide +kernel

/-- The binary action of a letter word (the last letter acts first). -/
def rootEightForestWordApply (w : List (Fin 4)) (v : ℕ) : ℕ :=
  w.foldr (fun g m => tenthForestApplyCols (rootEightForestLetterCols g) m) v

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
