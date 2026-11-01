/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact finite assembly of the original-source C322-parabolic right-coset program. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422CosetRaw
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422CosetSources

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Literal chronological program decoded only after every exact finite bound is proved. -/
def y422CosetProgram : Y522CosetProgram (Fin 9042) (Fin 9079) (Fin 8) 41827 :=
  y522RawCosetProgram 9042 9079 8 y422CosetRawData y422CosetRawData_allowed

/-- The unchanged exact coset checker, using independently valid original-source equations. -/
def y422CosetCheckAt (i : Fin 41827) : Prop :=
  y522CosetProgramChecked y422CosetSourcesData y422CosetFixedEquation y422CosetProgram i

/-- Literal finite program checks are decidable by exact source and word computation. -/
instance y422CosetCheckAtDecidable (i : Fin 41827) : Decidable (y422CosetCheckAt i) := by
  unfold y422CosetCheckAt y522CosetProgramChecked
  infer_instance

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
