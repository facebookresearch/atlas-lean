/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact finite assembly of the original-source terminal right-coset program. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC522CosetRaw
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC522CosetSources

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Literal chronological program decoded only after every exact finite bound is proved. -/
def y522CosetProgram : Y522CosetProgram (Fin 1806) (Fin 1863) (Fin 10) 10296 :=
  y522RawCosetProgram 1806 1863 10 y522CosetRawData y522CosetRawData_allowed

/-- The unchanged exact coset checker, using independently valid original-source equations. -/
def y522CosetCheckAt (i : Fin 10296) : Prop :=
  y522CosetProgramChecked y522CosetSourcesData y522CosetFixedEquation y522CosetProgram i

/-- Literal finite program checks are decidable by exact source and word computation. -/
instance y522CosetCheckAtDecidable (i : Fin 10296) : Decidable (y522CosetCheckAt i) := by
  unfold y522CosetCheckAt y522CosetProgramChecked
  infer_instance

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
