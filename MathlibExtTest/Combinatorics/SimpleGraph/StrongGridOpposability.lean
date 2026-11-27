/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Fin.VecNotation
import MathlibExt.Combinatorics.SimpleGraph.StrongGridOpposability

open MetaMathlibExt

-- The singleton grid leaves no vertices after deletion.
example : IsAlmostOpposable (strongGrid (k := 1) (fun _ => 1)) :=
  isAlmostOpposable_strongGrid (by decide) _ (fun _ => by decide)

-- An odd side has one middle vertex; an even side has two.
example : IsAlmostOpposable (strongGrid (k := 1) (fun _ => 5)) :=
  isAlmostOpposable_strongGrid (by decide) _ (fun _ => by decide)

example : IsAlmostOpposable (strongGrid (k := 1) (fun _ => 4)) :=
  isAlmostOpposable_strongGrid (by decide) _ (fun _ => by decide)

example : IsAlmostOpposable (strongGrid ![3, 4]) :=
  isAlmostOpposable_strongGrid (by decide) _ (by decide)

-- Strong adjacency allows diagonal steps, but not jumps or loops.
example : (strongGrid (k := 2) (fun _ => 3)).Adj ![0, 0] ![1, 1] := by decide

example : ¬ (strongGrid (k := 2) (fun _ => 3)).Adj ![0, 0] ![1, 2] := by decide

example : ¬ (strongGrid (k := 2) (fun _ => 3)).Adj ![0, 0] ![0, 0] := by decide
