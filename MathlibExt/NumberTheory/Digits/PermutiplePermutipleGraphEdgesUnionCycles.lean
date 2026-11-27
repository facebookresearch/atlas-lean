/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Digits.HoeySloaneCycles

/-!
# Permutiple graphs are unions of cycles (Holt)

Statements from Benjamin V. Holt, *Finding Permutiples of a Known Base and
Multiplier*, INTEGERS 25 (2025), Article A13.

`permutipleGraphEdges_union_cycles` (every edge of the graph of a permutiple is an edge of the
mother graph and lies on a directed cycle of distinct digits within the graph) is proved in
`MathlibExt.NumberTheory.Digits.HoeySloaneCycles`, where it shares the cycle argument of
`hoeySloaneWord_inputs_union_cycles`. This module re-exports it.
-/
