/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.Order.Floor.Ring
public import MathlibExt.Dynamics.NExpansionGaps
public import MathlibExt.Dynamics.NExpansionGapsPointLtIff

/-!
# Intervals of N-expansions with many gaps

Statements from Jaap de Jonge, *Intervals of N-Expansions with Many Gaps*, INTEGERS 26 (2026),
Article A75. The N-expansion map and its digit with three basic properties, the alternation in
order of orbits with the same digits, the ideal period words (Definition 7), their first values
and their formulas for digit lengths and block counts are in `MathlibExt.Dynamics.NExpansionGaps`,
which this module imports. The comparison and orbit minimality of ideal periodic points are in
`MathlibExt.Dynamics.NExpansionGapsPointLtIff`, which this module also imports.
-/
