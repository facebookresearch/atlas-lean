/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The central lozenge of the 2n - 1, 2n, 2n - 1 hexagon (Propp, Problem 1)

J. Propp, Twenty open problems in enumeration of matchings, Problem 1: show that in the `2n - 1, 2n,
2n - 1` semiregular hexagon, the central location (consisting of the two innermost triangles) is
covered by a lozenge in exactly one-third of the tilings. (Equivalently: if one chooses a random
perfect matching of the dual graph, the probability that the central edge is contained in the
matching is exactly 1/3.)
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import MathlibExt.Combinatorics.CentralLozengeOneThirdAMR122Problem0001
