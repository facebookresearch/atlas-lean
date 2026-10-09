/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Quantum.Grover.IterationBounds

/-!
# Grover search

This is the public entry point for the finite real-amplitude formalization of
standard Grover search with a fixed, nonempty proper oracle-marked subset. The
standard floor iteration choice assumes that the subset's cardinality is known,
not its members.
-/
