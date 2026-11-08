/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Matrix.Strassen.Basic
public import CSLibExt.Algorithms.Lean.Matrix.Strassen.Correctness
public import CSLibExt.Algorithms.Lean.Matrix.Strassen.Costs

/-!
# Strassen matrix accumulation

The source-shaped executor computes the saved accumulator plus the matrix product
for power-of-two dimensions, with exact counts of actual scalar operations.
-/
