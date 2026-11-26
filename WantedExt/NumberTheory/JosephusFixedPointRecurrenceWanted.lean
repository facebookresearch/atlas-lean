/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Nat.Nth
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import MathlibExt.NumberTheory.JosephusFixedPointInterval
public import MathlibExt.NumberTheory.JosephusFixedPointRecurrence
public import MathlibExt.NumberTheory.JosephusThreeHighExtremalSuccCases

/-!
# A recurrence formula for the fixed points of the Josephus function `J₃`

This module re-exports the proved statements.

Statements from Yunier Bello-Cruz and Roy Quintero-Contreras, *On the Recurrence Formula
for Fixed Points of the Josephus Function*, INTEGERS 24 (2024), Article A115 (preprint
arXiv:2310.12984, from which the definitions are taken). `J₃` is the existing
`MetaMathlibExt.josephus 3`. A *high extremal point* is an `n ≥ 1` with
`J₃(n) ∈ {n - 1, n}`, a *fixed point* one with `J₃(n) = n`, and a *pure* high extremal point
one with `J₃(n) = n - 1`. The paper's sequences `n_e^{(i)}` and `n_p^{(ℓ)}` (`i, ℓ ≥ 1`,
increasing) are `Nat.nth` of the corresponding predicates at the zero-based index `i - 1`.
-/
