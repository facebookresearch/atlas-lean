/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Continuous integer-valued functions on a compact space (Kourovka Notebook Problem 2.36)

Kourovka Notebook, Archive of Solved Problems, Problem 2.36 (V. I. Kuz'minov; question of J. de
Groot): is the group of all continuous integer-valued functions on a compact space free abelian?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

namespace MathlibExt.Algebra.ContinuousIntegerFunctionsFreeKourovka2Problem36Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 2.36 (V. I.
Kuz'minov; question of J. de Groot). UnsolvedMath record UM-00700109 (`KOU-2.36`), dataset
ulamai/UnsolvedMath v1.8.0.

A compact space is a compact Hausdorff space (bicompactum), as in the Archive's argument, which maps
the Čech compactification of a discrete space onto `X`; `ℤ` carries its discrete topology. Mathlib
proves Nöbeling's theorem for profinite spaces (`LocallyConstant.freeOfProfinite`); the statement
for all compact Hausdorff spaces is in neither Mathlib nor MathlibExt.
-/

/-- Kourovka 2.36 (J. de Groot; V. I. Kuz'minov): for every compact Hausdorff space `X`, the
additive group `C(X, ℤ)` of continuous integer-valued functions on `X` is a free abelian group. -/
def continuousIntegerFunctionsFreeAbelian : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X], Module.Free ℤ C(X, ℤ)

/--
Resolved true: the Kourovka Archive answers 2.36 "Yes, it is" with Kuz'minov's 1969 argument: by
Nöbeling's theorem the bounded integer-valued functions on any set form a free abelian group, hence
so do the continuous integer-valued functions on the Čech compactification `Y` of a discrete space;
a continuous surjection `Y → X` embeds `C(X, ℤ)` into `C(Y, ℤ)`, and subgroups of free abelian
groups are free. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory:
The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem
2.36 (V. I. Kuz'minov; question of J. de Groot); resolution: G. Nöbeling, Invent. Math. 6 (1968),
41-55; V. I. Kuz'minov, 1969, Kourovka Archive, Problem 2.36: Yes; by Nöbeling the bounded
integer-valued functions on any set form a free group, so continuous integer-valued functions on the
Čech compactification Y of a discrete space form a free group, and a continuous surjection Y → X
embeds C(X, Z) into C(Y, Z) (V. I. Kuz'minov, 1969), https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted continuousIntegerFunctionsFreeAbelian_holds :
    continuousIntegerFunctionsFreeAbelian

end MathlibExt.Algebra.ContinuousIntegerFunctionsFreeKourovka2Problem36Wanted
