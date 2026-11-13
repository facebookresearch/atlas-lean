/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Central elements of quasi-finite groups (Kourovka Notebook Problem 9.82)

Kourovka Notebook, Archive of Solved Problems, Problem 9.82 (V. P. Shunkov): an infinite group all
of whose proper subgroups are finite is called quasi-finite. Is it true that an element of a
quasi-finite group `G` is central if and only if it is contained in infinitely many subgroups of
`G`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Finite.Defs
public import Mathlib.GroupTheory.Subgroup.Center

@[expose] public section

namespace MathlibExt.GroupTheory.QuasiFiniteCentralElementsKourovka9Problem82Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 9.82 (V. P.
Shunkov). UnsolvedMath record UM-00700615 (`KOU-9.82`), dataset ulamai/UnsolvedMath v1.8.0.

Quasi-finite: `G` infinite and every proper subgroup finite. The target is the "if and only if" for
every element; the Archive does not say which direction fails.
-/

/-- `G` is quasi-finite: `G` is infinite and every proper subgroup of `G` is finite. -/
def IsQuasiFinite (G : Type*) [Group G] : Prop :=
  Infinite G ∧ ∀ H : Subgroup G, H ≠ ⊤ → Finite H

/-- Kourovka 9.82 (V. P. Shunkov): an element of a quasi-finite group `G` is central if and only if
it lies in infinitely many subgroups of `G`. -/
def quasiFiniteCentralIffInfinitelyMany : Prop :=
  ∀ (G : Type) [Group G], IsQuasiFinite G →
    ∀ g : G, g ∈ Subgroup.center G ↔ {H : Subgroup G | g ∈ H}.Infinite

/--
Resolved false: the Kourovka Archive answers 9.82 "No", citing Lossov (VINITI deposit 5529-V89): in
some quasi-finite group the central elements are not exactly the elements lying in infinitely many
subgroups. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 9.82
(V. P. Shunkov); resolution: K. I. Lossov, deposited at VINITI, no. 5529-V89, Moscow, 1988
(Russian), Kourovka Archive of Solved Problems, Problem 9.82: No,
https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted quasiFiniteCentralIffInfinitelyMany_refuted :
    ¬ quasiFiniteCentralIffInfinitelyMany

end MathlibExt.GroupTheory.QuasiFiniteCentralElementsKourovka9Problem82Wanted
