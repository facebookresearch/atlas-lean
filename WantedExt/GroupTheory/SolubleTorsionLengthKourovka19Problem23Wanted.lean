/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Soluble groups of torsion length greater than two (Kourovka Notebook Problem 19.23)

Kourovka Notebook, Archive of Solved Problems, Problem 19.23 (M. Chiodo, R. Vyas): `Tor₁(G)` is the
normal closure of the torsion elements of `G`, `Tor_{i+1}(G)` the preimage of `Tor₁(G / Tor_i(G))`,
and the torsion length is the least `l ≥ 1` with `G / Tor_l(G)` torsion-free (or `ω`). Does there
exist a finitely generated, or even finitely presented, soluble group with torsion length greater
than `2`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.FinitelyPresentedGroup
public import Mathlib.GroupTheory.Solvable

@[expose] public section

namespace MathlibExt.GroupTheory.SolubleTorsionLengthKourovka19Problem23Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 19.23 (M.
Chiodo, R. Vyas). UnsolvedMath record UM-00701571 (`KOU-19.23`), dataset ulamai/UnsolvedMath v1.8.0.

The stronger alternative (finitely presented) is stated, with Mathlib's `Group.IsFinitelyPresented`.
`Tor_{i+1}(G)` is written as the normal closure of the elements with a positive power in `Tor_i(G)`,
which is the preimage of `Tor₁(G / Tor_i(G))`. Torsion length greater than `2` means `G / Tor₂(G)`
is not torsion-free (if `G / Tor₁(G)` were torsion-free, `Tor₂(G) = Tor₁(G)`).
-/

/-- The torsion series of Chiodo and Vyas: `Tor₀(G) = 1` and `Tor_{i+1}(G)` is the normal closure of
the elements having a positive power in `Tor_i(G)`. This is the preimage of `Tor₁(G / Tor_i(G))`,
the normal closure of the torsion elements of `G / Tor_i(G)`, since normal closures commute with
the quotient map and `Tor_i(G)` lies in that set. -/
def torsionSeries (G : Type*) [Group G] : ℕ → Subgroup G
  | 0 => ⊥
  | i + 1 => Subgroup.normalClosure {g | ∃ n : ℕ, 0 < n ∧ g ^ n ∈ torsionSeries G i}

/-- `G` has torsion length greater than `2`: `G / Tor₂(G)` is not torsion-free (then
`G / Tor₁(G)` is not torsion-free either, so neither `1` nor `2` is the torsion length). -/
def TorsionLengthGtTwo (G : Type*) [Group G] : Prop :=
  ∃ g : G, g ∉ torsionSeries G 2 ∧ ∃ n : ℕ, 0 < n ∧ g ^ n ∈ torsionSeries G 2

/-- Kourovka 19.23 (M. Chiodo, R. Vyas), in its stronger form: there is a finitely presented
soluble group of torsion length greater than `2`. -/
def existsFinitelyPresentedSolubleTorsionLengthGtTwo : Prop :=
  ∃ (G : Type) (_ : Group G), Group.IsFinitelyPresented G ∧ Group.IsSolvable G ∧
    TorsionLengthGtTwo G

/--
Resolved true: the Kourovka Archive answers 19.23 "Yes, such groups exist"; Leary and Minasyan
(Theorem 2.14) construct polycyclic groups, which are finitely presented and soluble, of every
torsion length `n ≥ 1`, in particular of torsion length `3`. Source: E. I. Khukhro and V. D. Mazurov
(eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49
(2026), Archive of Solved Problems, Problem 19.23 (M. Chiodo, R. Vyas); resolution: I. J. Leary and
A. Minasyan, A note on torsion length and torsion subgroups, J. Group Theory 26 (2023), no. 4,
741-750 (arXiv:2112.14546), Theorem 2.14: for every integer n ≥ 1 there is a polycyclic group of
torsion length n (their torsion length counts G₀ = G, G_{n+1} = G_n / Tor(G_n) from 0 and agrees
with the Notebook's for n ≥ 1); Kourovka Archive, Problem 19.23: Yes, such groups exist,
https://arxiv.org/abs/2112.14546.
-/
public theorem_wanted existsFinitelyPresentedSolubleTorsionLengthGtTwo_holds :
    existsFinitelyPresentedSolubleTorsionLengthGtTwo

end MathlibExt.GroupTheory.SolubleTorsionLengthKourovka19Problem23Wanted
