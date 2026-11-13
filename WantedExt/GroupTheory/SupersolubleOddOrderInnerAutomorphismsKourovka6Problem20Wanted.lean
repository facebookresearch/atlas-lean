/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Supersoluble groups of odd order with only inner automorphisms (Kourovka Notebook Problem 6.20)

Kourovka Notebook, Archive of Solved Problems, Problem 6.20 (V. D. Mazurov): does there exist a
supersoluble group of odd order, all of whose automorphisms are inner?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.SetTheory.Cardinal.Finite
public import WantedExt.GroupTheory.AbnormalSupersolubleFactorizationKourovka19Problem100Wanted

@[expose] public section

namespace MathlibExt.GroupTheory.SupersolubleOddOrderInnerAutomorphismsKourovka6Problem20Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 6.20 (V. D.
Mazurov). UnsolvedMath record UM-00700367 (`KOU-6.20`), dataset ulamai/UnsolvedMath v1.8.0.

Supersoluble is `IsSupersoluble` of the Kourovka 19.100 module (a normal series with cyclic
factors). The group must be non-trivial: the trivial group has only the identity automorphism, which
is inner. Groups of odd order are finite here.
-/

open MathlibExt.GroupTheory.AbnormalSupersolubleFactorizationKourovka19Problem100Wanted
  (IsSupersoluble)

/-- Kourovka 6.20 (V. D. Mazurov): there is a non-trivial finite supersoluble group of odd order all
of whose automorphisms are inner. -/
def existsSupersolubleOddOrderAllAutomorphismsInner : Prop :=
  ∃ (G : Type) (_ : Group G) (_ : Finite G), Nontrivial G ∧ Odd (Nat.card G) ∧ IsSupersoluble G ∧
    ∀ φ : G ≃* G, ∃ g : G, φ = MulAut.conj g

/--
Resolved true: the Kourovka Archive answers 6.20 "Yes, there does", citing Hartley and Robinson
(1980): some non-trivial finite supersoluble group of odd order has only inner automorphisms.
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 6.20 (V. D.
Mazurov); resolution: B. Hartley and D. J. S. Robinson, On finite complete groups, Arch. Math. 35
(1980), 67-74, Kourovka Archive, Problem 6.20: Yes, there does (Hartley, Robinson),
https://doi.org/10.1007/BF01235320.
-/
public theorem_wanted existsSupersolubleOddOrderAllAutomorphismsInner_holds :
    existsSupersolubleOddOrderAllAutomorphismsInner

end MathlibExt.GroupTheory.SupersolubleOddOrderInnerAutomorphismsKourovka6Problem20Wanted
