/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Non-abelian varieties with abelian finite groups (Kourovka Notebook Problem 4.73)

Kourovka Notebook, Archive of Solved Problems, Problem 4.73 (A. L. Shmel'kin): does there exist a
non-abelian variety of groups a) all of whose finite groups are abelian? b) all of whose periodic
groups are abelian?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Torsion
public import WantedExt.GroupTheory.FormationVarietyPGroupsKourovka11Problem21Wanted

@[expose] public section

namespace MathlibExt.GroupTheory.NonAbelianVarietyAbelianFiniteGroupsKourovka4Problem73Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 4.73 (A. L.
Shmel'kin). UnsolvedMath record UM-00700280 (`KOU-4.73`), dataset ulamai/UnsolvedMath v1.8.0.

Laws and varieties are `SatisfiesLaws` of the Kourovka 11.21 entry, reused here: a law is a word of
`FreeGroup ℕ`, the variety defined by a set `W` of laws consists of the groups in which every law of
`W` holds, and every variety arises this way. A variety is non-abelian when it contains a
non-abelian group; periodic means that every element has finite order (`IsMulTorsion`). Part (b)
implies part (a).
-/

open MathlibExt.GroupTheory.FormationVarietyPGroupsKourovka11Problem21Wanted (SatisfiesLaws)

/-- Kourovka 4.73(a) (A. L. Shmel'kin): there is a non-abelian variety of groups all of whose
finite groups are abelian. -/
def existsNonAbelianVarietyFiniteGroupsAbelian : Prop :=
  ∃ W : Set (FreeGroup ℕ),
    (∃ (G : Type) (_ : Group G), SatisfiesLaws W G ∧ ∃ a b : G, a * b ≠ b * a) ∧
      ∀ (G : Type) [Group G] [Finite G], SatisfiesLaws W G → ∀ a b : G, a * b = b * a

/-- Kourovka 4.73(b) (A. L. Shmel'kin): there is a non-abelian variety of groups all of whose
periodic groups are abelian. -/
def existsNonAbelianVarietyPeriodicGroupsAbelian : Prop :=
  ∃ W : Set (FreeGroup ℕ),
    (∃ (G : Type) (_ : Group G), SatisfiesLaws W G ∧ ∃ a b : G, a * b ≠ b * a) ∧
      ∀ (G : Type) [Group G], IsMulTorsion G → SatisfiesLaws W G → ∀ a b : G, a * b = b * a

/--
Resolved true: the Kourovka Archive answers 4.73(a) "Yes, there does", citing Ol'shanskii, Varieties
in which all finite groups are abelian (Math. USSR-Sb. 54 (1986), 57-80,
https://doi.org/10.1070/SM1986v054n01ABEH002960). Source: E. I. Khukhro and V. D. Mazurov (eds.),
Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026),
Archive of Solved Problems, Problem 4.73 (A. L. Shmel'kin); resolution: (a) A. Yu. Ol'shanskii,
Varieties in which all finite groups are abelian, Math. USSR-Sb. 54 (1986), 57-80; (b) S. V. Ivanov
and A. M. Storozhev, On varieties of groups in which all periodic groups are abelian, Contemp. Math.
360 (2004), 55-62, and P. A. Kozhevnikov, On varieties of groups of large odd exponent, Dep.
1612-V00, VINITI, Moscow, 2000, Kourovka Archive, Problem 4.73: a) Yes, there does (Ol'shanskii); b)
Yes, there does (Kozhevnikov; Ivanov-Storozhev); Ol'shanskii's abstract: the problem of the
existence of a variety that contains non-abelian groups but in which all finite groups are abelian
is solved affirmatively, the variety being given by a single two-variable identity; part (b) is the
title of Ivanov and Storozhev's paper, https://doi.org/10.1090/conm/360/06570.
-/
public theorem_wanted existsNonAbelianVarietyFiniteGroupsAbelian_holds :
    existsNonAbelianVarietyFiniteGroupsAbelian

/--
Resolved true: the Kourovka Archive answers 4.73(b) "Yes, there does", citing Kozhevnikov (VINITI
deposit, 2000) and Ivanov and Storozhev, On varieties of groups in which all periodic groups are
abelian (Contemp. Math. 360 (2004), 55-62). Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of
Solved Problems, Problem 4.73 (A. L. Shmel'kin); resolution: (a) A. Yu. Ol'shanskii, Varieties in
which all finite groups are abelian, Math. USSR-Sb. 54 (1986), 57-80; (b) S. V. Ivanov and A. M.
Storozhev, On varieties of groups in which all periodic groups are abelian, Contemp. Math. 360
(2004), 55-62, and P. A. Kozhevnikov, On varieties of groups of large odd exponent, Dep. 1612-V00,
VINITI, Moscow, 2000, Kourovka Archive, Problem 4.73: a) Yes, there does (Ol'shanskii); b) Yes,
there does (Kozhevnikov; Ivanov-Storozhev); Ol'shanskii's abstract: the problem of the existence of
a variety that contains non-abelian groups but in which all finite groups are abelian is solved
affirmatively, the variety being given by a single two-variable identity; part (b) is the title of
Ivanov and Storozhev's paper, https://doi.org/10.1090/conm/360/06570.
-/
public theorem_wanted existsNonAbelianVarietyPeriodicGroupsAbelian_holds :
    existsNonAbelianVarietyPeriodicGroupsAbelian

end MathlibExt.GroupTheory.NonAbelianVarietyAbelianFiniteGroupsKourovka4Problem73Wanted
