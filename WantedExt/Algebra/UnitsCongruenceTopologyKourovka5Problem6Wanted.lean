/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Units of finitely generated domains of positive characteristic (Kourovka Notebook Problem 5.6)

Kourovka Notebook, Archive of Solved Problems, Problem 5.6 (B. A. F. Wehrfritz): if R is a finitely
generated integral domain of characteristic p > 0, does the profinite (ideal) topology of R induce
the profinite topology on the group of units of R? It does for p = 0.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Index
public import Mathlib.RingTheory.FiniteType

@[expose] public section

namespace MathlibExt.Algebra.UnitsCongruenceTopologyKourovka5Problem6Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 5.6 (B. A. F.
Wehrfritz). UnsolvedMath record UM-00700290 (`KOU-5.6`), dataset ulamai/UnsolvedMath v1.8.0.

Finitely generated means finitely generated as a ring (`Algebra.FiniteType ℤ R`), and positive
characteristic is `ringChar R ≠ 0`. The ideal topology of `R` has the ideals of finite index as a
base at `0`, so the topology it induces on `Rˣ` has the congruence subgroups `ker (Rˣ → (R ⧸ I)ˣ)`,
`R ⧸ I` finite, as a base at `1`. Each congruence subgroup has finite index in `Rˣ` (its quotient
embeds in the finite group `(R ⧸ I)ˣ`), so the two topologies on `Rˣ` agree exactly when every
subgroup of finite index of `Rˣ` contains a congruence subgroup; the target states this non-trivial
inclusion.
-/

/-- Kourovka 5.6 (B. A. F. Wehrfritz): if `R` is a finitely generated integral domain of positive
characteristic, the ideal (profinite) topology of `R` induces the profinite topology on `Rˣ`:
every subgroup of finite index of `Rˣ` contains the congruence subgroup `{u ∈ Rˣ | u ≡ 1 mod I}`
of some ideal `I` with `R ⧸ I` finite. -/
def unitsProfiniteTopologyInduced : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R], Algebra.FiniteType ℤ R → ringChar R ≠ 0 →
    ∀ H : Subgroup Rˣ, H.FiniteIndex →
      ∃ I : Ideal R, Finite (R ⧸ I) ∧
        (Units.map (Ideal.Quotient.mk I).toMonoidHom).ker ≤ H

/--
Resolved true: the Kourovka Archive answers 5.6 "Yes, it does", citing Segal (1979): for a finitely
generated integral domain `R` of positive characteristic, every subgroup of finite index of `Rˣ`
contains a congruence subgroup `{u ∈ Rˣ | u ≡ 1 mod I}` with `R ⧸ I` finite, so the ideal topology
induces the profinite topology on `Rˣ` (the characteristic `0` case was known before). Source: E. I.
Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 5.6 (B. A. F. Wehrfritz);
resolution: D. Segal, Congruence topologies in commutative rings, Bull. London Math. Soc. 11 (1979),
186-190, Kourovka Archive, Problem 5.6: Yes, it does (Segal), https://doi.org/10.1112/blms/11.2.186.
-/
public theorem_wanted unitsProfiniteTopologyInduced_holds : unitsProfiniteTopologyInduced

end MathlibExt.Algebra.UnitsCongruenceTopologyKourovka5Problem6Wanted
