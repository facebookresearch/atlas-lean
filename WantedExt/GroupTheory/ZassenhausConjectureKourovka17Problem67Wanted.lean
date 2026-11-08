/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The first Zassenhaus conjecture (Kourovka Notebook Problem 17.67)

Kourovka Notebook, Archive of Solved Problems, Problem 17.67 (V. D. Mazurov): (H. Zassenhaus).
Conjecture: every invertible element of finite order of the integral group ring `ℤG` of a finite
group `G` is conjugate in the rational group ring `ℚG` to an element of `±G`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.GroupTheory.OrderOfElement

@[expose] public section

namespace MathlibExt.GroupTheory.ZassenhausConjectureKourovka17Problem67Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 17.67 (V. D.
Mazurov). UnsolvedMath record UM-00701369 (`KOU-17.67`), dataset ulamai/UnsolvedMath v1.8.0.

`ℤG` and `ℚG` are `MonoidAlgebra ℤ G` and `MonoidAlgebra ℚ G`, `ℤG` maps to `ℚG` by
`MonoidAlgebra.mapRingHom G (Int.castRingHom ℚ)`, conjugation is by a unit of `ℚG`, and `±g` is
`MonoidAlgebra.single g ε` with `ε = ±1`.
-/

/-- Kourovka 17.67 (H. Zassenhaus's conjecture, recorded by V. D. Mazurov): every unit of finite
order of the integral group ring `ℤG` of a finite group `G` is conjugate, by a unit of the rational
group ring `ℚG`, to an element `±g` with `g ∈ G`. -/
def zassenhausConjecture : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (u : (MonoidAlgebra ℤ G)ˣ), IsOfFinOrder u →
    ∃ (v : (MonoidAlgebra ℚ G)ˣ) (g : G) (ε : ℚ), (ε = 1 ∨ ε = -1) ∧
      (v : MonoidAlgebra ℚ G) *
          MonoidAlgebra.mapRingHom G (Int.castRingHom ℚ) (u : MonoidAlgebra ℤ G) *
          (↑v⁻¹ : MonoidAlgebra ℚ G) = MonoidAlgebra.single g ε

/--
Resolved false: Eisele and Margolis (abstract and Theorem A) give a metabelian group `G` of order
`2⁷·3²·5·7²·19²` and a unit of order `7·19` in `ℤG` that is not conjugate in `ℚG` to any element
`±g`, `g ∈ G`; the Kourovka Archive records for 17.67 "A counterexample was constructed". Source: E.
I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 17.67 (V. D. Mazurov);
resolution: F. Eisele and L. Margolis, A counterexample to the first Zassenhaus conjecture, Adv.
Math. 339 (2018), 599-641, abstract and Theorem A (a metabelian group of order 2⁷·3²·5·7²·19² whose
integral group ring contains a unit of order 7·19 not conjugate in the rational group algebra to any
±g); Kourovka Archive, Problem 17.67 (A counterexample was constructed),
http://eprints.gla.ac.uk/177223/7/177223.pdf.
-/
public theorem_wanted zassenhausConjecture_refuted : ¬ zassenhausConjecture

end MathlibExt.GroupTheory.ZassenhausConjectureKourovka17Problem67Wanted
