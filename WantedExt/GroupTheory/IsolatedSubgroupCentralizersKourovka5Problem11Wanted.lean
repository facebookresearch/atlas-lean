/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Subgroups containing the centralizers of their elements (Kourovka Notebook Problem 5.11)

Kourovka Notebook, Archive of Solved Problems, Problem 5.11 (K. W. Gruenberg): let G be a finite
group and suppose that there exists a non-empty proper subset π of the set of all primes dividing
|G| such that the centralizer of every non-trivial π-element is a π-subgroup; does G contain a
subgroup U such that U^g ∩ U = 1 or U for every g ∈ G and the centralizer of every non-trivial
element of U is contained in U?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.OrderOfElement
public import WantedExt.GroupTheory.DPiHallIntersectionKourovka18Problem31Wanted

@[expose] public section

namespace MathlibExt.GroupTheory.IsolatedSubgroupCentralizersKourovka5Problem11Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 5.11 (K. W.
Gruenberg). UnsolvedMath record UM-00700295 (`KOU-5.11`), dataset ulamai/UnsolvedMath v1.8.0.

A `π`-element is an element whose order is a `π`-number, and a `π`-subgroup is one whose order is a
`π`-number (`IsPiNumber` and `IsPiSubgroup` of the Kourovka 18.31 entry, reused here). The subgroup
`U` asked for is an isolated TI-subgroup: proper, as in Suzuki's definition of an isolated subgroup,
and non-trivial (Williams's subgroups are Hall subgroups for a component of the prime graph); `U =
1` and `U = G` satisfy both conditions of the problem in every group. `U^g` is the conjugate `g U
g⁻¹`.
-/

open MathlibExt.GroupTheory.DPiHallIntersectionKourovka18Problem31Wanted (IsPiNumber IsPiSubgroup)

/-- Kourovka 5.11 (K. W. Gruenberg): let `G` be a finite group and `π` a non-empty proper subset of
the set of primes dividing `|G|` such that the centralizer of every non-trivial `π`-element is a
`π`-subgroup. Then `G` has a subgroup `U`, other than `1` and `G`, with `U ∩ U^g ∈ {1, U}` for every
`g ∈ G` and `C_G(u) ≤ U` for every `u ∈ U \ {1}`. -/
def isolatedSubgroupExists : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (π : Set ℕ), π ⊆ {p | p.Prime ∧ p ∣ Nat.card G} →
    π.Nonempty → (∃ p, p.Prime ∧ p ∣ Nat.card G ∧ p ∉ π) →
    (∀ g : G, g ≠ 1 → IsPiNumber π (orderOf g) → IsPiSubgroup π (Subgroup.centralizer {g})) →
    ∃ U : Subgroup G, U ≠ ⊥ ∧ U ≠ ⊤ ∧
      (∀ g : G, U ⊓ U.map (MulAut.conj g).toMonoidHom = ⊥ ∨
        U ⊓ U.map (MulAut.conj g).toMonoidHom = U) ∧
      ∀ u ∈ U, u ≠ 1 → Subgroup.centralizer {u} ≤ U

/--
Resolved true: the Kourovka Archive answers 5.11 "Yes, it does (mod CFSG)", citing Williams, Prime
graph components of finite groups (J. Algebra 69 (1981), 487-513). The hypothesis says that no
non-trivial `π`-element commutes with a non-trivial `π'`-element, so the prime graph of `G` is
disconnected. By Williams's theorem (Kondrat'ev's account) a finite non-soluble group with
disconnected prime graph has, for each component not containing `2`, a nilpotent isolated Hall
subgroup `U` for that component, which is proper and non-trivial, with `U ∩ U^g ∈ {1, U}` and
`C_G(u) ≤ U` for `u ∈ U \ {1}`; by the Gruenberg-Kegel theorem a soluble such group is a Frobenius
or `2`-Frobenius group, and every finite group with disconnected prime graph has an isolated
subgroup. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 5.11
(K. W. Gruenberg); resolution: J. S. Williams, Prime graph components of finite groups, J. Algebra
69 (1981), 487-513, Kourovka Archive, Problem 5.11: Yes, it does (mod CFSG) (Williams); Williams's
theorem as stated in A. S. Kondrat'ev, On prime graphs of finite groups (survey slides), Theorem 2:
a finite non-soluble group with disconnected prime graph contains, for each component π_i other than
the one containing 2, a nilpotent isolated π_i-Hall TI-subgroup; with the Gruenberg-Kegel theorem
(Theorem 1, published in Williams's paper) the finite groups with disconnected prime graph are
exactly those having an isolated subgroup, https://doi.org/10.1016/0021-8693(81)90218-0.
-/
public theorem_wanted isolatedSubgroupExists_holds : isolatedSubgroupExists

end MathlibExt.GroupTheory.IsolatedSubgroupCentralizersKourovka5Problem11Wanted
