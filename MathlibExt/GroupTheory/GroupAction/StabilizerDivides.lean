/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.SetTheory.Cardinal.Finite

open scoped BigOperators

/-!
# A subgroup stabilizing a finite set divides its cardinality

Source: `v1/Atlas/AlgebraNotes/code/SylowTheorems.lean`
(`SylowTheorems.card_stabilizer_dvd_card`, fully proved there), formalizing a
lemma used in the book's proof of the Sylow theorems (Proofs and Applications
of the Sylow Theorems, Proof of Sylow Theorems): if a subgroup `H` of a group
`G` stabilizes a finite subset `U` of `G` under left multiplication, then
`|H|` divides `|U|`.

The proof is the orbit partition: the `H`-orbits of elements of `U` (under
left multiplication) partition `U`, and every orbit has exactly `|H|`
elements, since left multiplication by a fixed element of `G` is injective.
-/

@[expose] public section

namespace Subgroup

variable {G : Type*} [Group G] [Fintype G]

/-- **A subgroup stabilizing a subset has order dividing its size.** Let $G$ be a finite group,
let $H$ be a subgroup of $G$ and let $U$ be a subset of $G$ such that $hu \in U$ for all
$h \in H$ and $u \in U$. Then $|H|$ divides $|U|$.

The $H$-orbits partition $U$ and each orbit has exactly $|H|$ elements, since left
multiplication is injective. -/
theorem card_stabilizer_dvd_card (H : Subgroup G) (U : Finset G)
    (hU : ∀ (h : G), h ∈ H → ∀ u ∈ U, h * u ∈ U) :
    Nat.card H ∣ U.card := by
  classical
  have : Fintype H := Subtype.fintype (· ∈ H)
  rw [Nat.card_eq_fintype_card]
  let orb : G → Finset G := fun u => Finset.univ.image (fun h : H => (h : G) * u)
  have orbit_card : ∀ u : G, (orb u).card = Fintype.card H := by
    intro u
    apply Finset.card_image_of_injective
    intro ⟨a, ha⟩ ⟨b, hb⟩ hab
    simp only [Subtype.mk.injEq]
    exact mul_right_cancel (show a * u = b * u from by simpa using hab)
  have orbit_sub : ∀ u ∈ U, orb u ⊆ U := by
    intro u hu v hv
    simp only [orb, Finset.mem_image, Finset.mem_univ, true_and] at hv
    obtain ⟨⟨h, hh⟩, rfl⟩ := hv
    exact hU h hh u hu
  have orbit_eq : ∀ u v : G, v ∈ orb u → orb v = orb u := by
    intro u v hv
    simp only [orb, Finset.mem_image, Finset.mem_univ, true_and] at hv ⊢
    obtain ⟨⟨h₀, hh₀⟩, rfl⟩ := hv
    ext w
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨h₁, hh₁⟩, rfl⟩
      exact ⟨⟨h₁ * h₀, H.mul_mem hh₁ hh₀⟩, by simp [mul_assoc]⟩
    · rintro ⟨⟨h₁, hh₁⟩, rfl⟩
      exact ⟨⟨h₁ * h₀⁻¹, H.mul_mem hh₁ (H.inv_mem hh₀)⟩, by simp [mul_assoc]⟩
  have mem_orbit : ∀ u : G, u ∈ orb u := by
    intro u
    simp only [orb, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨1, H.one_mem⟩, by simp⟩
  have fiber_eq_orbit : ∀ u ∈ U, U.filter (fun v => orb v = orb u) = orb u := by
    intro u hu
    ext v
    simp only [Finset.mem_filter]
    constructor
    · intro ⟨_, hv⟩
      rw [← hv]
      exact mem_orbit v
    · intro hv
      exact ⟨orbit_sub u hu hv, orbit_eq u v hv⟩
  have h_fiber : U.card = ∑ O ∈ U.image orb, (U.filter (fun v => orb v = O)).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro u hu
    exact Finset.mem_image_of_mem orb hu
  have h_each : ∀ O ∈ U.image orb, (U.filter (fun v => orb v = O)).card = Fintype.card H := by
    intro O hO
    simp only [Finset.mem_image] at hO
    obtain ⟨u, hu, rfl⟩ := hO
    rw [fiber_eq_orbit u hu, orbit_card u]
  rw [h_fiber, Finset.sum_congr rfl h_each, Finset.sum_const, smul_eq_mul]
  exact dvd_mul_left _ _

end Subgroup
