/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Frattini
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup
import Mathlib.Tactic.Linarith

/-!
# Abelian components of partitions of finite `p`-groups (Kourovka Notebook Problem 15.26)

Kourovka Notebook, Problem 15.26 (Ya. G. Berkovich): a partition of a group is a representation of
it as a set-theoretic union of some of its proper subgroups (components) that intersect pairwise
trivially. Is it true that every nontrivial partition of a finite `p`-group has an abelian
component?

`pGroupPartitionHasAbelianComponent_holds` answers the question positively: every partition of a
finite `p`-group has an abelian component.

## Proof outline

Let `C` be a partition of a finite `p`-group `G` and let `Φ` be the Frattini subgroup of `G`. Some
component `H` meets `Φ` trivially. Since the commutator subgroup of a finite `p`-group lies in `Φ`,
every commutator of two elements of `H` is then trivial, so `H` is abelian.

To find `H`, suppose instead that every component meets `Φ` nontrivially, hence in at least `p`
elements. Counting the nonidentity elements of a subgroup `S` component by component gives
`∑_{H ∈ C} |H ∩ S| = |C| + |S| - 1`; for `S = Φ` this yields `(p - 1) |C| < |Φ|`. For a component
`H` the subgroup `HΦ` is proper, because `Φ` consists of non-generators, hence of index at least
`p`, so `p |H| |Φ| = p |HΦ| |H ∩ Φ| ≤ |G| |H ∩ Φ|`. Summing over `C` and counting with `S = G`
gives `p |Φ| (|C| + |G| - 1) ≤ |G| (|C| + |Φ| - 1)`, which is impossible because
`1 ≤ |C| < |Φ|`.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.PGroupPartitionAbelianComponentKourovka15Problem26Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 15.26 (Ya. G. Berkovich). UnsolvedMath
record UM-00701114 (`KOU-15.26`), dataset ulamai/UnsolvedMath v1.8.0.

Components are proper subgroups that cover `G` and meet pairwise in `1`. They are not required to be
nontrivial, as in Theorem A of the resolving preprint: a trivial component is abelian, and removing
it leaves a partition. A partition always has at least two components, so "nontrivial" adds no
condition.
-/

/-- **Partition of a group.** Let $G$ be a group. A set $C$ of subgroups of $G$ is a partition of
$G$ when every member of $C$ is a proper subgroup of $G$, every element of $G$ lies in some member
of $C$, and any two distinct members of $C$ intersect in the trivial subgroup. The members of $C$
are called its components. -/
def IsGroupPartition {G : Type*} [Group G] (C : Set (Subgroup G)) : Prop :=
  (∀ H ∈ C, H ≠ ⊤) ∧ (∀ g : G, ∃ H ∈ C, g ∈ H) ∧ ∀ H ∈ C, ∀ K ∈ C, H ≠ K → H ⊓ K = ⊥

/-- **Berkovich's question on abelian components of partitions.** The statement that for every prime
$p$, every finite $p$-group $G$ and every partition $C$ of $G$ (a set of proper subgroups of $G$
whose union is $G$ and any two distinct members of which intersect in the trivial subgroup), some
member $H$ of $C$ is abelian, that is, $xy = yx$ for all $x, y \in H$.

This is Kourovka Notebook Problem 15.26 (Ya. G. Berkovich). -/
def pGroupPartitionHasAbelianComponent : Prop :=
  ∀ p : ℕ, p.Prime → ∀ (G : Type) [Group G] [Finite G], IsPGroup p G →
    ∀ C : Set (Subgroup G), IsGroupPartition C → ∃ H ∈ C, ∀ x ∈ H, ∀ y ∈ H, x * y = y * x

open Subgroup
open scoped commutatorElement

section Proof

variable {p : ℕ} [hp : Fact p.Prime] {G : Type*} [Group G]

-- A maximal subgroup of a finite `p`-group is normal of index `p`, so the quotient is cyclic.
private theorem commutator_le_of_isCoatom [Finite G] (hG : IsPGroup p G) {M : Subgroup G}
    (hM : IsCoatom M) : commutator G ≤ M := by
  have := hG.isNilpotent
  have : M.Normal := Group.normalizerCondition_of_isNilpotent.normal_of_coatom M hM
  have hcard : Nat.card (G ⧸ M) = p := hG.isCoatom_iff_index_eq_prime.mp hM
  have : IsCyclic (G ⧸ M) := isCyclic_of_prime_card hcard
  exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance

private theorem commutator_le_frattini [Finite G] (hG : IsPGroup p G) :
    commutator G ≤ frattini G :=
  le_iInf₂ fun _ hM => commutator_le_of_isCoatom hG hM

-- Each nonidentity element of `S` lies in exactly one component, and `1` lies in all of them.
private theorem sum_card_inf_add_one [Finite G] {C : Finset (Subgroup G)}
    (hcover : ∀ g : G, ∃ H ∈ C, g ∈ H) (hdisj : ∀ H ∈ C, ∀ K ∈ C, H ≠ K → H ⊓ K = ⊥)
    (S : Subgroup G) :
    ∑ H ∈ C, Nat.card (H ⊓ S : Subgroup G) + 1 = C.card + Nat.card S := by
  classical
  have := Fintype.ofFinite G
  have hcard (K : Subgroup G) : Nat.card K = ∑ g : G, if g ∈ K then 1 else 0 := by
    rw [Finset.sum_boole, Nat.cast_id, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hfib (g : G) (hg : g ≠ 1) :
      ∑ H ∈ C, (if g ∈ H ⊓ S then 1 else 0) = if g ∈ S then 1 else 0 := by
    obtain ⟨H₀, hH₀, hgH₀⟩ := hcover g
    rw [Finset.sum_eq_single_of_mem H₀ hH₀]
    · simp [mem_inf, hgH₀]
    · intro K hK hKH₀
      have hgK : g ∉ K := fun hgK => hg <| by
        simpa [hdisj K hK H₀ hH₀ hKH₀] using (mem_inf.mpr ⟨hgK, hgH₀⟩ : g ∈ K ⊓ H₀)
      simp [mem_inf, hgK]
  simp_rw [hcard]
  rw [Finset.sum_comm, Fintype.sum_eq_add_sum_compl 1, Fintype.sum_eq_add_sum_compl 1
    (fun g => if g ∈ S then 1 else 0)]
  have h₁ : ∑ H ∈ C, (if (1 : G) ∈ H ⊓ S then 1 else 0) = C.card := by simp
  rw [h₁, Finset.sum_congr rfl fun g hg => hfib g (by simpa using hg)]
  simp only [S.one_mem, ↓reduceIte]
  ring

private theorem card_mul_card_eq (H N : Subgroup G) [N.Normal] :
    Nat.card H * Nat.card N = Nat.card (H ⊔ N : Subgroup G) * Nat.card (H ⊓ N : Subgroup G) := by
  have h₁ := relIndex_mul_card N H
  have h₂ := relIndex_mul_card N (H ⊔ N)
  rw [relIndex_sup_right, inf_of_le_left le_sup_right] at h₂
  rw [← h₁, ← h₂, inf_comm]
  ring

-- Some component meets the Frattini subgroup trivially.
private theorem exists_inf_frattini_eq_bot [Finite G] (hG : IsPGroup p G)
    {C : Set (Subgroup G)} (hC : IsGroupPartition C) : ∃ H ∈ C, H ⊓ frattini G = ⊥ := by
  classical
  obtain ⟨hproper, hcover, hdisj⟩ := hC
  by_contra! hcon
  set N := frattini G
  set D := (Set.toFinite C).toFinset
  have hD {H : Subgroup G} : H ∈ D ↔ H ∈ C := Set.Finite.mem_toFinset _
  have hp2 : 2 ≤ p := hp.out.two_le
  -- Each component meets `N` in at least `p` elements.
  have hinf (H : Subgroup G) (hH : H ∈ C) : p ≤ Nat.card (H ⊓ N : Subgroup G) := by
    rcases (hG.to_subgroup (H ⊓ N)).card_eq_or_dvd with h | h
    · exact absurd (card_eq_one.mp h) (hcon H hH)
    · exact Nat.le_of_dvd Nat.card_pos h
  -- Each component and `N` generate a proper subgroup, of index at least `p`.
  have hsup (H : Subgroup G) (hH : H ∈ C) : p * Nat.card (H ⊔ N : Subgroup G) ≤ Nat.card G := by
    have hne : H ⊔ N ≠ ⊤ := fun h => hproper H hH (frattini_nongenerating h)
    obtain ⟨k, hk⟩ := hG.index (H ⊔ N)
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hne (index_eq_one.mp (by simpa using hk))
    rw [← (H ⊔ N).card_mul_index, hk, mul_comm]
    exact Nat.mul_le_mul_left _ (le_self_pow₀ hp.out.one_lt.le hk0)
  have hcover' (g : G) : ∃ H ∈ D, g ∈ H := by
    obtain ⟨H, hH, hgH⟩ := hcover g
    exact ⟨H, hD.mpr hH, hgH⟩
  have hdisj' : ∀ H ∈ D, ∀ K ∈ D, H ≠ K → H ⊓ K = ⊥ := fun H hH K hK =>
    hdisj H (hD.mp hH) K (hD.mp hK)
  have hA := sum_card_inf_add_one hcover' hdisj' ⊤
  have hB := sum_card_inf_add_one hcover' hdisj' N
  simp only [inf_top_eq, card_top] at hA
  have hkey : p * Nat.card N * ∑ H ∈ D, Nat.card H ≤
      Nat.card G * ∑ H ∈ D, Nat.card (H ⊓ N : Subgroup G) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun H hH => ?_
    calc p * Nat.card N * Nat.card H
        = p * Nat.card (H ⊔ N : Subgroup G) * Nat.card (H ⊓ N : Subgroup G) := by
          rw [mul_assoc, mul_comm (Nat.card N), card_mul_card_eq, mul_assoc]
      _ ≤ Nat.card G * Nat.card (H ⊓ N : Subgroup G) :=
          Nat.mul_le_mul_right _ (hsup H (hD.mp hH))
  have hc : p * D.card ≤ ∑ H ∈ D, Nat.card (H ⊓ N : Subgroup G) := by
    rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun H hH => hinf H (hD.mp hH)
  have hc1 : 1 ≤ D.card := by
    obtain ⟨H, hH, -⟩ := hcover' 1
    exact Finset.card_pos.mpr ⟨H, hH⟩
  have hg1 : 1 ≤ Nat.card G := Nat.card_pos
  set A := ∑ H ∈ D, Nat.card H
  set B := ∑ H ∈ D, Nat.card (H ⊓ N : Subgroup G)
  set c := D.card
  set g := Nat.card G
  set n := Nat.card N
  have h₁ : 2 * c ≤ B := (Nat.mul_le_mul_right c hp2).trans hc
  have h₂ : B + 2 ≤ 2 * n := by omega
  have h₃ : 2 * n * g ≤ p * n * A := Nat.mul_le_mul (Nat.mul_le_mul_right n hp2) (by omega)
  have h₄ : g * (B + 2) ≤ g * (2 * n) := Nat.mul_le_mul_left g h₂
  nlinarith

end Proof

/--
**Every partition of a finite $p$-group has an abelian component.** For every prime $p$, every
finite $p$-group $G$ and every partition $C$ of $G$ (a set of proper subgroups of $G$ whose union is
$G$ and any two distinct members of which intersect in the trivial subgroup), some member $H$ of $C$
is abelian, that is, $xy = yx$ for all $x, y \in H$.

Resolved true: by Theorem B of Cat's preprint, every partition of a finite $p$-group into nontrivial
components has an abelian component (for non-abelian $G$ an elementary abelian one meeting the
Frattini subgroup $\Phi(G)$ of $G$ trivially); the Kourovka Notebook (21st issue) marks 15.26
solved, "Yes, it is true" (AI solution confirmed by E. I. Khukhro). Components are not required to
be nontrivial here: a trivial component is abelian, and removing it leaves a partition.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 15.26 (Ya. G. Berkovich); resolution: G.
Cat, A Frattini-free component in every partition, and Kourovka 15.26, preprint (2026), AI-generated
solution confirmed by E. I. Khukhro, Theorem B (a partition of a finite p-group into nontrivial
components has an abelian component), derived from Theorem A; the Kourovka Notebook (21st issue)
marks 15.26 solved,
https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/08/kourovka_15-26-ai.pdf.
-/
public theorem pGroupPartitionHasAbelianComponent_holds : pGroupPartitionHasAbelianComponent := by
  intro p hp G _ _ hG C hC
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨H, hHC, hH⟩ := exists_inf_frattini_eq_bot hG hC
  refine ⟨H, hHC, fun x hx y hy => ?_⟩
  have hxy : ⁅x, y⁆ ∈ H ⊓ frattini G := by
    refine mem_inf.mpr ⟨?_, commutator_le_frattini hG ?_⟩
    · rw [commutatorElement_def]
      exact H.mul_mem (H.mul_mem (H.mul_mem hx hy) (H.inv_mem hx)) (H.inv_mem hy)
    · exact commutator_mem_commutator (mem_top x) (mem_top y)
  rwa [hH, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hxy

end MathlibExt.GroupTheory.PGroupPartitionAbelianComponentKourovka15Problem26Wanted
