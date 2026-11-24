/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.PUnit
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.Order.SupClosed

/-!
# Complete lattices of formations of finite groups

The formations defined by restricting the prime divisors of the group order realize the
pentagon lattice, giving a positive answer to Kourovka Notebook Problem 18.92(b).
-/

@[expose] public section

namespace MathlibExt.GroupTheory.CompleteLatticeOfFormationsKourovka18Problem92Wanted

/-- **Isomorphism-closed classes of groups (Kourovka 18.92).** A class of groups $\mathfrak{X}$ is
given by a membership predicate on groups whose underlying type lies in the lowest universe, such
that whenever a group $H$ belongs to $\mathfrak{X}$ and $K$ is a group isomorphic to $H$, the group
$K$ also belongs to $\mathfrak{X}$. -/
structure GroupClass where
  /-- Membership predicate. -/
  mem : ∀ (H : Type) [Group H], Prop
  /-- Closure under isomorphism. -/
  iso : ∀ (H K : Type) [Group H] [Group K], (H ≃* K) → mem H → mem K

/-- **Formations of finite groups (Kourovka 18.92).** A class $\mathfrak{X}$ of groups is a
formation if every group in $\mathfrak{X}$ is finite, $\mathfrak{X}$ contains the trivial group,
for every finite group $G$ in $\mathfrak{X}$ and every normal subgroup $N$ of $G$ the quotient
$G/N$ lies in $\mathfrak{X}$, and for every finite group $G$ with normal subgroups $N_1$ and $N_2$
such that $G/N_1$ and $G/N_2$ lie in $\mathfrak{X}$, the quotient $G/(N_1 \cap N_2)$ lies in
$\mathfrak{X}$. -/
def IsFormation (X : GroupClass) : Prop :=
  (∀ (H : Type) [Group H], X.mem H → Finite H) ∧ X.mem Unit ∧
  (∀ (G : Type) [Group G] [Finite G] (N : Subgroup G) [N.Normal], X.mem G → X.mem (G ⧸ N)) ∧
  ∀ (G : Type) [Group G] [Finite G] (N₁ N₂ : Subgroup G) [N₁.Normal] [N₂.Normal],
    X.mem (G ⧸ N₁) → X.mem (G ⧸ N₂) → X.mem (G ⧸ (N₁ ⊓ N₂))

/-- **Inclusion of group classes.** For classes of groups $\mathfrak{X}$ and $\mathfrak{Y}$, the
class $\mathfrak{X}$ is included in $\mathfrak{Y}$, written $\mathfrak{X} \subseteq \mathfrak{Y}$,
if every group that belongs to $\mathfrak{X}$ also belongs to $\mathfrak{Y}$. -/
def Incl (X Y : GroupClass) : Prop :=
  ∀ (H : Type) [Group H], X.mem H → Y.mem H

/-- **Complete lattices of formations.** A set $\Theta$ of classes of groups is a complete lattice
of formations if it is nonempty, every member of $\Theta$ is a formation, for every nonempty subset
$S \subseteq \Theta$ the intersection of the classes in $S$ (the class of groups belonging to every
member of $S$) belongs to $\Theta$, and $\Theta$ has a member that contains every member of
$\Theta$. -/
def IsCompleteLatticeOfFormations (Θ : Set GroupClass) : Prop :=
  Θ.Nonempty ∧ (∀ X ∈ Θ, IsFormation X) ∧
  (∀ S ⊆ Θ, S.Nonempty → ∃ Y ∈ Θ, ∀ (H : Type) [Group H], Y.mem H ↔ ∀ X ∈ S, X.mem H) ∧
  ∃ T ∈ Θ, ∀ X ∈ Θ, Incl X T

/-- **Joins in a set of group classes.** Let $\Theta$ and $S$ be sets of classes of groups. A class
$\mathfrak{J}$ is the join of $S$ in $\Theta$ if $\mathfrak{J} \in \Theta$, every member of $S$ is
contained in $\mathfrak{J}$, and $\mathfrak{J}$ is contained in every member of $\Theta$ that
contains every member of $S$. -/
def IsJoinIn (Θ S : Set GroupClass) (J : GroupClass) : Prop :=
  J ∈ Θ ∧ (∀ X ∈ S, Incl X J) ∧ ∀ U ∈ Θ, (∀ X ∈ S, Incl X U) → Incl J U

/-- **Compact elements of a set of group classes.** Let $\Theta$ be a set of classes of groups and
$\mathfrak{A}$ a class of groups. Then $\mathfrak{A}$ is compact in $\Theta$ if, for every subset
$S \subseteq \Theta$ and every join $\mathfrak{J}$ of $S$ in $\Theta$ with
$\mathfrak{A} \subseteq \mathfrak{J}$, there are a finite subset $S_1 \subseteq S$ and a join
$\mathfrak{J}_1$ of $S_1$ in $\Theta$ with $\mathfrak{A} \subseteq \mathfrak{J}_1$. -/
def IsCompactIn (Θ : Set GroupClass) (A : GroupClass) : Prop :=
  ∀ S ⊆ Θ, ∀ J, IsJoinIn Θ S J → Incl A J →
    ∃ S₁ ⊆ S, S₁.Finite ∧ ∃ J₁, IsJoinIn Θ S₁ J₁ ∧ Incl A J₁

/-- **Algebraic sets of group classes.** A set $\Theta$ of classes of groups is algebraic if every
member $\mathfrak{A}$ of $\Theta$ is the join in $\Theta$ of some subset $S \subseteq \Theta$ all of
whose members are compact in $\Theta$. -/
def IsAlgebraicIn (Θ : Set GroupClass) : Prop :=
  ∀ A ∈ Θ, ∃ S ⊆ Θ, (∀ C ∈ S, IsCompactIn Θ C) ∧ IsJoinIn Θ S A

/-- **Modular sets of group classes.** A set $\Theta$ of classes of groups is modular if for all
$\mathfrak{A}, \mathfrak{B}, \mathfrak{C} \in \Theta$ with $\mathfrak{A} \subseteq \mathfrak{C}$
the following holds: whenever $\mathfrak{J}_1$ is the join in $\Theta$ of the set
$\{\mathfrak{A}, \mathfrak{B} \cap \mathfrak{C}\}$ and $\mathfrak{D}$ is the join in $\Theta$ of
the set $\{\mathfrak{A}, \mathfrak{B}\}$, the classes $\mathfrak{J}_1$ and
$\mathfrak{D} \cap \mathfrak{C}$ contain the same groups. This is the modular law
$\mathfrak{A} \vee (\mathfrak{B} \wedge \mathfrak{C}) = (\mathfrak{A} \vee \mathfrak{B}) \wedge
\mathfrak{C}$, with joins taken in $\Theta$ and meets the intersections. -/
def IsModularIn (Θ : Set GroupClass) : Prop :=
  ∀ A ∈ Θ, ∀ B ∈ Θ, ∀ C ∈ Θ, Incl A C → ∀ BC J₁ AB J₂ : GroupClass,
    (∀ (H : Type) [Group H], BC.mem H ↔ B.mem H ∧ C.mem H) → IsJoinIn Θ {A, BC} J₁ →
    IsJoinIn Θ {A, B} AB → (∀ (H : Type) [Group H], J₂.mem H ↔ AB.mem H ∧ C.mem H) →
    Incl J₁ J₂ ∧ Incl J₂ J₁

/-- **Kourovka Problem 18.92(a) (A. N. Skiba).** The proposition that some set $\Theta$ of classes
of groups is a complete lattice of formations of finite groups and is not algebraic. -/
def nonAlgebraicCompleteLatticeOfFormations : Prop :=
  ∃ Θ : Set GroupClass, IsCompleteLatticeOfFormations Θ ∧ ¬ IsAlgebraicIn Θ

/-- **The non-modular formation lattice problem (Kourovka 18.92(b), A. N. Skiba).** The proposition
that there is a complete lattice of formations of finite groups that is not modular, joins being
least upper bounds in the lattice and meets being intersections. -/
def nonModularCompleteLatticeOfFormations : Prop :=
  ∃ Θ : Set GroupClass, IsCompleteLatticeOfFormations Θ ∧ ¬ IsModularIn Θ

/-- The finite groups whose orders have all their prime divisors in `S`. -/
def primeSupportClass (S : Set ℕ) : GroupClass where
  mem H _ := Finite H ∧ ∀ p : ℕ, p.Prime → p ∣ Nat.card H → p ∈ S
  iso H _ _ _ e h := by
    have : Finite H := h.1
    exact ⟨Finite.of_equiv H e.toEquiv, Nat.card_congr e.toEquiv ▸ h.2⟩

/-- Restricting the prime divisors of the group order defines a formation. -/
theorem isFormation_primeSupportClass (S : Set ℕ) : IsFormation (primeSupportClass S) := by
  refine ⟨fun _ _ h ↦ h.1, ⟨inferInstance, ?_⟩, ?_, ?_⟩
  · intro p hp hd
    exact (hp.not_dvd_one (by simpa using hd)).elim
  · intro G _ _ N _ h
    exact ⟨inferInstance, fun p hp hd ↦ h.2 p hp (hd.trans N.card_quotient_dvd_card)⟩
  · intro G _ _ N M _ _ hN hM
    refine ⟨inferInstance, fun p hp hd ↦ ?_⟩
    change p ∣ (N ⊓ M).index at hd
    rw [Subgroup.index_inf] at hd
    rcases hp.dvd_mul.mp hd with h | h
    · exact hN.2 p hp (h.trans (N.relIndex_dvd_index_of_normal M))
    · exact hM.2 p hp h

private theorem primeSupportClass_mono {S T : Set ℕ} (h : S ⊆ T) :
    Incl (primeSupportClass S) (primeSupportClass T) :=
  fun _ _ hG ↦ ⟨hG.1, fun p hp hd ↦ h (hG.2 p hp hd)⟩

/-- A cyclic group of order `p` detects whether the prime `p` is allowed. -/
private theorem prime_mem_of_incl {S T : Set ℕ}
    (h : Incl (primeSupportClass S) (primeSupportClass T)) {p : ℕ} (hp : p.Prime) (hS : p ∈ S) :
    p ∈ T := by
  have : NeZero p := ⟨hp.ne_zero⟩
  let G := Multiplicative (ZMod p)
  have hcard : Nat.card G = p := Nat.card_zmod p
  have hG : (primeSupportClass S).mem G := by
    refine ⟨inferInstance, fun q hq hd ↦ ?_⟩
    rwa [(Nat.prime_dvd_prime_iff_eq hq hp).mp (hcard ▸ hd)]
  exact (h G hG).2 p hp (hcard ▸ dvd_rfl)

private def primeSets : Set (Set ℕ) := {∅, {2}, {2, 3}, {5}, Set.univ}

private def pentagon : Set GroupClass := primeSupportClass '' primeSets

private theorem primeSets_infClosed : InfClosed primeSets := by
  simp only [InfClosed, primeSets, Set.mem_insert_iff, Set.mem_singleton_iff]
  rintro _ (rfl | rfl | rfl | rfl | rfl) _ (rfl | rfl | rfl | rfl | rfl) <;>
    simp [Set.ext_iff]

private theorem pentagon_complete : IsCompleteLatticeOfFormations pentagon := by
  have htop : Set.univ ∈ primeSets := by simp [primeSets]
  refine ⟨⟨_, Set.mem_image_of_mem _ htop⟩, ?_, ?_, ?_⟩
  · rintro _ ⟨S, _, rfl⟩
    exact isFormation_primeSupportClass S
  · intro D hD hne
    let sets := primeSets ∩ primeSupportClass ⁻¹' D
    have hsub : sets ⊆ primeSets := Set.inter_subset_left
    have hfin : primeSets.Finite := by simp [primeSets]
    refine ⟨primeSupportClass (⋂₀ sets),
      Set.mem_image_of_mem _ (primeSets_infClosed.sInf_mem (hfin.subset hsub) htop hsub), ?_⟩
    intro G _
    constructor
    · rintro h _ hX
      obtain ⟨S, hS, rfl⟩ := hD hX
      exact primeSupportClass_mono (Set.sInter_subset_of_mem (show S ∈ sets from ⟨hS, hX⟩)) G h
    · intro h
      obtain ⟨X, hX⟩ := hne
      obtain ⟨S, _, rfl⟩ := hD hX
      exact ⟨(h _ hX).1, fun p hp hd T hT ↦ (h _ hT.2).2 p hp hd⟩
  · refine ⟨_, Set.mem_image_of_mem _ htop, ?_⟩
    rintro _ ⟨S, _, rfl⟩
    exact primeSupportClass_mono (Set.subset_univ S)

private theorem join_pair {Θ : Set GroupClass} {A B J : GroupClass} (hJ : J ∈ Θ)
    (hA : Incl A J) (hB : Incl B J)
    (hleast : ∀ U ∈ Θ, Incl A U → Incl B U → Incl J U) : IsJoinIn Θ {A, B} J := by
  refine ⟨hJ, ?_, fun U hU h ↦ hleast U hU (h A (by simp)) (h B (by simp))⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rintro _ (rfl | rfl)
  · exact hA
  · exact hB

private theorem pentagon_not_modular : ¬ IsModularIn pentagon := by
  let F := primeSupportClass
  have hA : F {2} ∈ pentagon := Set.mem_image_of_mem _ (by simp [primeSets])
  have hB : F {5} ∈ pentagon := Set.mem_image_of_mem _ (by simp [primeSets])
  have hC : F {2, 3} ∈ pentagon := Set.mem_image_of_mem _ (by simp [primeSets])
  have hT : F Set.univ ∈ pentagon := Set.mem_image_of_mem _ (by simp [primeSets])
  have hAC : Incl (F {2}) (F {2, 3}) := primeSupportClass_mono (by simp)
  -- The meet of the two incomparable arms is the bottom formation.
  have hBC (G : Type) [Group G] : (F ∅).mem G ↔ (F {5}).mem G ∧ (F {2, 3}).mem G := by
    constructor
    · exact fun h ↦ ⟨primeSupportClass_mono (Set.empty_subset _) G h,
        primeSupportClass_mono (Set.empty_subset _) G h⟩
    · rintro ⟨hB, hC⟩
      refine ⟨hB.1, fun p hp hd ↦ ?_⟩
      have h5 : p = 5 := hB.2 p hp hd
      have h23 := hC.2 p hp hd
      simp [h5] at h23
  have hleft : IsJoinIn pentagon {F {2}, F ∅} (F {2}) :=
    join_pair hA (fun _ _ h ↦ h) (primeSupportClass_mono (Set.empty_subset _))
      (fun _ _ h _ ↦ h)
  -- Only the top formation contains both the order-two and order-five cyclic groups.
  have hAB : IsJoinIn pentagon {F {2}, F {5}} (F Set.univ) := by
    apply join_pair hT (primeSupportClass_mono (Set.subset_univ _))
      (primeSupportClass_mono (Set.subset_univ _))
    rintro _ ⟨S, hS, rfl⟩ h2 h5
    have h2S : 2 ∈ S := prime_mem_of_incl h2 (by decide) rfl
    have h5S : 5 ∈ S := prime_mem_of_incl h5 (by decide) rfl
    have hSuniv : S = Set.univ := by
      simp only [primeSets, Set.mem_insert_iff, Set.mem_singleton_iff] at hS
      rcases hS with rfl | rfl | rfl | rfl | rfl <;> simp_all
    exact primeSupportClass_mono (by rw [hSuniv])
  have hright (G : Type) [Group G] : (F {2, 3}).mem G ↔
      (F Set.univ).mem G ∧ (F {2, 3}).mem G :=
    ⟨fun h ↦ ⟨primeSupportClass_mono (Set.subset_univ _) G h, h⟩, And.right⟩
  intro hmod
  have h := hmod _ hA _ hB _ hC hAC _ _ _ _ hBC hleft hAB hright
  have : 3 ∈ ({2} : Set ℕ) := prime_mem_of_incl h.2 (by decide) (by simp)
  simp at this

/--
**A non-modular complete lattice of formations exists (Kourovka 18.92(b)).** There is a complete
lattice of formations of finite groups that is not modular: a nonempty set $\Theta$ of formations
of finite groups, ordered by inclusion, that contains the intersection of each of its nonempty
subsets and has a largest element, in which the modular law $A \vee (B \wedge C) = (A \vee B)
\wedge C$ for $A \le C$ fails, joins being least upper bounds in $\Theta$ and meets intersections.

The Kourovka Notebook (21st issue) answers 18.92(b) "Yes" (Kinyon-Urban, 2026, confirmed by A. N.
Skiba): writing $\mathfrak{F}_S$ for the finite groups whose order has all prime divisors in $S$,
the formations $\mathfrak{F}_S$ with $S = \emptyset, \{2\}, \{2, 3\}, \{5\}$ and $S$ the set of all
primes are closed under intersections and form the pentagon $N_5$.

Source: E. I. Khukhro and V. D. Mazurov
(eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49
(2026), Problem 18.92 (A. N. Skiba); resolution: M. Kinyon and J. Urban, Results on problems from
the Kourovka Notebook, preprint, version 4, 19 September 2026, Section 3.29 (Problem 18.92): with
F_S the finite groups whose order has all prime divisors in S, {F_S : S finite} ∪ {F_P} is not
algebraic and the formations with prime sets ∅, {2}, {2, 3}, {5}, P form a pentagon N_5; an AI
solution confirmed by A. N. Skiba, accepted in the Kourovka Notebook (21st issue),
https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/09/kourovka-mathematics.pdf.
-/
public theorem nonModularCompleteLatticeOfFormations_holds :
    nonModularCompleteLatticeOfFormations :=
  ⟨pentagon, pentagon_complete, pentagon_not_modular⟩

end MathlibExt.GroupTheory.CompleteLatticeOfFormationsKourovka18Problem92Wanted
