/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Sylow

/-!
# Conjugacy classes and a Sylow-center reduction step for groups of order `p ^ a * q ^ b`

Authors: Muse Spark 1.3

Port of the fully proved group-theoretic core from the screened archive
`burnside_wip.zip` (SHA-256
`0686f20667e5fef0850dc3c6ba2e4d9e3ef5ba3f89c2f937faa8a251cd1eee30`):
`Burnside/ConjClass.lean` lines 1–45, `Burnside/ClassSum.lean` lines 13–17,
and `Burnside/SylowCenter.lean` lines 1–56.

Historical citation (independently verified): W. Burnside, "On Groups of Order
p^alpha q^beta," *Proceedings of the London Mathematical Society* s2-1 (1904),
388–392, DOI 10.1112/plms/s2-1.1.388.

This partial stage does not prove the full Burnside `p^a * q^b` solvability theorem.
-/

namespace BurnsidePaqb

@[expose] public section

variable {G : Type*} [Group G] [Fintype G]

open Classical in
/-- **Conjugacy class.** For an element $g$ of a finite group $G$, the conjugacy class of $g$ is
the finite set $\{h g h^{-1} : h \in G\}$, the orbit of $g$ under the action of $G$ on itself
by conjugation. -/
noncomputable def conjClass (g : G) : Finset G :=
  (MulAction.orbit (ConjAct G) g).toFinset

open Classical in
theorem mem_conjClass_iff {g h : G} : h ∈ conjClass g ↔ IsConj h g := by
  simp [conjClass, ConjAct.mem_orbit_conjAct, Set.mem_toFinset]

open Classical in
/-- **Orbit–stabilizer for a conjugacy class.** For every element $g$ of a finite group $G$, the
size of the conjugacy class of $g$ times the order of the stabilizer of $g$ under the action of
$G$ on itself by conjugation, $x \cdot y = x y x^{-1}$, equals the order of $G$. -/
theorem conjClass_card_mul_stabilizer_card (g : G) :
    (conjClass g).card * Fintype.card (MulAction.stabilizer (ConjAct G) g) =
      Fintype.card G := by
  rw [conjClass, Set.toFinset_card]
  exact MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) g

open Classical in
/-- **Centralizer as a conjugation stabilizer.** For an element $g$ of a finite group $G$, this
is the bijection from the centralizer $C_G(g) = \{x \in G : xg = gx\}$ onto the stabilizer of
$g$ for the action of $G$ on itself by conjugation, $x \cdot y = x y x^{-1}$, that sends each
element $x$ to itself. -/
def centralizerEquivStabilizer (g : G) :
    Subgroup.centralizer {g} ≃ MulAction.stabilizer (ConjAct G) g :=
  Equiv.subtypeEquiv ConjAct.toConjAct.toEquiv (fun x => by
    rw [Subgroup.mem_centralizer_iff]
    simp only [Set.mem_singleton_iff, forall_eq]
    rw [MulAction.mem_stabilizer_iff]
    change g * x = x * g ↔ ConjAct.toConjAct x • g = g
    rw [ConjAct.toConjAct_smul, mul_inv_eq_iff_eq_mul]
    exact eq_comm)

open Classical in
theorem centralizer_card_eq_stabilizer_card (g : G) :
    Fintype.card (Subgroup.centralizer {g}) =
      Fintype.card (MulAction.stabilizer (ConjAct G) g) :=
  Fintype.card_congr (centralizerEquivStabilizer g)

open Classical in
/-- **Class size times centralizer order.** Let $g$ be an element of a finite group $G$, let
$g^G$ be its conjugacy class and let $C_G(g) = \{x \in G : xg = gx\}$ be its centralizer.
Then $|g^G| \cdot |C_G(g)| = |G|$. -/
theorem conjClass_card_mul_centralizer_card (g : G) :
    (conjClass g).card * Fintype.card (Subgroup.centralizer {g}) = Fintype.card G := by
  rw [centralizer_card_eq_stabilizer_card]
  exact conjClass_card_mul_stabilizer_card g

open Classical in
/-- **Conjugacy classes are closed under conjugation.** Let $g$, $h$ and $x$ be elements of a
finite group $G$. If $x$ lies in the conjugacy class of $g$, then so does $h x h^{-1}$. -/
theorem conj_mem_conjClass (g h x : G) (hx : x ∈ conjClass g) :
    h * x * h⁻¹ ∈ conjClass g := by
  rw [mem_conjClass_iff] at hx ⊢
  exact (isConj_iff.mpr ⟨h⁻¹, by group⟩).trans hx

open Classical in
/-- **A nontrivial element whose class size is a power of $p$.** Let $p$ and $q$ be primes, let
$a$ and $b$ be natural numbers with $b \ge 1$, and let $G$ be a finite group of order
$p^a q^b$. Then there are an element $g \ne 1$ of $G$ and a natural number $k \le a$ such that
the conjugacy class of $g$ has exactly $p^k$ elements.

In the proof, $g$ is a nontrivial element of the center of a subgroup of $G$ of order $q^b$
(a Sylow $q$-subgroup when $p \ne q$). -/
theorem exists_ne_one_class_prime_pow {p q a b : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hcard : Fintype.card G = p ^ a * q ^ b) (hb : 1 ≤ b) :
    ∃ g : G, g ≠ 1 ∧ ∃ k ≤ a, (conjClass g).card = p ^ k := by
  have : Fact (Nat.Prime q) := ⟨hq⟩
  have hqdvd : q ^ b ∣ Nat.card G := by
    rw [Nat.card_eq_fintype_card, hcard]
    exact ⟨p ^ a, by ring⟩
  obtain ⟨H, hHcard⟩ := Sylow.exists_subgroup_card_pow_prime q hqdvd
  have hHQ : IsPGroup q H := IsPGroup.of_card hHcard
  have hcardH : 1 < Fintype.card H := by
    rw [← Nat.card_eq_fintype_card, hHcard]
    exact one_lt_pow₀ hq.one_lt (by omega)
  have : Nontrivial H := Fintype.one_lt_card_iff_nontrivial.mp hcardH
  have hnt := IsPGroup.center_nontrivial hHQ
  obtain ⟨gH, hgH⟩ := exists_ne (1 : Subgroup.center H)
  refine ⟨((gH : H) : G), ?_, ?_⟩
  · intro hcon
    apply hgH
    have h1 : (gH : H) = 1 := Subtype.ext_iff.mpr hcon
    exact Subtype.ext_iff.mpr h1
  · have hle : H ≤ Subgroup.centralizer {((gH : H) : G)} := by
      intro h hh
      rw [Subgroup.mem_centralizer_iff]
      simp only [Set.mem_singleton_iff, forall_eq]
      have hmem := Subgroup.mem_center_iff.mp gH.property ⟨h, hh⟩
      have hcoe := congrArg (fun x : H => (x : G)) hmem
      rw [Subgroup.coe_mul, Subgroup.coe_mul] at hcoe
      exact hcoe.symm
    set g : G := ((gH : H) : G) with hg
    have hdvd : q ^ b ∣ Fintype.card (Subgroup.centralizer {g}) := by
      have h1 : Nat.card H ∣ Nat.card (Subgroup.centralizer {g}) :=
        Subgroup.card_dvd_of_le hle
      rw [hHcard] at h1
      rwa [Nat.card_eq_fintype_card] at h1
    have hclass := conjClass_card_mul_centralizer_card g
    rw [hcard] at hclass
    obtain ⟨t, ht⟩ := hdvd
    have hcancel : (conjClass g).card * t * q ^ b = p ^ a * q ^ b := by
      calc (conjClass g).card * t * q ^ b
          = (conjClass g).card * (q ^ b * t) := by ring
        _ = (conjClass g).card * Fintype.card (Subgroup.centralizer {g}) := by rw [ht]
        _ = p ^ a * q ^ b := hclass
    have hct : (conjClass g).card * t = p ^ a :=
      mul_right_cancel₀ (pow_ne_zero b hq.ne_zero) hcancel
    exact (Nat.dvd_prime_pow hp).mp ⟨t, hct.symm⟩

end

end BurnsidePaqb
