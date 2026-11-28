/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Log
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.PGroup

@[expose] public section

/-!
# Breadth of elements and finite groups

The breadth of an element `g` is the exponent `br(g)` with
`p ^ br(g) = |g^G|`, recovered as the base-`p` logarithm of the
conjugacy-class size. The breadth of a finite group is the maximum
element breadth. Every conjugacy-class size in a finite `p`-group is a
power of `p`, so the logarithm recovers the exact exponent.
-/

namespace ClassBreadth

variable {G : Type*} [Group G]

/-- **Breadth of an element.** Let $G$ be a finite group, $p$ a natural number and $g \in G$,
and write $g^G$ for the conjugacy class of $g$. When $p \ge 2$, the breadth
$\operatorname{br}_p(g)$ of $g$ is $\lfloor \log_p |g^G| \rfloor$, the largest natural number
$k$ with $p^k \le |g^G|$; when $p \le 1$, it is $0$.

If $p$ is prime and $G$ is a $p$-group, then $|g^G|$ is a power of $p$, so
$p^{\operatorname{br}_p(g)} = |g^G|$. -/
noncomputable def elementBreadth [Finite G] (p : ℕ) (g : G) : ℕ :=
  Nat.log p (Nat.card (ConjClasses.mk g).carrier)

/-- **Breadth of a finite group.** For a finite group $G$ and a natural number $p$, the breadth
$\operatorname{br}_p(G)$ of $G$ is the maximum of the element breadths $\operatorname{br}_p(g)$
over all $g \in G$. -/
noncomputable def breadth (p : ℕ) (G : Type*) [Group G] [Fintype G] : ℕ :=
  Finset.univ.sup (fun g : G ↦ elementBreadth p g)

/-- **Conjugacy class sizes divide the group order.** In a finite group $G$, the number of
elements of the conjugacy class of any $g \in G$ divides the order $|G|$. -/
theorem card_carrier_dvd_card [Finite G] (g : G) :
    Nat.card (ConjClasses.mk g).carrier ∣ Nat.card G := by
  let _ := Fintype.ofFinite G
  classical
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) g
  rw [ConjAct.orbit_eq_carrier_conjClasses] at h
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact ⟨Fintype.card (MulAction.stabilizer (ConjAct G) g), h.symm⟩

/-- **Conjugacy classes of a finite $p$-group have $p$-power size.** Let $p$ be a prime and
$G$ a finite $p$-group. For every $g \in G$ there is a natural number $k$ such that the
conjugacy class of $g$ has exactly $p^k$ elements. -/
theorem exists_card_carrier_eq_pow (p : ℕ) [Finite G] [Fact p.Prime]
    (hG : IsPGroup p G) (g : G) :
    ∃ k : ℕ, Nat.card (ConjClasses.mk g).carrier = p ^ k := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hG
  have hdvd : Nat.card (ConjClasses.mk g).carrier ∣ p ^ n := hn ▸ card_carrier_dvd_card g
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Fact.out).mp hdvd
  exact ⟨k, hk⟩

/-- **Breadth from an exact class size.** Let $G$ be a finite group, $p$ a prime, $k$ a natural
number and $g \in G$. If the conjugacy class of $g$ has exactly $p^k$ elements, then the breadth
$\operatorname{br}_p(g)$ of $g$ equals $k$. -/
theorem elementBreadth_eq_of_card_eq [Finite G] {p k : ℕ} (hp : p.Prime) (g : G)
    (h : Nat.card (ConjClasses.mk g).carrier = p ^ k) :
    elementBreadth p g = k := by
  rw [elementBreadth, h, Nat.log_pow hp.one_lt]

/-- **Class sizes in a $p$-group via breadth.** Let $p$ be a prime, $G$ a finite $p$-group and
$g \in G$, and write $g^G$ for the conjugacy class of $g$. Then the breadth
$\operatorname{br}_p(g)$ of $g$ satisfies $p^{\operatorname{br}_p(g)} = |g^G|$. -/
theorem pow_elementBreadth_eq_card (p : ℕ) [Finite G] [Fact p.Prime]
    (hG : IsPGroup p G) (g : G) :
    p ^ elementBreadth p g = Nat.card (ConjClasses.mk g).carrier := by
  obtain ⟨k, hk⟩ := exists_card_carrier_eq_pow p hG g
  rw [elementBreadth_eq_of_card_eq Fact.out g hk, hk]

/-- **The conjugacy class of the identity.** In every group, the conjugacy class of the identity
element $1$ is the singleton $\{1\}$. -/
theorem carrier_mk_one : (ConjClasses.mk (1 : G)).carrier = {1} := by
  ext x
  simp [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj]

/-- **Breadth of the identity.** In a finite group, the breadth $\operatorname{br}_p(1)$ of the
identity element $1$ is $0$ for every natural number $p$. -/
theorem elementBreadth_one [Finite G] (p : ℕ) : elementBreadth p (1 : G) = 0 := by
  rw [elementBreadth, carrier_mk_one, Nat.card_unique, Nat.log_one_right]

/-- **Element breadth is at most the group breadth.** Let $G$ be a finite group and $p$ a
natural number. For every $g \in G$, the breadth $\operatorname{br}_p(g)$ of $g$ is at most
the breadth $\operatorname{br}_p(G)$ of $G$. -/
theorem elementBreadth_le_breadth (p : ℕ) [Fintype G] (g : G) :
    elementBreadth p g ≤ breadth p G :=
  Finset.le_sup (Finset.mem_univ g)

/-- **The group breadth is attained.** Let $G$ be a finite group and $p$ a natural number.
There is an element $g \in G$ whose breadth $\operatorname{br}_p(g)$ equals the breadth
$\operatorname{br}_p(G)$ of $G$. -/
theorem exists_breadth_eq_elementBreadth (p : ℕ) [Fintype G] [Nonempty G] :
    ∃ g : G, breadth p G = elementBreadth p g := by
  obtain ⟨g, -, hg⟩ := Finset.exists_mem_eq_sup Finset.univ
    Finset.univ_nonempty (fun g : G ↦ elementBreadth p g)
  exact ⟨g, hg⟩

end ClassBreadth
