/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import Mathlib.Data.Fintype.Basic
public import MathlibExt.Combinatorics.SetFamily.UniformHypergraph
/-!
Turan systems after Liu and Pikhurko,
"A note on the minimum size of Turán systems" (arXiv:2501.15457v2).
Tracks source lines 138-139, 148, and 150-152 for the covering definition.
-/
@[expose] public section
namespace TuranSystem
/-- **Turán system.** Let $n$, $s$, $r$ be natural numbers. A family $H$ of subsets of
$\{0, 1, \dots, n-1\}$ is a Turán $(n, s, r)$-system when $0 < r < s \le n$, $H$ is
$r$-uniform (every member of $H$ has exactly $r$ elements), and every $s$-element subset of
$\{0, 1, \dots, n-1\}$ contains some member of $H$. -/
public def IsTuranSystem (n s r : ℕ) (H : Finset (Finset (Fin n))) : Prop :=
  0 < r ∧ r < s ∧ s ≤ n ∧ SetFamily.IsUniform H r ∧
    ∀ T ∈ Finset.powersetCard s (Finset.univ : Finset (Fin n)), ∃ e ∈ H, e ⊆ T
/-- **Turán systems have positive uniformity.** Let $n$, $s$, $r$ be natural numbers and let $H$
be a Turán system with parameters $n$, $s$, $r$, whose definition includes $0 < r < s \le n$.
Then $0 < r$. -/
public theorem pos_of_isTuran (n s r : ℕ) (H : Finset (Finset (Fin n)))
    (h : IsTuranSystem n s r H) : 0 < r := h.1
/-- **A Turán system has $r < s$.** Let $n$, $s$, $r$ be natural numbers and let $H$ be a
Turán $(n, s, r)$-system. Then $r < s$. -/
public theorem lt_of_isTuran (n s r : ℕ) (H : Finset (Finset (Fin n)))
    (h : IsTuranSystem n s r H) : r < s := h.2.1
/-- **A Turán system has $s \le n$.** Let $n$, $s$, $r$ be natural numbers and let $H$ be a
Turán $(n, s, r)$-system. Then $s \le n$. -/
public theorem le_of_isTuran (n s r : ℕ) (H : Finset (Finset (Fin n)))
    (h : IsTuranSystem n s r H) : s ≤ n := h.2.2.1
/-- **Turán systems are uniform.** Let $n$, $s$, $r$ be natural numbers. If $H$ is a Turán system
with parameters $n$, $s$, $r$, then $H$ is $r$-uniform: every member of $H$ has exactly $r$
elements. -/
public theorem uniform_of_isTuran (n s r : ℕ) (H : Finset (Finset (Fin n)))
    (h : IsTuranSystem n s r H) : SetFamily.IsUniform H r := h.2.2.2.1
/-- **Turán systems cover every $s$-set.** Let $n$, $s$, $r$ be natural numbers and let $H$ be a
Turán $(n, s, r)$-system. Then every $s$-element subset $T$ of $\{0, 1, \dots, n-1\}$ contains
some member $e$ of $H$. -/
public theorem cover_of_isTuran (n s r : ℕ) (H : Finset (Finset (Fin n)))
    (h : IsTuranSystem n s r H) :
    ∀ T ∈ Finset.powersetCard s (Finset.univ : Finset (Fin n)),
      ∃ e ∈ H, e ⊆ T := h.2.2.2.2
/-- **The complete $r$-graph.** For natural numbers $n$ and $r$, the complete $r$-graph on $n$
vertices is the family of all $r$-element subsets of $\{0, 1, \dots, n-1\}$. -/
public def completeGraph (n r : ℕ) : Finset (Finset (Fin n)) :=
  Finset.powersetCard r (Finset.univ : Finset (Fin n))
/-- **The complete $r$-graph is $r$-uniform.** For all natural numbers $n$ and $r$, every member
of the complete $r$-graph on $\{0, 1, \dots, n-1\}$ has exactly $r$ elements. -/
public theorem completeGraph_uniform (n r : ℕ) :
    SetFamily.IsUniform (completeGraph n r) r := by
  intro e he
  exact (Finset.mem_powersetCard.mp he).2
/-- **The complete $r$-graph is a Turán system.** Let $n$, $s$, $r$ be natural numbers with
$0 < r < s \le n$. Then the complete $r$-graph on $\{0, 1, \dots, n-1\}$ (the family of all its
$r$-element subsets) is a Turán $(n, s, r)$-system. -/
public theorem completeGraph_isTuran (n s r : ℕ)
    (hd : 0 < r ∧ r < s ∧ s ≤ n) :
    IsTuranSystem n s r (completeGraph n r) := by
  refine ⟨hd.1, hd.2.1, hd.2.2, completeGraph_uniform n r, ?_⟩
  intro T hT
  have hTs : T.card = s := (Finset.mem_powersetCard.mp hT).2
  have hle : r ≤ T.card := by rw [hTs]; exact Nat.le_of_lt hd.2.1
  obtain ⟨S, hST, hSc⟩ := Finset.exists_subset_card_eq hle
  exact ⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ S, hSc⟩, hST⟩
/-- **Realized sizes of Turán systems.** For natural numbers $n$, $s$, $r$, the set of realized
sizes is the set of natural numbers $k$ such that some Turán system with parameters $n$, $s$, $r$
on the vertex set $\{0, \dots, n-1\}$ has exactly $k$ members. -/
public def realizedCounts (n s r : ℕ) : Set ℕ :=
  { k | ∃ H, IsTuranSystem n s r H ∧ H.card = k }
/-- **Membership in the realized sizes.** For natural numbers $n$, $s$, $r$, $k$, the number $k$
lies in the set of realized sizes for $(n, s, r)$ if and only if some Turán $(n, s, r)$-system
$H$ has exactly $k$ members. -/
public theorem mem_realizedCounts (n s r k : ℕ) :
    k ∈ realizedCounts n s r ↔ ∃ H, IsTuranSystem n s r H ∧ H.card = k :=
  Iff.rfl
/-- **Turán systems exist.** For all natural numbers $n$, $s$, $r$ with $0 < r < s \le n$, there
is a Turán $(n, s, r)$-system. -/
public theorem exists_system (n s r : ℕ) (hd : 0 < r ∧ r < s ∧ s ≤ n) :
    ∃ H, IsTuranSystem n s r H :=
  ⟨_, completeGraph_isTuran n s r hd⟩
/-- **Some size of a Turán system is realized.** For natural numbers $n$, $s$, $r$ with
$0 < r < s \le n$, the set of realized sizes for $n$, $s$, $r$ is nonempty: some natural number
$k$ is the number of members of a Turán system with parameters $n$, $s$, $r$. -/
public theorem realizedCounts_nonempty (n s r : ℕ)
    (hd : 0 < r ∧ r < s ∧ s ≤ n) : ∃ k, k ∈ realizedCounts n s r :=
  ⟨_, _, completeGraph_isTuran n s r hd, rfl⟩
/-- **Turán number.** For natural numbers $n$, $s$, $r$, the Turán number $T(n, s, r)$ is the
least element of the set of realized sizes for $n$, $s$, $r$, that is, the least number of members
of a Turán system with parameters $n$, $s$, $r$, and $T(n, s, r) = 0$ if no such system exists. -/
public noncomputable def turanNumber (n s r : ℕ) : ℕ := by
  classical
  exact if h : ∃ k, k ∈ realizedCounts n s r then Nat.find h else 0
/-- **The Turán number is a realized size.** Let $n$, $s$, $r$ be natural numbers with
$0 < r < s \le n$ and let $T(n, s, r)$ denote the Turán number. Then $T(n, s, r)$ belongs to the
set of realized sizes for $n$, $s$, $r$. -/
public theorem turanNumber_mem (n s r : ℕ) (hd : 0 < r ∧ r < s ∧ s ≤ n) :
    turanNumber n s r ∈ realizedCounts n s r := by
  classical
  have hex : ∃ k, k ∈ realizedCounts n s r := realizedCounts_nonempty n s r hd
  rw [turanNumber, dite_eq_left hex]
  exact Nat.find_spec hex
/-- **The Turán number is attained.** Let $n$, $s$, $r$ be natural numbers with $0 < r < s \le n$
and let $T(n, s, r)$ denote the Turán number. Then some Turán system with parameters $n$, $s$,
$r$ has exactly $T(n, s, r)$ members. -/
public theorem turanNumber_attains (n s r : ℕ)
    (hd : 0 < r ∧ r < s ∧ s ≤ n) :
    ∃ H, IsTuranSystem n s r H ∧ H.card = turanNumber n s r := by
  obtain ⟨H, hH, hcard⟩ := turanNumber_mem n s r hd
  exact ⟨H, hH, hcard⟩
/-- **Turán systems are at least as large as the Turán number.** Let $n$, $s$, $r$ be natural
numbers and let $T(n, s, r)$ denote the Turán number. If $H$ is a Turán system with parameters
$n$, $s$, $r$, then $T(n, s, r) \le |H|$. -/
public theorem turanNumber_le (n s r : ℕ) (H : Finset (Finset (Fin n)))
    (hH : IsTuranSystem n s r H) : turanNumber n s r ≤ H.card := by
  classical
  have hex : ∃ k, k ∈ realizedCounts n s r := ⟨_, _, hH, rfl⟩
  rw [turanNumber, dite_eq_left hex]
  exact Nat.find_min' hex ⟨H, hH, rfl⟩
/-- **Lower bounds on the Turán number.** Let $n$, $s$, $r$, $b$ be natural numbers with
$0 < r < s \le n$. If $b \le k$ for every $k$ in the set of realized sizes for $(n, s, r)$
(the sizes of Turán $(n, s, r)$-systems), then $b$ is at most the Turán number $T(n, s, r)$. -/
public theorem le_turanNumber (n s r b : ℕ)
    (hb : ∀ k ∈ realizedCounts n s r, b ≤ k)
    (hd : 0 < r ∧ r < s ∧ s ≤ n) : b ≤ turanNumber n s r :=
  hb _ (turanNumber_mem n s r hd)
end TuranSystem
