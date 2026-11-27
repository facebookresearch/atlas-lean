/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.Pi
public import MathlibExt.Combinatorics.SimpleGraph.SnortOppositions
import Mathlib.Data.Fin.Rev

/-!
# Almost opposability of strong grids

A strong grid of positive dimension and positive side lengths is almost opposable.
Reflect all coordinates and delete the block consisting of the middle one or two vertices
in each coordinate. The block lies in the closed neighbourhood of its lower middle vertex.
The reflection restricts to an opposition on the remaining vertices, using the involution
convention for an opposition even when no vertices remain.

## References

* Rylo Ashmore, Beth Ann Austin, Alfie M. Davies, Danny Dyer, and William Kellough,
  *On Graph Automorphisms Related to SNORT*, INTEGERS 26 (2026), Article G2, pp. 1–28,
  Corollary 3 and Theorem 5 (coordinate reflection and deletion in the strong product).
* Keiko Kakihara, *Snort: A combinatorial game*, master's thesis, California State University,
  San Bernardino, 2010, Section 3 (opposable graphs, as credited in Section 1 of Ashmore et al.).
* Edward Arroyo, *Dawson’s Chess, Snort on Graphs and Graph Involutions*, Ph.D. thesis, City
  University of New York, 1998, for the precursor to almost opposability cited in Section 4
  of Ashmore et al.
* `MathlibExt.Combinatorics.SimpleGraph.CompatibleOppositionProducts`,
  `isCompatiblyAlmostOpposable_strongProd` (restricting a product automorphism).
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Strong grid.** For $k \in \mathbb{N}$ and natural numbers $n_0, \dots, n_{k-1}$, the
$k$-dimensional strong grid $P_{n_0} \boxtimes \cdots \boxtimes P_{n_{k-1}}$ is the simple
graph whose vertices are the tuples $(x_0, \dots, x_{k-1})$ of integers with $0 \le x_i < n_i$
for each $i$, in which two vertices $x$ and $y$ are adjacent if and only if $x \ne y$ and
$|x_i - y_i| \le 1$ for every $i$.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Corollary 3 (strong
grids). -/
def strongGrid {k : ℕ} (n : Fin k → ℕ) : SimpleGraph ((i : Fin k) → Fin (n i)) :=
  SimpleGraph.fromRel fun x y => ∀ i, (x i : ℕ) ≤ y i + 1 ∧ (y i : ℕ) ≤ x i + 1

instance {k : ℕ} (n : Fin k → ℕ) : DecidableRel (strongGrid n).Adj := fun x y =>
  inferInstanceAs (Decidable (x ≠ y ∧ _))

/-- **Almost opposability of strong grids.** Let $k \ge 1$ and $n_1, \dots, n_k \ge 1$. Then the
$k$-dimensional strong grid $P_{n_1} \boxtimes \cdots \boxtimes P_{n_k}$, the strong product of the
paths $P_{n_i}$ on $n_i$ vertices, is almost opposable.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Corollary 3. -/
public theorem isAlmostOpposable_strongGrid {k : ℕ} (hk : 1 ≤ k) (n : Fin k → ℕ)
    (hn : ∀ i, 1 ≤ n i) : IsAlmostOpposable (strongGrid n) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  let V := (i : Fin (d + 1)) → Fin (n i)
  let near (x y : V) : Prop := ∀ i, (x i : ℕ) ≤ y i + 1 ∧ (y i : ℕ) ≤ x i + 1
  have near_comm (x y : V) : near x y ↔ near y x := forall_congr' fun _ => and_comm
  have adj_iff (x y : V) : (strongGrid n).Adj x y ↔ x ≠ y ∧ near x y := by
    change x ≠ y ∧ (near x y ∨ near y x) ↔ x ≠ y ∧ near x y
    rw [near_comm y x, or_self]
  let r : Equiv.Perm V := Equiv.piCongrRight fun _ => Fin.revPerm
  have rev_val (x : V) (i : Fin (d + 1)) : (r x i : ℕ) = n i - (x i + 1) := Fin.val_rev _
  have hr : Function.Involutive r := fun x => funext fun i => Fin.rev_rev (x i)
  have near_rev (x y : V) : near (r x) (r y) ↔ near x y := by
    simp only [near, rev_val]
    refine forall_congr' fun i => ?_
    have hx := (x i).isLt
    have hy := (y i).isLt
    omega
  let α : strongGrid n ≃g strongGrid n := ⟨r, by
    intro x y
    simp only [adj_iff, ne_eq, r.injective.eq_iff, near_rev]⟩
  let u : V := fun i => ⟨(n i - 1) / 2, by have := hn i; omega⟩
  have u_val (i : Fin (d + 1)) : (u i : ℕ) = (n i - 1) / 2 := rfl
  let S : Set V := {x | near x (r x)}
  refine ⟨u, S, ?_, ?_, ?_⟩
  · intro i
    simp only [rev_val, u_val]
    have hi := hn i
    omega
  · intro x hx
    rw [Set.mem_insert_iff, SimpleGraph.mem_neighborSet, adj_iff]
    by_cases h : u = x
    · exact Or.inl h.symm
    · refine Or.inr ⟨h, fun i => ?_⟩
      have hi := hx i
      simp only [rev_val] at hi
      rw [u_val]
      have hxi := (x i).isLt
      omega
  -- Reversing coordinates swaps the two vertices in the defining test for membership in `S`.
  have mem_rev (x : V) : r x ∈ S ↔ x ∈ S := by
    change near (r x) (r (r x)) ↔ near x (r x)
    rw [hr x, near_comm (r x) x]
  let f := α.induce (r.bijOn (fun x => not_congr (mem_rev x)) : Set.BijOn α Sᶜ Sᶜ)
  refine ⟨f, fun x => ⟨Subtype.ext (hr x.val), ?_, ?_⟩⟩
  · intro h
    have he : r x.val = x.val := congrArg Subtype.val h
    apply x.property
    change near x.val (r x.val)
    rw [he]
    exact fun i => ⟨Nat.le_succ (x.val i), Nat.le_succ (x.val i)⟩
  · intro h
    exact x.property ((adj_iff x.val (r x.val)).mp h).2

end

end MetaMathlibExt
