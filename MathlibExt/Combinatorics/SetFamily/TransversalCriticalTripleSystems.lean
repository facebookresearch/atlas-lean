/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SetFamily.UniformHypergraph
import MathlibExt.Combinatorics.SetFamily.BollobasSetPairs
import Mathlib.Tactic.Choose

/-!
# Minimum degree of transversal-critical triple systems

We refute the transversal interpretation of Erdős Problem 834. Following Li's set-pairs
construction, we restrict to the edges through one vertex and remove that vertex before
applying Bollobás's inequality. This bounds the degree by six.

## Record carried over from the retired wanted module

From `WantedExt/Combinatorics/TransversalCriticalTripleSystemDegreeErdosProblem834Wanted.lean`:

Source: T. F. Bloom, Erdős Problems, Problem #834, https://www.erdosproblems.com/834 (status
SOLVED). UnsolvedMath record UM-30007054 (`EP-834`), dataset ulamai/UnsolvedMath v1.8.0.

Erdős and Lovász did not define `3`-critical. The page gives two definitions and records Li's
resolution of both. This module states the transversal one: there is a set of `3` vertices meeting
every edge, no such set of size `2`, and for every edge `e` a pair of vertices meeting every edge
except `e` (`τ(H) = 3` and `τ(H - e) ≤ 2`; transversals of size at most `t` are used, which is
equivalent once there are at least `t` vertices). Uniformity is MathlibExt's
`SetFamily.IsUniform`; the transversal conditions are written out in the target. The vertex set is
`Fin n`, and every vertex of it must have degree at least `7`. The chromatic reading is not
stated: Li answers it with one explicit `9`-vertex hypergraph, a finite check. Compared with the
formal-conjectures statement `ErdosProblems/834.lean` (equivalent to its part (i); no code
imported).
-/

@[expose] public section

namespace MathlibExt.Combinatorics.TransversalCriticalTripleSystemDegreeErdosProblem834Wanted

open Finset

/-- **Erdős Problem 834 for transversal-critical triple systems.** There exist $n \in \mathbb{N}$
and a $3$-uniform hypergraph $H$ on the vertex set $\{0, \dots, n-1\}$ such that some set of at
most $3$ vertices meets every edge of $H$, no set of at most $2$ vertices meets every edge of $H$,
for every edge $e$ of $H$ some set of at most $2$ vertices meets every edge of $H$ other than $e$,
and every vertex lies in at least $7$ edges of $H$.

Writing $\tau$ for the least size of a vertex set meeting every edge and $H - e$ for $H$ with the
edge $e$ removed, this asks for $\tau(H) = 3$ and $\tau(H - e) \le 2$ for every edge $e$, with
every vertex of degree at least $7$. -/
def transversalCriticalMinDegreeSeven : Prop :=
  ∃ (n : ℕ) (H : Finset (Finset (Fin n))), SetFamily.IsUniform H 3 ∧
    (∃ T : Finset (Fin n), T.card ≤ 3 ∧ ∀ f ∈ H, (f ∩ T).Nonempty) ∧
    (¬ ∃ T : Finset (Fin n), T.card ≤ 2 ∧ ∀ f ∈ H, (f ∩ T).Nonempty) ∧
    (∀ e ∈ H, ∃ T : Finset (Fin n), T.card ≤ 2 ∧ ∀ f ∈ H.erase e, (f ∩ T).Nonempty) ∧
    ∀ v : Fin n, 7 ≤ (H.filter (v ∈ ·)).card

/--
**Erdős Problem 834 fails for transversal-critical triple systems.** There are no
$n \in \mathbb{N}$ and $3$-uniform hypergraph $H$ on the vertex set $\{0, \dots, n-1\}$ such that
some set of at most $3$ vertices meets every edge of $H$, no set of at most $2$ vertices meets
every edge of $H$, for every edge $e$ of $H$ some set of at most $2$ vertices meets every edge of
$H$ other than $e$, and every vertex lies in at least $7$ edges of $H$.

Writing $\tau(H)$ for the least size of a vertex set meeting every edge of $H$ and $H - e$ for
$H$ with the edge $e$ removed, Li proved that a $3$-uniform hypergraph $H$ with $\tau(H) = 3$ and
$\tau(H - e) = 2$ for every edge $e$ has at most $10$ edges, so some vertex has degree at most $6$.

Source: T. F. Bloom, Erdős Problems, Problem #834, https://www.erdosproblems.com/834 (status
SOLVED); resolution: R. Li, On an Erdős-Lovász problem: 3-critical 3-graphs of minimum degree 7,
arXiv:2512.24850 (2025; unrefereed, accepted on erdosproblems.com/834), abstract and main theorem
for the transversal interpretation: a 3-uniform hypergraph H with τ(H) = 3 and τ(H - e) = 2 for
every edge e has at most 10 edges, in particular δ(H) ≤ 6, sharp for K₅⁽³⁾; erdosproblems.com/834:
'In the first formulation ... Li proves that a 3-critical 3-uniform hypergraph must have a vertex
of degree ≤ 6', https://arxiv.org/abs/2512.24850.
-/
public theorem transversalCriticalMinDegreeSeven_refuted :
    ¬ transversalCriticalMinDegreeSeven := by
  classical
  rintro ⟨n, H, htriple, ⟨S, _, hS⟩, hno, hcritical, hdeg⟩
  have hScard : 2 < S.card := lt_of_not_ge fun h => hno ⟨S, h, hS⟩
  obtain ⟨v, _⟩ := card_pos.mp (by omega : 0 < S.card)
  choose! T hsize hhit using hcritical
  -- A transversal after deletion must miss the deleted edge.
  have hdisj (e) (he : e ∈ H) : Disjoint e (T e) := by
    by_contra h
    refine hno ⟨T e, hsize e he, fun f hf => ?_⟩
    by_cases hfe : f = e
    · subst f
      exact not_disjoint_iff_nonempty_inter.mp h
    · exact hhit e he f (mem_erase.mpr ⟨hfe, hf⟩)
  let star := H.filter (v ∈ ·)
  have hbound : star.card ≤ (2 + 2).choose 2 := by
    apply SetFamily.BollobasSetPairs.card_le_choose star (fun e => e.erase v) T 2 2
    · intro e he
      obtain ⟨heH, hve⟩ := mem_filter.mp he
      rw [card_erase_of_mem hve, htriple e heH]
    · intro e he
      obtain ⟨heH, hve⟩ := mem_filter.mp he
      -- Adding v to a smaller deletion transversal would cover all of H with two vertices.
      apply le_antisymm (hsize e heH)
      by_contra! hsmall
      refine hno ⟨insert v (T e), (card_insert_le _ _).trans (by omega), fun f hf => ?_⟩
      by_cases hfe : f = e
      · subst f
        exact ⟨v, mem_inter.mpr ⟨hve, mem_insert_self ..⟩⟩
      · exact (hhit e heH f (mem_erase.mpr ⟨hfe, hf⟩)).mono
          (inter_subset_inter_left (subset_insert ..))
    · intro e he
      exact (hdisj e (mem_filter.mp he).1).mono_left (erase_subset ..)
    · intro e he f hf hef
      obtain ⟨hfH, hvf⟩ := mem_filter.mp hf
      obtain ⟨x, hx⟩ := hhit f hfH e (mem_erase.mpr ⟨hef, (mem_filter.mp he).1⟩)
      obtain ⟨hxe, hxT⟩ := mem_inter.mp hx
      have hvT := disjoint_left.mp (hdisj f hfH) hvf
      exact not_disjoint_iff.mpr ⟨x, mem_erase.mpr ⟨ne_of_mem_of_not_mem hxT hvT, hxe⟩, hxT⟩
  exact (by decide : ¬ 7 ≤ (2 + 2).choose 2) ((hdeg v).trans hbound)

end MathlibExt.Combinatorics.TransversalCriticalTripleSystemDegreeErdosProblem834Wanted
