/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.SnortOppositions

/-!
# Strong products of compatibly almost opposable graphs

The product of the two involutions restricts to an opposition outside the product of the
admissible sets.

## References

* Rylo Ashmore, Beth Ann Austin, Alfie M. Davies, Danny Dyer, and William Kellough,
  *On Graph Automorphisms Related to SNORT*, INTEGERS 26 (2026), Article G2, pp. 1–28,
  Definition 6 and Theorem 5.
* Edward Arroyo, *Dawson’s Chess, Snort on Graphs and Graph Involutions*, Ph.D. thesis,
  City University of New York, 1998, for the single-fixed-point precursor cited in Section 4
  of Ashmore et al.
* Keiko Kakihara, *Snort: a combinatorial game*, master’s thesis, California State University,
  San Bernardino, 2010, for opposable graphs as credited in Section 1 of Ashmore et al.
* Wilfried Imrich and Sandi Klavžar, *Product Graphs: Structure and Recognition*,
  Wiley-Interscience, 2000, §5.1, for the strong graph product.
-/

namespace MetaMathlibExt

@[expose] public section

variable {V W : Type*}

/-- **Compatibly almost opposable graphs.** A graph $G$ is compatibly almost opposable if there
are a vertex $u$, a set $S$ of vertices with $u \in S \subseteq N[u]$ (the closed neighbourhood
of $u$), an automorphism $\alpha$ of $G$ with $\alpha(\alpha(v)) = v$ for every vertex $v$, and
an opposition $f$ of the subgraph $G - S$ induced on the vertices outside $S$, such that
$\alpha(x) = f(x)$ for every vertex $x \notin S$.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Section 4 (compatibly almost opposable
graphs). -/
def IsCompatiblyAlmostOpposable (G : SimpleGraph V) : Prop :=
  ∃ u : V, ∃ S : Set V, u ∈ S ∧ S ⊆ insert u (G.neighborSet u) ∧
    ∃ α : G ≃g G, (∀ v, α (α v) = v) ∧
      ∃ f : G.induce Sᶜ ≃g G.induce Sᶜ, IsOpposition _ f ∧ ∀ x : ↥Sᶜ, α x = (f x : V)

/-- **Compatible almost opposability via the ambient involution.** A graph $G$ is compatibly
almost opposable if and only if there are a vertex $u$, a set $S$ with $u \in S \subseteq N_G[u]$,
and an involutive automorphism $\alpha$ of $G$ such that for every $x \notin S$,
$\alpha(x) \notin S$ and $x\alpha(x) \in E(\overline{G})$. -/
theorem isCompatiblyAlmostOpposable_iff_exists_involution (G : SimpleGraph V) :
    IsCompatiblyAlmostOpposable G ↔
      ∃ (u : V) (S : Set V), u ∈ S ∧ S ⊆ insert u (G.neighborSet u) ∧
        ∃ α : G ≃g G, Function.Involutive α ∧ ∀ x ∉ S, α x ∉ S ∧ Gᶜ.Adj x (α x) := by
  constructor
  · rintro ⟨u, S, hu, hS, α, hα, h⟩
    exact ⟨u, S, hu, hS, α, hα, (exists_compatible_opposition_iff hα).mp h⟩
  · rintro ⟨u, S, hu, hS, α, hα, h⟩
    exact ⟨u, S, hu, hS, α, hα, (exists_compatible_opposition_iff hα).mpr h⟩

/-- **Strong products of compatibly almost opposable graphs.** If $G$ and $H$ are compatibly
almost opposable graphs, then their strong product $G \boxtimes H$ is compatibly almost
opposable.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Theorem 5. -/
public theorem isCompatiblyAlmostOpposable_strongProd [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hG : IsCompatiblyAlmostOpposable G) (hH : IsCompatiblyAlmostOpposable H) :
    IsCompatiblyAlmostOpposable (strongProd G H) := by
  obtain ⟨u, S, hu, hS, a, ha, hleft⟩ :=
    (isCompatiblyAlmostOpposable_iff_exists_involution G).mp hG
  obtain ⟨v, T, hv, hT, b, hb, hright⟩ :=
    (isCompatiblyAlmostOpposable_iff_exists_involution H).mp hH
  let α : strongProd G H ≃g strongProd G H :=
    ⟨a.toEquiv.prodCongr b.toEquiv, by
      intro x y
      change (strongProd G H).Adj (a x.1, b x.2) (a y.1, b y.2) ↔ (strongProd G H).Adj x y
      simp only [strongProd_adj, a.injective.eq_iff, b.injective.eq_iff,
        a.map_adj_iff, b.map_adj_iff]⟩
  have hinv : Function.Involutive α := fun x => Prod.ext (ha x.1) (hb x.2)
  refine (isCompatiblyAlmostOpposable_iff_exists_involution _).mpr
    ⟨(u, v), S ×ˢ T, ⟨hu, hv⟩, ?_, α, hinv, ?_⟩
  · intro x hx
    have hleft := Set.mem_insert_iff.mp (hS hx.1)
    have hright := Set.mem_insert_iff.mp (hT hx.2)
    simp only [SimpleGraph.mem_neighborSet] at hleft hright
    simp only [Set.mem_insert_iff, SimpleGraph.mem_neighborSet, Prod.ext_iff, strongProd_adj]
    change (x.1 = u ∧ x.2 = v) ∨ (u = x.1 ∧ H.Adj v x.2) ∨
      (G.Adj u x.1 ∧ v = x.2) ∨ (G.Adj u x.1 ∧ H.Adj v x.2)
    rw [eq_comm (a := u), eq_comm (a := v)]
    tauto
  · rintro ⟨x, y⟩ hxy
    change (a x, b y) ∉ S ×ˢ T ∧ (strongProd G H)ᶜ.Adj (x, y) (a x, b y)
    simp only [Set.mem_prod, SimpleGraph.compl_adj, ne_eq, Prod.mk.injEq, strongProd_adj] at hxy ⊢
    rcases not_and_or.mp hxy with hx | hy
    · obtain ⟨hmem, hfar⟩ := hleft x hx
      have ⟨hne, hnadj⟩ := (G.compl_adj _ _).mp hfar
      tauto
    · obtain ⟨hmem, hfar⟩ := hright y hy
      have ⟨hne, hnadj⟩ := (H.compl_adj _ _).mp hfar
      tauto

end

end MetaMathlibExt
