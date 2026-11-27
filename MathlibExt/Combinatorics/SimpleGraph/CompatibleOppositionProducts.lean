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

private theorem compatible_outside {G : SimpleGraph V} {S : Set V} {a : G ≃g G}
    {f : G.induce Sᶜ ≃g G.induce Sᶜ} (hf : IsOpposition _ f)
    (hcompat : ∀ x : ↥Sᶜ, a x = (f x : V)) {x : V} (hx : x ∉ S) :
    a x ∉ S ∧ a x ≠ x ∧ ¬ G.Adj x (a x) := by
  let x' : ↥Sᶜ := ⟨x, hx⟩
  rw [hcompat x']
  exact ⟨(f x').2, fun h => (hf x').2.1 (Subtype.ext h), (hf x').2.2⟩

/-- **Strong products of compatibly almost opposable graphs.** If $G$ and $H$ are compatibly
almost opposable graphs, then their strong product $G \boxtimes H$ is compatibly almost
opposable.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Theorem 5. -/
public theorem isCompatiblyAlmostOpposable_strongProd [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hG : IsCompatiblyAlmostOpposable G) (hH : IsCompatiblyAlmostOpposable H) :
    IsCompatiblyAlmostOpposable (strongProd G H) := by
  obtain ⟨u, S, hu, hS, a, ha, f, hf, hfa⟩ := hG
  obtain ⟨v, T, hv, hT, b, hb, g, hg, hgb⟩ := hH
  let α : strongProd G H ≃g strongProd G H :=
    ⟨a.toEquiv.prodCongr b.toEquiv, by
      intro x y
      change (strongProd G H).Adj (a x.1, b x.2) (a y.1, b y.2) ↔ (strongProd G H).Adj x y
      simp only [strongProd_adj, a.injective.eq_iff, b.injective.eq_iff,
        a.map_adj_iff, b.map_adj_iff]⟩
  have hinv : Function.Involutive α := fun x => Prod.ext (ha x.1) (hb x.2)
  refine ⟨(u, v), S ×ˢ T, ⟨hu, hv⟩, ?_, α, hinv, ?_⟩
  · intro x hx
    have hleft := Set.mem_insert_iff.mp (hS hx.1)
    have hright := Set.mem_insert_iff.mp (hT hx.2)
    simp only [SimpleGraph.mem_neighborSet] at hleft hright
    simp only [Set.mem_insert_iff, SimpleGraph.mem_neighborSet, Prod.ext_iff, strongProd_adj]
    change (x.1 = u ∧ x.2 = v) ∨ (u = x.1 ∧ H.Adj v x.2) ∨
      (G.Adj u x.1 ∧ v = x.2) ∨ (G.Adj u x.1 ∧ H.Adj v x.2)
    rw [eq_comm (a := u), eq_comm (a := v)]
    tauto
  -- A surviving coordinate stays outside its deleted set and rules out both equality
  -- and adjacency of the entire pair.
  have houtside (x : ↥(S ×ˢ T)ᶜ) :
      α x ∈ (S ×ˢ T)ᶜ ∧ α x ≠ x.val ∧ ¬ (strongProd G H).Adj x (α x) := by
    have hx : ¬ (x.val.1 ∈ S ∧ x.val.2 ∈ T) := x.2
    change (a x.val.1, b x.val.2) ∈ (S ×ˢ T)ᶜ ∧ (a x.val.1, b x.val.2) ≠ x.val ∧
      ¬ (strongProd G H).Adj x.val (a x.val.1, b x.val.2)
    simp only [Set.mem_compl_iff, Set.mem_prod, ne_eq, Prod.ext_iff, strongProd_adj]
    rw [eq_comm (a := x.val.1), eq_comm (a := x.val.2)]
    rcases not_and_or.mp hx with hx | hx
    · obtain ⟨hmem, hne, hnadj⟩ := compatible_outside hf hfa hx
      tauto
    · obtain ⟨hmem, hne, hnadj⟩ := compatible_outside hg hgb hx
      tauto
  have hmaps : Set.MapsTo α (S ×ˢ T)ᶜ (S ×ˢ T)ᶜ := fun x hx => (houtside ⟨x, hx⟩).1
  have hbij : Set.BijOn α (S ×ˢ T)ᶜ (S ×ˢ T)ᶜ :=
    ⟨hmaps, α.injective.injOn, fun x hx => ⟨α x, hmaps hx, hinv x⟩⟩
  refine ⟨α.induce hbij, ?_, fun _ => rfl⟩
  intro x
  obtain ⟨_, hne, hnadj⟩ := houtside x
  exact ⟨Subtype.ext (hinv x), fun h => hne (congrArg Subtype.val h), hnadj⟩

end

end MetaMathlibExt
