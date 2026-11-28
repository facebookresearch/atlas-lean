/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.CompatibleOppositionProducts

/-!
# Cartesian products of compatibly almost opposable graphs

If $G$ and $H$ are compatibly almost opposable and deleting a single vertex $u$ of $G$ leaves
an opposition that extends to an involutive automorphism of $G$, then $G \square H$ is compatibly
almost opposable. For an admissible deletion set $T$ in $H$, delete $\{u\} \times T$ and use
the product of the ambient involutions. As for `IsOpposition`, the order-two condition is read
as involutivity, so the restriction is allowed even when no vertices remain.

## References

* Rylo Ashmore, Beth Ann Austin, Alfie M. Davies, Danny Dyer, and William Kellough,
  *On Graph Automorphisms Related to SNORT*, INTEGERS 26 (2026), Article G2, pp. 1–28,
  Theorem 7 (p. 19), using the restriction argument of Theorem 5.
* Edward Arroyo, *Dawson’s Chess, Snort on Graphs and Graph Involutions*, Ph.D. thesis, City
  University of New York, 1998, for the precursor to almost opposability cited in Section 4
  of Ashmore et al.
* Keiko Kakihara, *Snort: a combinatorial game*, master’s thesis, California State University,
  San Bernardino, 2010, Section 3 (opposable graphs, as credited in Section 1 of Ashmore et al.).
* `MathlibExt.Combinatorics.SimpleGraph.CompatibleOppositionProducts`,
  `isCompatiblyAlmostOpposable_strongProd` (the coordinatewise automorphism and the surviving
  coordinate argument).
-/

namespace MetaMathlibExt

variable {V W : Type*}

-- The published hypotheses include `hG`, although it follows from the singleton witness.
set_option linter.unusedVariables false in
/-- **Cartesian products of compatibly almost opposable graphs.** Let $G$ and $H$ be compatibly
almost opposable graphs. Suppose that for some vertex $u$ of $G$ there are an involutive
automorphism $\alpha$ of $G$ and an opposition $f$ of the induced subgraph $G - u$ on the vertices
other than $u$ such that $\alpha(x) = f(x)$ for every vertex $x \neq u$. Then the Cartesian product
$G \square H$ is compatibly almost opposable.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Theorem 7. -/
public theorem isCompatiblyAlmostOpposable_boxProd (G : SimpleGraph V)
    (H : SimpleGraph W) (hG : IsCompatiblyAlmostOpposable G) (hH : IsCompatiblyAlmostOpposable H)
    (hu : ∃ u : V, ∃ α : G ≃g G, (∀ v, α (α v) = v) ∧
      ∃ f : G.induce ({u}ᶜ : Set V) ≃g G.induce ({u}ᶜ : Set V),
        IsOpposition _ f ∧ ∀ x : ↥({u}ᶜ : Set V), α x = (f x : V)) :
    IsCompatiblyAlmostOpposable (G □ H) := by
  obtain ⟨u, α, hα, hf⟩ := hu
  have hleft := (exists_compatible_opposition_iff (S := ({u} : Set V)) hα).mp hf
  obtain ⟨v, T, hv, hT, β, hβ, hright⟩ :=
    (isCompatiblyAlmostOpposable_iff_exists_involution H).mp hH
  let γ : G □ H ≃g G □ H :=
    ⟨α.toEquiv.prodCongr β.toEquiv, by
      intro x y
      change (G □ H).Adj (α x.1, β x.2) (α y.1, β y.2) ↔ (G □ H).Adj x y
      simp only [SimpleGraph.boxProd_adj, α.map_adj_iff, β.map_adj_iff,
        α.injective.eq_iff, β.injective.eq_iff]⟩
  refine (isCompatiblyAlmostOpposable_iff_exists_involution (G □ H)).mpr
    ⟨(u, v), {u} ×ˢ T, ⟨Set.mem_singleton u, hv⟩, ?_, γ,
      fun x => Prod.ext (hα x.1) (hβ x.2), ?_⟩
  · rintro ⟨x, y⟩ ⟨hx, hy⟩
    obtain rfl := Set.mem_singleton_iff.mp hx
    rcases Set.mem_insert_iff.mp (hT hy) with rfl | hadj
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (SimpleGraph.boxProd_adj_right.mpr hadj)
  · rintro ⟨x, y⟩ hxy
    -- A surviving coordinate stays outside its deleted set and rules out both kinds of edge.
    change (α x, β y) ∉ {u} ×ˢ T ∧ (G □ H)ᶜ.Adj (x, y) (α x, β y)
    simp only [Set.mem_prod, SimpleGraph.compl_adj, ne_eq, Prod.mk.injEq,
      SimpleGraph.boxProd_adj] at hxy ⊢
    rcases not_and_or.mp hxy with hx | hy
    · obtain ⟨hmem, hfar⟩ := hleft x hx
      have ⟨hne, hnadj⟩ := (G.compl_adj _ _).mp hfar
      tauto
    · obtain ⟨hmem, hfar⟩ := hright y hy
      have ⟨hne, hnadj⟩ := (H.compl_adj _ _).mp hfar
      tauto

end MetaMathlibExt
