/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Batteries.Util.ProofWanted

namespace MetaMathlibExt

@[expose] public section

/-- **Euler's polyhedron formula.** Let $V$, $E$ and $F$ be finite sets, let
$\iota : V \to \mathbb{R}^3$ be an injective map into Euclidean space, and let
$P = \operatorname{conv} \iota(V)$ be the convex hull of its image; assume $P$ has nonempty
interior $\operatorname{int} P$, and write $\partial P$ for its frontier. Each edge $e \in E$ has an
ordered pair of endpoints $(s(e), t(e)) \in V \times V$, with segment
$[e] = [\iota(s(e)), \iota(t(e))]$; each face $f \in F$ has a finite vertex set $V_f \subseteq V$,
with cell $C_f = \operatorname{conv} \iota(V_f)$. Say that the segment between vertices
$u, w \in V$ lies in the face $f$ when $u, w \in V_f$ and $[\iota(u), \iota(w)] \subseteq C_f$, and
that it lies in exactly two faces when it lies in two distinct faces $f_1, f_2$ and every face it
lies in is $f_1$ or $f_2$. Assume the following. For every edge $e$: $[e] \subseteq P$;
$s(e) \ne t(e)$; if $\iota(v) \in [e]$ for a vertex $v$, then $v = s(e)$ or $v = t(e)$; and the
segment between $s(e)$ and $t(e)$ lies in exactly two faces. Distinct edges $e_1, e_2$ never have
the same endpoints, in the same or in the reverse order, and every common point of $[e_1]$ and
$[e_2]$ is $\iota(v)$ for a vertex $v$ that is an endpoint of both. Every vertex is an endpoint of
some edge. For every face $f$: $C_f \subseteq P$; $V_f$ has at least $3$ elements;
$C_f \cap \operatorname{int} P = \emptyset$; the affine span of $C_f$ has dimension $2$; and every
$v \in V_f$ is an endpoint of two distinct edges whose segments are contained in $C_f$. For
distinct faces $f_1, f_2$, $V_{f_1} \not\subseteq V_{f_2}$, and every point of
$C_{f_1} \cap C_{f_2}$ is $\iota(v)$ for some vertex $v$ or lies on $[e]$ for some edge $e$. The
cells cover the frontier: $\partial P \subseteq \bigcup_{f \in F} C_f$. Finally, if $v_1 \ne v_2$
are vertices such that $[\iota(v_1), \iota(v_2)] \subseteq P$, this segment is disjoint from
$\operatorname{int} P$, it contains $\iota(v)$ only for $v \in \{v_1, v_2\}$, and it lies in
exactly two faces, then some edge has endpoints $(v_1, v_2)$ or $(v_2, v_1)$. Then
$|V| - |E| + |F| = 2$.

The vertex set may contain points that are not extreme points of $P$, such as subdivision
vertices on an edge or inside a face of the polyhedron, and the faces may subdivide a face of $P$
(for example by a diagonal); the statement concerns this cellulation, and $E$ and $F$ need not be
the edges and facets of $P$.

Source: https://en.wikipedia.org/wiki/Euler_characteristic. -/
theorem_wanted euler_polyhedron_formula
    {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
    (P : Set (EuclideanSpace Real (Fin 3)))
    (emb : V → EuclideanSpace Real (Fin 3))
    (hemb : Function.Injective emb)
    (hP : P = convexHull Real (Set.range emb))
    (hinterior : (interior P).Nonempty)
    (edgeEndpoints : E → V × V)
    (hEdge : ∀ e, segment Real (emb (edgeEndpoints e).1) (emb (edgeEndpoints e).2) ⊆ P)
    (hEdge_ne : ∀ e, (edgeEndpoints e).1 ≠ (edgeEndpoints e).2)
    (hEdge_atomic : ∀ (e : E) (v : V),
      emb v ∈ segment Real (emb (edgeEndpoints e).1) (emb (edgeEndpoints e).2) →
      v = (edgeEndpoints e).1 ∨ v = (edgeEndpoints e).2)
    (hEdge_inter : ∀ e₁ e₂, e₁ ≠ e₂ → ∀ x,
      x ∈ segment Real (emb (edgeEndpoints e₁).1) (emb (edgeEndpoints e₁).2) →
      x ∈ segment Real (emb (edgeEndpoints e₂).1) (emb (edgeEndpoints e₂).2) →
      ∃ v : V, emb v = x ∧
        (v = (edgeEndpoints e₁).1 ∨ v = (edgeEndpoints e₁).2) ∧
        (v = (edgeEndpoints e₂).1 ∨ v = (edgeEndpoints e₂).2))
    (faceVertices : F → Finset V)
    (hFace : ∀ f, convexHull Real (emb '' ↑(faceVertices f)) ⊆ P)
    (hFace_card : ∀ f, 3 ≤ (faceVertices f).card)
    (hVert_edge : ∀ v, ∃ e, (edgeEndpoints e).1 = v ∨ (edgeEndpoints e).2 = v)
    (hFace_bdry : ∀ f, convexHull Real (emb '' ↑(faceVertices f)) ∩ interior P = ∅)
    (hFace_dim : ∀ f, Module.finrank Real
      (affineSpan Real (convexHull Real (emb '' ↑(faceVertices f)))).direction = 2)
    (hFace_cover : frontier P ⊆
      Set.iUnion (fun f => convexHull Real (emb '' ↑(faceVertices f))))
    (hEdge_two_faces : ∀ e, ∃ f₁ f₂, f₁ ≠ f₂ ∧
      (edgeEndpoints e).1 ∈ faceVertices f₁ ∧
      (edgeEndpoints e).2 ∈ faceVertices f₁ ∧
      segment Real (emb (edgeEndpoints e).1) (emb (edgeEndpoints e).2) ⊆
        convexHull Real (emb '' ↑(faceVertices f₁)) ∧
      (edgeEndpoints e).1 ∈ faceVertices f₂ ∧
      (edgeEndpoints e).2 ∈ faceVertices f₂ ∧
      segment Real (emb (edgeEndpoints e).1) (emb (edgeEndpoints e).2) ⊆
        convexHull Real (emb '' ↑(faceVertices f₂)) ∧
      ∀ f, ((edgeEndpoints e).1 ∈ faceVertices f ∧
        (edgeEndpoints e).2 ∈ faceVertices f ∧
        segment Real (emb (edgeEndpoints e).1) (emb (edgeEndpoints e).2) ⊆
          convexHull Real (emb '' ↑(faceVertices f))) → f = f₁ ∨ f = f₂)
    (hEdge_no_rev : ∀ e₁ e₂, (edgeEndpoints e₁ = edgeEndpoints e₂ ∨
      ((edgeEndpoints e₁).1 = (edgeEndpoints e₂).2 ∧
       (edgeEndpoints e₁).2 = (edgeEndpoints e₂).1)) → e₁ = e₂)
    (hEdge_complete : ∀ v₁ v₂ : V, v₁ ≠ v₂ →
      segment Real (emb v₁) (emb v₂) ⊆ P →
      segment Real (emb v₁) (emb v₂) ∩ interior P = ∅ →
      (∀ v : V, emb v ∈ segment Real (emb v₁) (emb v₂) → v = v₁ ∨ v = v₂) →
      (∃ f₁ f₂ : F,
        f₁ ≠ f₂ ∧ v₁ ∈ faceVertices f₁ ∧ v₂ ∈ faceVertices f₁ ∧
        segment Real (emb v₁) (emb v₂) ⊆
          convexHull Real (emb '' ↑(faceVertices f₁)) ∧
        v₁ ∈ faceVertices f₂ ∧ v₂ ∈ faceVertices f₂ ∧
        segment Real (emb v₁) (emb v₂) ⊆
          convexHull Real (emb '' ↑(faceVertices f₂)) ∧
        ∀ f : F, (v₁ ∈ faceVertices f ∧ v₂ ∈ faceVertices f ∧
          segment Real (emb v₁) (emb v₂) ⊆
            convexHull Real (emb '' ↑(faceVertices f))) → f = f₁ ∨ f = f₂) →
      ∃ e : E, edgeEndpoints e = (v₁, v₂) ∨ edgeEndpoints e = (v₂, v₁))
    (hFace_incomparable :
      ∀ f₁ f₂, f₁ ≠ f₂ → ¬ (faceVertices f₁ ⊆ faceVertices f₂))
    (hFace_inter : ∀ f₁ f₂, f₁ ≠ f₂ → ∀ x,
      x ∈ convexHull Real (emb '' ↑(faceVertices f₁)) →
      x ∈ convexHull Real (emb '' ↑(faceVertices f₂)) →
      (∃ v, emb v = x) ∨
        (∃ e, x ∈ segment Real (emb (edgeEndpoints e).1) (emb (edgeEndpoints e).2)))
    (hFace_boundary : ∀ f, ∀ v ∈ faceVertices f, ∃ e₁ e₂, e₁ ≠ e₂ ∧
      ((edgeEndpoints e₁).1 = v ∨ (edgeEndpoints e₁).2 = v) ∧
      ((edgeEndpoints e₂).1 = v ∨ (edgeEndpoints e₂).2 = v) ∧
      segment Real (emb (edgeEndpoints e₁).1) (emb (edgeEndpoints e₁).2) ⊆
        convexHull Real (emb '' ↑(faceVertices f)) ∧
      segment Real (emb (edgeEndpoints e₂).1) (emb (edgeEndpoints e₂).2) ⊆
        convexHull Real (emb '' ↑(faceVertices f)))
    : (Fintype.card V : Int) - (Fintype.card E : Int) + (Fintype.card F : Int) = 2

end

end MetaMathlibExt
