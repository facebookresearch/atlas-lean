# Euler's polyhedron formula

Let $V$, $E$ and $F$ be finite sets, let
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

## Sources

- https://en.wikipedia.org/wiki/Euler_characteristic.
