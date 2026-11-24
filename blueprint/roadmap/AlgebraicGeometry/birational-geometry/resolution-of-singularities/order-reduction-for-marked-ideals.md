# Order reduction for marked ideals

This node is still to be broken down: the statement is precise, but its proof, which occupies most
of Kollár's lecture, is not.

Let $X$ be a smooth equidimensional scheme of finite type over a field of characteristic zero,
possibly reducible, $I \subset \mathcal{O}_X$ a coherent ideal sheaf that is nonzero on every
irreducible component of $X$, and $E = (E^1, \dots, E^s)$ an ordered sequence of smooth divisors,
each possibly reducible or empty, whose sum is a reduced divisor with simple normal crossings
(Kollár's Notation 64). A *marked ideal sheaf* is a pair $(I, m)$ with an integer $m \ge 1$; its
cosupport $\operatorname{cosupp}(I, m)$ is the set of points where $I$ has order at least $m$, and
$\operatorname{max\text{-}ord} I$ is the maximal order of $I$ at points of $X$. A smooth blow-up
sequence of order $\ge m$ starting with $(X, I, m, E)$ (Definitions 65–66) blows up smooth centres
$Z_j \subset X_j$ such that $I_j$ has order at least $m$ along $Z_j$ and $Z_j$ has simple normal
crossings with the **current** boundary $E_j$; it replaces $I_j$ by its birational transform
$I_{j+1} = \mathcal{O}(m F_j) \cdot \pi_j^* I_j$, with $F_j$ the exceptional divisor, and $E_j$ by
the strict transforms of its members, in order, followed by $F_j$. A centre that is smooth and
contained in the cosupport but tangent to the boundary is not allowed: in $\mathbb{A}^2$ with $m =
1$, $E = (y = 0)$ and $I = (y - x^2)$, the centre $V(I)$ is tangent to $E$ at the origin, and adding
it to the boundary does not give a divisor with simple normal crossings.

**Theorem** (Kollár, Theorem 69). For every $m \ge 1$ there is a smooth blow-up sequence functor
$BMO_m$ of order $\ge m$, defined on triples $(X, I, m, E)$ as above, such that if $BMO_m(X, I, m,
E)$ ends with $(X_r, I_r, m, E_r)$, then $\operatorname{max\text{-}ord} I_r < m$. Kollár states that
$BMO_m$ commutes with smooth morphisms and with change of fields. Moreover (Claim 71.2), for a
closed embedding $\tau \colon Y \hookrightarrow X$ of smooth schemes and ideal sheaves $J \subset
\mathcal{O}_Y$, nonzero on every irreducible component of $Y$, and $I \subset \mathcal{O}_X$ with
$\tau_*(\mathcal{O}_Y / J) = \mathcal{O}_X / I$, one has $BMO_1(X, I, 1, \emptyset) = \tau_*
BMO_1(Y, J, 1, \emptyset)$, the push-forward of a blow-up sequence along the successive embeddings
of the strict transforms (Kollár 30.3); Kollár notes that this compatibility can fail when $E \ne
\emptyset$.

The hypotheses matter. The mark must be positive: for $X = \operatorname{Spec} k$, $I =
\mathcal{O}$, $E = \emptyset$ and $m = 0$ there are no blow-ups and the order stays $0$; no nonzero
ideal on a nonempty scheme has negative order. The ideal must be nonzero on every component: on two
disjoint lines, with $I = (x)$ on one and $0$ on the other, the order of $I$ is infinite on the
second line, and its transforms stay zero there.

Kollár's printed construction does not by itself establish the functoriality for a nonempty boundary
whose labels are disconnected. The global split of an ideal into a monomial and a nonmonomial part
in Definition–Lemma 110 and §111, Step 1 (p. 65) does not commute with restriction to an open
subset: on $X = \mathbb{A}^2_{x, y}$ with $D_i = V(x - i)$, $I = (x^2 (x - 1))$, $m = 1$ and one
label $E^1 = D_0 \sqcup D_2$, the first centre lies in $D_0$, while after restriction to $X
\setminus D_2$, where the label is $D_0$, it lies in $D_1$. This does not affect the existence of
the sequences, but an expansion must either check functoriality for a construction covering such
labels or state this limit.

A good expansion follows Kollár's lecture and has pages for: marked ideals, their birational
transforms and the inductive setup (§§5–6, with Notation 64 and Definitions 65–66, pp. 39–40);
birational transforms of derivatives (§7); maximal contact, going down and going up (§§8–9);
uniqueness of maximal contact and tuning of ideals (§§10–11); order reduction for ideals (§12,
through §§102–105, where the local hypersurfaces of maximal contact are globalized "as in (37)",
Theorem 103, Step 3, p. 61, and Theorem 105, p. 63); and order reduction for marked ideals (§13):
the inductive steps 70.1, which uses Theorem 69 in all dimensions $\le n - 1$ to prove Theorem 68 in
dimension $n$, and 70.2, from there to Theorem 69 in dimension $n$, with the proof of Claim 71.2 in
§§107–111 (§108 through the hypersurface case 103.3 and 107.3; §§110–111 for 107.3 with empty
boundary, pp. 64–66).

## Depends on

- [Simple normal crossing divisor](../simple-normal-crossing-divisor.md), for blow-up sequences, blow-up
  sequence functors and divisors with snc support

## Proof depends on

- [Embeddings and descent for blow-up sequence functors](embedding-and-descent-for-blow-up-sequence-functors.md),
  for the globalization of local constructions by descent

## Sources

- J. Kollár, "Resolution of singularities – Seattle lecture", arXiv:math/0508332 (version 3),
  <https://arxiv.org/abs/math/0508332v3>: §4, 49 (order reduction theorems, marked ideal sheaves and
  their birational transforms), pp. 30–31; §§5–6, pp. 36–43, with Notation 64 and Definitions 65–66,
  pp. 39–40; Theorems 68 and 69, 70 (the main inductive steps), 71 with Claims 71.1–71.2 and the
  remark that follows, pp. 41–42; §§7–13, pp. 43–67, with Theorems 103 and 105, pp. 59–63, and
  §§107–111, pp. 64–66; 30.3 (push-forward of blow-up sequences), p. 22.
