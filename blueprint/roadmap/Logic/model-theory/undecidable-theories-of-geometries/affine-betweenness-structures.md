# Affine betweenness structures

An affine betweenness structure is a subset T of a Euclidean space with the ternary relation "t lies between s and u"; its unary expansion class consists of all expansions of it by one unary predicate.

**Definition.** For $n \ge 1$ let $d$ be the Euclidean metric on $\mathbb R^n$ and let $\beta(s, t, u)$ hold iff $d(s, u) = d(s, t) + d(t, u)$. For $T \subseteq \mathbb R^n$, $(T, \beta)$ denotes $T$ with the restriction of $\beta$ to $T$. The *unary expansion class* $\mathcal E(T, \beta)$ is the class of all structures $(T, \beta, P)$ with $P \subseteq T$ arbitrary, and the *unary expansion class with a finite predicate* $\mathcal F(T, \beta)$ requires $P$ to be finite; the *first-order theory* of such a class is the set of first-order sentences in the vocabulary $\{\beta, P\}$ true in all its members.

*Lines and flats.* A *line in $T$* is a set $L \subseteq T$ with two distinct points, all of whose points are collinear, and such that for distinct $s, t \in L$ every $u \in T$ with $\beta(s, u, t)$ or $\beta(s, t, u)$ lies in $L$. A nonempty $U \subseteq \mathbb R^n$ is a *linearly regular $m$-dimensional flat* if it lies in an $m$-dimensional affine flat but in no $(m-1)$-dimensional one, is *linearly complete* (every line of $U$ is dense in the corresponding real line) and *linearly closed* (two lines of $U$ whose real extensions meet, meet in $U$). $T$ *extends linearly in $m$D* if there are a linearly regular $m$-dimensional flat $S$, a point $x \in S \cap T$ and $\varepsilon > 0$ with $\{u \in S \mid d(x, u) < \varepsilon\} \subseteq T$.

For example $\mathbb R^2$, $\mathbb Q^2$, the plane of real algebraic numbers and the unit cube $[0, 1]^3$ extend linearly in 2D.

## Depends on

None.

## Proof depends on

None.

## Expansion

Tarski's axiomatization of plane geometry uses betweenness and equidistance; the first-order theory of $(\mathbb R^2, \beta, \equiv)$ is decidable. Betweenness alone defines collinearity and lines, which the undecidability proofs use to interpret grids: a unary predicate marks discretely spaced sequences of points along lines, and grid points are recovered as intersections of lines.

## Sources

- A. Kuusisto, J. Meyers and J. Virtema, "Undecidable First-Order Theories of Affine Geometries", *Logical Methods in Computer Science* 9(4), 2013, paper 26, pp. 1–23, <https://doi.org/10.2168/LMCS-9(4:26)2013>; numbers from arXiv:1310.8200v3, <https://arxiv.org/abs/1310.8200v3>: Section 2.3 (betweenness, lines, flats, extending linearly, unary expansion classes) and Section 1.
