# Polytopes of exchangeable finitely sampling-consistent tree distributions

**Setting.** Let $RB_L(n)$ be the rooted binary phylogenetic trees with leaves labelled $[n]$ and $RB_U(n)$ the unlabelled tree shapes. A distribution $p$ on $RB_L(n)$ is *exchangeable* if $p(\sigma T)=p(T)$ for every relabelling $\sigma\in S_n$; let $EX_n$ be the set of these. For $m\ge n$, let $\pi_n$ map a distribution on $RB_L(m)$ to the law of the restriction of the tree to leaves $[n]$, and set

$$EX_n^m=\pi_n(EX_m),\qquad EX_n^\infty=\bigcap_{m\ge n}EX_n^m ,$$

the *$m$-sampling consistent* and the (infinitely) sampling consistent exchangeable distributions.

**Theorem (polytope structure).** $EX_n$ is a simplex of dimension $|RB_U(n)|-1$ whose vertices $p_T$ are the uniform labellings of the shapes $T$. For $m>k>n$, $EX_n^m\subseteq EX_n^k$, and

$$EX_n^m=\mathrm{conv}\{\pi_n(p_T):T\in RB_U(m)\},$$

where $\pi_n(p_T)$ assigns to each $n$-leaf shape its induced-subtree density in $T$ (the fraction of $n$-subsets of leaves of $T$ on which $T$ restricts to that shape). The comb distribution is always a vertex of $EX_n^m$.

**Theorem (four leaves).** $EX_4^\infty$ equals the four-leaf beta-splitting model: in coordinates (probability of the comb, probability of the balanced shape) it is the segment from $(1,0)$ to $(\tfrac47,\tfrac37)$, the second endpoint being the $\beta\to\infty$ limit of Aldous' beta-splitting model and the limiting induced density of the balanced 4-leaf shape in the most balanced $m$-leaf trees.

**Theorem (five leaves and general $n$).** Among trees with $m\ge7$ leaves, the number of 5-leaf subsets on which the tree restricts to the 5-leaf comb is minimized when every internal node is maximally balanced, so the projection of the maximally balanced $m$-leaf tree is a vertex of $EX_5^m$, converging to the $\beta=\infty$ point of the beta-splitting model; projections of $comb(Gir_5,m-4)$ and of the bicomb tree joining two combs of sizes $\lfloor m/2\rfloor,\lceil m/2\rceil$ are also vertices of $EX_5^m$. For general $n$, every limit point of projections $\pi_n(p_{T_m})$ is also a limit of explicit *multinomial models*, and $EX_n^\infty$ is the closed convex hull of limits of multinomial models built on trees whose projections are vertices of $EX_n^m$; each $p\in EX_n^m$ lies within $C/m$ of $EX_n^\infty$ coordinatewise.

## Expansion

Exchangeability forces a distribution on labelled trees to be uniform within each shape, which gives the simplex. Projection is linear, so $EX_n^m$ is the convex hull of projected vertices, i.e. of subtree-density vectors of big trees; decreasing in $m$ because an $m$-consistent family is also $k$-consistent. On four leaves only the balanced-shape probability varies, and its maximum over $m$-leaf trees is attained by the most balanced tree, whose balanced-quartet density tends to $3/7$, matching the beta-splitting extreme. A nested sequence of polytopes has intersection equal to the closed convex hull of limits of its vertices, which reduces $EX_n^\infty$ to vertex limits.

## Depends on

- [Sampling-consistent Markov branching models](../markov-branching-models-of-tree-shapes/sampling-consistent-markov-branching-models.md)

## Sources

- Benjamin Hollering, Seth Sullivant, "Exchangeable and Sampling Consistent Distributions on Rooted Binary Trees", arXiv:1902.03321: Definitions 2.1 and 2.3, Lemmas 2.2, 2.4, 2.5, 2.7, 2.10 and Corollary 2.8 (polytope structure), Theorem 4.2 (four leaves), Proposition 5.2, Lemma 5.4, Theorem 5.7 and Corollaries 5.8–5.9 (five leaves), Theorem 6.1, Corollary 6.2, Proposition 6.3 and Corollary 6.4 (general $n$ via multinomial models). <https://doi.org/10.48550/arXiv.1902.03321> Published version: Journal of Applied Probability 59 (2022) 60–80, <https://doi.org/10.1017/jpr.2021.28>.
