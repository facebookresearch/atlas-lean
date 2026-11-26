# Zero one-sided asymptotic modulus for equivalent norms on the full word coordinate space

Let $W$ be the set of all finite words in the alphabet $\mathbb N$, including the empty word, with $u\le v$ if $u$ is a prefix of $v$. Children of $u$ append one natural number. Use the [segment coordinate space](segment-coordinate-space.md) $X(W)$, the norm-closed span of the coordinate functionals inside $J(W)^*$ with the inherited norm. There is no bound on word length, and this is not the full dual of the segment space or a disjoint union of finite-height copies.

For all reals $\alpha,\beta$ and each real seminorm $N$ on $X(W)$ with $0<\alpha\le\beta$ and $\alpha\|z\|\le N(z)\le\beta\|z\|$ for all $z\in X(W)$, the [one-sided asymptotic modulus](unit-direction-asymptotic-moduli.md) satisfies

$$\delta_N\!\left(\frac{\alpha}{2\beta}\right)=0.$$

The comparison constants are the given constants for that norm. The direction in the modulus has $N$-norm exactly one. The assertion is at this specified scale; it does not assert that the modulus vanishes at every positive scale.

## Depends on

- [Coordinate space of a segment-norm completion](segment-coordinate-space.md).
- [Equivalent norms and the one-sided modulus](unit-direction-asymptotic-moduli.md).

## Expansion

Isolate the bounded-tree obstruction for equivalent norms on infinite-dimensional spaces. Its hypotheses are trees of each positive finite height on natural-number words, with node vectors of original norm one and child increments of norm at least one converging weakly to zero along the children of each fixed node. At the given scale $\alpha/(2\beta)$, use approximation of the increments in closed finite-codimensional subspaces to turn a positive one-sided modulus into a uniform positive increment in $N$ along a branch. This contradicts the bound $N\le\beta$ on the chosen nodes at sufficiently large height. Prove modulus nonnegativity via a supporting functional for the equivalent norm to obtain equality with zero.

## Proof outline

For a word $v$, use the sum of $e_w^*$ for all prefixes $w$ of $v$. Each prefix set is one segment, and testing at a coordinate vector gives norm one. For fixed $v$, the increment to child $vj$ is $e_{vj}^*$, of norm one. A finite linear combination of these increments has norm at most the Euclidean norm of its coefficients, by singleton segment tests on the primal vectors. It follows that evaluations of those increments by an arbitrary continuous functional are square-summable in $j$ and hence tend to zero. The resulting trees of arbitrarily large finite height have all vectors of original norm one and $N$-norm at most $\beta$; apply the obstruction at the stated scale. This does not use reflexivity.

## Sources

- OpenAI, [word-forest statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/ForestSpace/Main.lean#L43-L47), [word order and append-one-letter children](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/ForestSpace/Trees.lean#L15-L50), [path increments and the modulus result](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/ForestSpace/Trees.lean#L84-L111), [bounded-tree obstruction](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/ForestSpace/Renorming.lean#L215-L303).
- OpenAI, [*Asymptotic midpoint uniform convexity and unbounded diamond distortion in a reflexive tree space*, Lemma 3.2 and §4.1](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Asymptotic-midpoint-uniform-convexity-and-unbounded-diamond-distortion-in-a-reflexive-tree-space-September-27-2026/manuscript.pdf); [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/331.md).
