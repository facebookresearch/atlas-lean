# Ordinary mixing and mixing of every finite order

Let $(X,\mathcal A,\mu)$ be a probability space and $T:X\to X$ an invertible bimeasurable transformation preserving $\mu$. Assume that for every pair of measurable sets $A,B$,
$\mu(A\cap (T^n)^{-1}B)\to\mu(A)\mu(B)$ as $|n|\to\infty$ over $n\in\mathbb Z$.

For each integer $k\ge 3$ and each $k$-tuple of measurable sets $A_0,\ldots,A_{k-1}$, take positive integer gaps $g_0,\ldots,g_{k-2}$. Put $s_0=0$ and $s_i=\sum_{j<i}g_j$. The proposed result is

$$
\mu\!\left(\bigcap_{i=0}^{k-1}(T^{s_i})^{-1}A_i\right)\longrightarrow\prod_{i=0}^{k-1}\mu(A_i)
\qquad\text{as}\qquad \min_{0\le j<k-1}g_j\longrightarrow\infty.
$$

The limit uses the coordinatewise order on the gap tuples; no relative rates of divergence or common spacing are imposed. The claim concerns a single transformation, not general group actions.

## Depends on

- [Strong mixing](is-mixing.md): this definition uses $n\to+\infty$. For invertible measure-preserving $T$, invariance rewrites the correlation at $-n$ as $\mu(B\cap (T^n)^{-1}A)$, giving the two-sided convention above.

## Expansion

1. Formulate finite-order mixing using gap tuples and prove its equivalence to mixing along every sequence of increasingly separated natural-number layouts. At order two, use invariance to subtract the first time and use ordinary mixing; at order one, use invariance alone.
2. For a least failing order, separate the finite-alphabet zero-entropy witness and its lower-order marginal factorization from the construction of a saturated joining of ordered arrays.
3. Extract the fibrewise coefficient estimates and orbit cancellation of the source argument: bounded nonnegative coefficient sums with a fixed positive integral at each time are claimed to have Cesàro means tending to zero in almost every fibre. Verify the conditional marginal and measurability claims before using bounded convergence to obtain a contradiction. These are substantive proof prerequisites, not consequences of the definition of mixing.

## Sources

- OpenAI, [Comparator statement and definitions, lines 12–33](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/Rokhlin.lean#L12-L33), and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/145.md).
- OpenAI, [Rokhlin's multiple-mixing problem for one transformation](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Rokhlins-multiple-mixing-problem-for-one-transformation-September-23-2026/paper.pdf) (September 23, 2026), accompanying preprint. The comparator above specifies the selected formal scope.
