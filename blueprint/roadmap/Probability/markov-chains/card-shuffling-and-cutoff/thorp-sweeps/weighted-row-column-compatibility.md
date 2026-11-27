# Weighted compatibility on balanced rectangles

There exist real $L,C_0,m_0>0$ with the following property. Take natural $A,D$, set $n=AD$, $m=\sqrt n$, and $\theta=1-L/\log m$. Assume $m\ge m_0$, $\theta>0$, and $m/2\le A,D\le2m$. The source uses totalized real division in $\theta$. Give each row a permutation $r_i$ of the $D$ columns, each column a permutation $c_k$ of the $A$ rows, and nonnegative weights $w_i,v_k$ respectively on these finite groups. Call the pair compatible if for every original column $j$ the map $i\mapsto c_{r_i(j)}(i)$ is injective. Under independent uniform row and column permutations,

$$
\frac{(AD)!}{(D!)^A(A!)^D}\,\mathbb E\left[\mathbf 1_{\rm compatible}\prod_i w_i(r_i)\prod_k v_k(c_k)\right]
\le e^{C_0 n^{54/100}}\prod_i(\mathbb E w_i^{1/\theta})^\theta\prod_k(\mathbb E v_k^{1/\theta})^\theta.
$$

The expectations on the right are the separate uniform group means.

**Conventions.** Use row and column permutation choices, the injectivity test in the original columns, and the exact factorial normalization and power means.

## Depends on

The statement uses the explicit definitions given above.

## Proof outline

The weighted counting comparison for the compatibility event, with a near-$1$ exponent and a sublinear explicit exponential loss uniform in the two balanced side lengths.

Separate the counting and norm inequalities, then check the marginal weighting step for arbitrary nonnegative weights, including zeros. The result is only the weighted compatibility bound, not a uniform regular moment or rank bound.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ThorpWeightedCompatibility.lean#L47-L49)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/238.md)
- [Accompanying manuscript: Compatibility entropy and the spectrum of a Thorp sweep](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Compatibility-entropy-and-the-spectrum-of-a-Thorp-sweep-September-26-2026/paper.pdf)
- [Pinned definitions used inline](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ThorpWeightedCompatibility.lean#L9-L44)
