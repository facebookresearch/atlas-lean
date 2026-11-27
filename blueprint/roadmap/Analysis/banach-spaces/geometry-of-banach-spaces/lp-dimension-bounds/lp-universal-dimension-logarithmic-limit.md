# Logarithmic growth rate of the universal Lp dimension

For real $p>1$, $p\ne2$, let $d_p(n,D)$ be the least admissible integer dimension for embedding all $n$-point real $L^p$ subsets into coordinate $\ell_p$ with a common positive scale and distortion at most $D$. For every real $D\geq1$, $\log d_p(n,D)/\log n$ tends to $0$ if $D>1$, and to $2$ if $D=1$, as $n\to\infty$ along the integers. Initial logarithms are interpreted with the real totalization used in the source and do not affect the limit.

## Depends on
The same least universal dimension for arbitrary real $L^p$ measure spaces, with distortion fixed.

## Proof depends on
- [Subpolynomial dimension bounds](lp-dimension-reduction-positive-distortion.md).
- [Isometric dimension bounds](lp-isometric-dimension-bounds.md).

## Proof strategy
Show eventual positivity of the dimension, take logarithms on that tail, and apply squeezing separately for the strict-distortion and isometric cases. In the strict case check $\gamma(p)<1$ on both sides of $2$.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SubpolynomialLp.lean#L31-L45) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/094.md).
