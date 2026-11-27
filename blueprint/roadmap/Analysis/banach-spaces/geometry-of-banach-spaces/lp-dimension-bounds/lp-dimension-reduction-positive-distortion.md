# Universal subpolynomial dimension reduction in real Lp

Fix real $p>1$, $p\ne2$. For integers $n,d$ and $D\geq1$, say $d$ is admissible if for every real $L^p(\Omega,\mu)$ over a measure space and every injective family $(x_i)_{i=1}^n$ in it there are $y_i\in\mathbb R^d$ and a common scale $s>0$ such that $s\|x_i-x_j\|_p\leq\|y_i-y_j\|_{\ell_p^d}\leq Ds\|x_i-x_j\|_p$ for all $i,j$, with coordinate norm $(\sum_a|y_a|^p)^{1/p}$. Let $d_p(n,D)$ be the infimum of admissible natural-number dimensions. For every $D>1$ there is a real $C$ such that for all $n\geq2$ the infimum is admissible and lies between $\log n/\log(1+2D)$ and $\exp(C(\log n)^{\gamma(p)})$, with $\gamma(p)=2-p$ for $p<2$ and $1-2/p$ for $p>2$.

## Depends on
Real $L^p$ modulo null sets over arbitrary measure spaces and a common scale per embedding, chosen before the pair of points.

## Proof depends on
A uniform dimension-reduction construction at distortion $D$ and a separated-point volumetric lower bound.

## Expansion
Separate the universal scale/embedding construction from the packing obstruction, then show that the natural-number infimum is realized. A bound for just one measure space or a constant depending on $n$ is insufficient.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SubpolynomialLp.lean#L31-L45) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/094.md).
