# Universal isometric dimension bounds in real Lp

For real $p>1$, $p\ne2$, let $d_p(n,1)$ be the least integer $d$ for which every $n$-point subset in every real $L^p$ over any measure space has an embedding into $\ell_p^d$ preserving all distances up to a common positive scalar. For every integer $n\geq9$ such a dimension exists, is admissible, and satisfies $\lfloor(n-1)/4\rfloor^2\leq d_p(n,1)\leq\binom n2$. The lower bound uses natural-number division before squaring.

## Depends on
Use real $L^p$ distances and the finite-coordinate $\ell_p^d$ norm. An admissible dimension here must realize the finite distance matrix up to a single positive scalar; the admissible dimensions are natural numbers and $d_p(n,1)$ is their minimum. No positive-distortion estimate enters this definition.

## Proof depends on
An exact representation of the distance data in at most one coordinate per unordered pair and a worst-case family forcing the quadratic lower bound.

## Expansion
Establish admissibility and cardinal-coordinate accounting for the exact embedding, and prove the separate obstruction. Check the finite endpoints $n=9$ and the flooring convention.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SubpolynomialLp.lean#L31-L45) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/094.md).
