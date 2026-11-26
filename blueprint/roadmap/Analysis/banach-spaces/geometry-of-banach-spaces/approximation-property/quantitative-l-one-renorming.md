# Quantitative bounded-approximation renorming of real ℓ¹

For every integer $p\ge1$ let $B_p=300p^2+150p+5$. The real sequence space $\ell_1(\mathbb N)$ admits a complete norm $N$ on its original real vector-space operations with $N(rx)=|r|N(x)$ and $\tfrac12\|x\|_1\le N(x)\le B_p\|x\|_1$ for every $r,x$. With this new norm it has the $2B_p$-bounded approximation property and fails the $p$-bounded approximation property; in particular if $p=1$ it fails the $1$-bounded approximation property. For a bound $\Lambda$, the property means each compact set admits finite-rank linear approximations to the identity of norm at most $\Lambda$, with errors bounded uniformly by some $\eta<\epsilon$ for each $\epsilon>0$.

## Depends on

- [The approximation property](has-approximation-property.md) and the original real $\ell_1$ operations.

## Proof depends on

- Quantitative norm construction on the fixed vector space, upper approximation bounds and a lower bound obstructing every approximant under the smaller norm constraint.

## Expansion

Separate compatibility with the original scalar action from completeness and the two bounded approximation estimates. The lower bound must apply in the new norm, not in the standard $\ell_1$ norm.

## Sources

- OpenAI, [RealL1Renorming comparator, real_l1_quantitative_renorming](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/RealL1Renorming.lean#L48-L50).
- OpenAI, [scope and accompanying papers](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/330.md).
