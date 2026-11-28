# Refutation of the Heilbronn upper bound with half the explicit saving

For $p,q,r\in[0,1]^2$ let $A(p,q,r)=\frac12|\det(q-p,r-p)|$. Put $M=\binom{163}{41}$, $T=\binom M3$, and $\eta=1/(100000(T^2+1))$.

We have $\eta/2>0$, and there are **no** $C>0$ and $n_0\in\mathbb N$ such that every $n\ge\max(n_0,3)$ and every $n$-point subset of the closed unit square has some pairwise distinct triple with area at most $Cn^{-2+\eta/2}$. The exponent here is fixed, not existential.

## Depends on

- Heilbronn determinant area on distinct triples.

## Proof depends on

- [Explicit sequence lower bound](explicit-power-lower-bound.md)
- Compare $Cn^{-2+\eta/2}$ to $n^{-2+\eta}$ for arbitrarily large sizes from the lower bound.

## Expansion

Use divergence of $n_j^{\eta/2}$ and choose an index meeting both size thresholds and the strict comparison. It depends on the construction, so it is not a ready wanted task.

## Sources

- OpenAI Math, [`almost_n_minus_two_refuted`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/HeilbronnTriangle.lean#L59-L63) (statement and local definitions).
