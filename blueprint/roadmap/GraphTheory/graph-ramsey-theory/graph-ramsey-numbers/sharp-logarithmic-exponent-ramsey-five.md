# Sharp logarithmic bounds for R(5,t)

Let $R(5,t)$ be the least order forcing a clique of size five or an independent set of size $t$ in every simple graph. There is $C>0$ such that for all real $\epsilon>0$ and all large enough natural $t$ (threshold may depend on $\epsilon$),

$$
\frac{t^4}{(\log t)^{3+\epsilon}}\le R(5,t)\le C\frac{t^4}{(\log t)^3}.
$$

The upper constant is independent of $\epsilon$ and the logarithms are natural.

## Depends on

- [Classical graph Ramsey number](graph-ramsey.md)
- Real powers of logarithms and an eventual quantifier along the naturals.

## Proof outline

State the two estimates for this explicit clique size with the shared quantifier order. They furnish the separately stated logarithmic limit.

- Sharp logarithmic lower-bound construction and matching upper bound.

## Related results

The lower bound implies the corresponding $s=5$ case of [Erdős Problem 986](https://www.erdosproblems.com/986), formalized as the lower-bound proposition [`offDiagonalRamseyLowerBound`](https://github.com/facebookresearch/atlas-lean/blob/099efaa6aabe39c8022e0f67e7f37ca1c8b8e7c0/WantedExt/GraphTheory/OffDiagonalRamseyLowerBoundErdosProblem986Wanted.lean#L35-L41). Choose any fixed positive epsilon in the log exponent. This implication does not assert the cases $s=3,4$ or the reverse implication.

## Sources

- [Comparator statement: `OAI.SharpRamseyFive.main`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/RamseyFive.lean#L25-L27)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/170.md)
