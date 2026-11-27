# Sharp logarithmic bounds for fixed off-diagonal Ramsey numbers

Fix a natural $s\ge6$. Let $R(s,t)$ be the least order forcing a clique of size $s$ or an independent set of size $t$. There is $C_s>0$ such that for every real $\epsilon>0$ and all sufficiently large natural $t$,

$$
\frac{t^{s-1}}{(\log t)^{s-2+\epsilon}}\le R(s,t)\le C_s\frac{t^{s-1}}{(\log t)^{s-2}}.
$$

The upper constant is independent of $\epsilon$, and each logarithm is natural.

## Depends on

- [Classical graph Ramsey number](graph-ramsey.md)
- Natural threshold and real logarithmic scales.

## Proof outline

Provide both estimates for fixed $s$ and connect a clique in the complement to the independent-set formulation. The log exponent limit is a separate consequence.

- Parameterized off-diagonal lower construction and upper bound.

## Related results

The lower bound implies the corresponding $s\ge6$ case of [Erdős Problem 986](https://www.erdosproblems.com/986), formalized as the lower-bound proposition [`offDiagonalRamseyLowerBound`](https://github.com/facebookresearch/atlas-lean/blob/099efaa6aabe39c8022e0f67e7f37ca1c8b8e7c0/WantedExt/GraphTheory/OffDiagonalRamseyLowerBoundErdosProblem986Wanted.lean#L35-L41). Choose any fixed positive epsilon in the log exponent. This implication does not assert the cases $s=3,4$ or the reverse implication.

## Sources

- [Comparator statement: `OAI.SharpLogRamsey.main`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SharpLogRamsey.lean#L32-L34)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/170.md)
