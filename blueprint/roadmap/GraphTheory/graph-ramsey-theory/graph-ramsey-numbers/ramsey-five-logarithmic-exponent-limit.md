# Logarithmic exponent limit for R(5,t)

For the least order $R(5,t)$ forcing a clique of size five or an independent set of size $t$, as natural $t\to\infty$,

$$
\frac{4\log t-\log R(5,t)}{\log\log t}\longrightarrow 3.
$$

The expression is real and all logarithms are natural. The limit is along every natural order, not a subsequence.

## Depends on

- [Classical graph Ramsey number](graph-ramsey.md)

## Proof depends on

- [Sharp two-sided bounds for R(5,t)](sharp-logarithmic-exponent-ramsey-five.md)

## Proof outline

On a final segment where $\log\log t$ is positive, take logs of both inequalities, then let the allowed epsilon tend to zero and use $\log C/\log\log t\to0$.

## Sources

- [Comparator statement: `OAI.SharpRamseyFive.main`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/RamseyFive.lean#L25-L27)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/170.md)
