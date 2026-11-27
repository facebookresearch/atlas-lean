# Logarithmic exponent limit for fixed R(s,t)

Fix a natural $s\ge6$. For the least order $R(s,t)$ forcing a clique of size $s$ or an independent set of size $t$, as natural $t\to\infty$,

$$
\frac{(s-1)\log t-\log R(s,t)}{\log\log t}\longrightarrow s-2.
$$

All logarithms are natural, and the quotient and limit are in the reals.

## Depends on

- [Classical graph Ramsey number](graph-ramsey.md)

## Proof depends on

- [Sharp two-sided bounds for fixed R(s,t)](sharp-logarithmic-exponents-off-diagonal-ramsey.md)

## Proof outline

Squeeze the expression by taking logs in the two inequalities at fixed $s$, with the source’s upper constant independent of epsilon and a cutoff that may depend on epsilon.

## Sources

- [Comparator statement: `OAI.SharpLogRamsey.main`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SharpLogRamsey.lean#L32-L34)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/170.md)
