# Squared-logarithmic threshold width for increasing graph properties

Let $n\ge2$ and let $f$ be a Boolean property of simple graphs on $n$ labelled vertices, taking both values, invariant under vertex relabeling and increasing under edge inclusion. Let $F(p)$ be its probability in the independent-edge model (each unordered pair is present with probability $p$), and put $q_a=\inf\{p\in[0,1]:F(p)\ge a\}$. For every $0<\epsilon<1/2$,

$$
q_{1-\epsilon}-q_\epsilon\le \frac{2^{19}}{(\log n)^2}\log\!\left(\frac{1}{2\epsilon}\right).
$$

## Depends on

- Vertex action on unordered edge configurations, finite Bernoulli product law, monotonicity and quantile infima.

## Expansion

State the independent variance–total-influence inequality for every vertex-invariant Boolean graph property at every fixed bias 0<p<1: variance is bounded by 2¹⁷ divided by (log n)² times total influence, for n≥2. This does not require monotonicity or quantiles. Check the exact product-measure and edge-index conventions before proving it; integrate the resulting derivative bound only in this leaf.

## Proof outline

Bridge the probability and derivative to the existing Bernoulli influence API. Identify the damped influence inequality and show it yields the squared log at all required densities. Prove the quantiles lie within the probability range using nontriviality, and check $n=2$ and $\epsilon\uparrow1/2$.

## Related results

The [damped $p$-biased KKL inequality](../../../../Combinatorics/boolean-functions/kahn-kalai-linial-inequality/a-damped-kkl-inequality-under-p-biased-measures/fpe-damped-var-log-gain.md) is a related Fourier estimate. The transfer from this estimate to a bound uniform in the graph density uses the derivative and symmetry argument; the two inequalities are not equivalent statements.

## Sources

- [Comparator statement: `OAI.Problem313.sharp_threshold_width`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SharpThreshold.lean#L51-L58)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/186.md)
- [Proof of the reduction and the prerequisite interfaces](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/SharpThreshold/Main.lean)
