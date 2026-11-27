# Friedgut: coarse thresholds of graph properties are local

Let $\mathcal{P}$ be a monotone graph property on $n$ vertices and $p = p(n)$. If $\mathcal{P}$ has a coarse threshold at $p$, in the sense that $p \cdot \frac{d}{dp}\mu_p(\mathcal{P}) \le C$ for a constant $C$, then $\mathcal{P}$ is approximated by a local property: for every $\delta > 0$ there is a monotone graph property $\mathcal{Q}$, all of whose minimal graphs are balanced (no subgraph has larger average degree) and have at most $k(\delta, C)$ edges, with $\mu_p(\mathcal{P} \triangle \mathcal{Q}) \le \delta$; here $k(\delta, C)$ does not depend on $n$. Friedgut used this criterion to prove that $k$-SAT unsatisfiability has a sharp threshold (whose location may depend on $n$), and Achlioptas and Friedgut used it to prove the same for $k$-colourability.

## Proof sketch

By the Margulis-Russo formula, a coarse threshold means bounded total influence at scale $p$. Bourgain's theorem then provides a bounded-size set of edges that boosts the probability; by symmetry this occurs for many copies of a fixed small graph, which yields the local approximation. For $k$-SAT one shows that no bounded-size structure has the required effect, forcing a sharp threshold.

## Depends on

- [Global functions on the p-biased cube](pbiased-global-function.md)

## Proof depends on

- [Bourgain's sharp-threshold theorem with global hypercontractivity](kllm-bourgain-strengthened.md)
- [Sharp threshold from influences](../../../Probability/percolation/phase-transition/sharp-thresholds-from-influences/sth-sharp-threshold.md)

## Sources

- E. Friedgut, "Sharp thresholds of graph properties, and the k-sat problem" (with an appendix by J. Bourgain), Journal of the American Mathematical Society 12 (1999) 1017-1054, Theorem 1.1.
- D. Achlioptas, E. Friedgut, "A sharp threshold for k-colorability", Random Structures & Algorithms 14 (1999) 63-70.
