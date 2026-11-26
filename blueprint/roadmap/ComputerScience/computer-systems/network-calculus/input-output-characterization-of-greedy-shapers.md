# Input-output characterization of greedy shapers

Consider a [greedy shaper](greedy-shapers.md) with shaping curve $\sigma$, whose buffer is empty at time $0$ and large enough that no data is lost. For an input flow $R$ the output is

$$
R^* = R \otimes \bar\sigma,
$$

where $\bar\sigma$ is the [sub-additive closure](min-plus-algebra/sub-additive-closure.md) of $\sigma$. Consequently, when $\sigma$ is sub-additive with $\sigma(0) = 0$, the greedy shaper offers the [service curve](service-curves.md) $\sigma$, and its backlog is at most $\sup_{t \ge 0}\{R(t) - (R \otimes \sigma)(t)\}$.

The proof shows that, for a good $\sigma$, among all functions $S$ with $S \le R$ and $S \le S \otimes \sigma$ there is a largest, $R \otimes \sigma$, and that the greedy shaper outputs it.

## Depends on

- [Greedy shapers](greedy-shapers.md)
- [Sub-additive closure](min-plus-algebra/sub-additive-closure.md)
- [Service curves](service-curves.md)

## Proof depends on

- [Reduction of an arrival curve to its sub-additive closure](reduction-of-an-arrival-curve-to-its-sub-additive-closure.md): $\sigma$ may be replaced by $\bar\sigma$ without changing the shaper.
- [Arrival curves as min-plus inequalities](arrival-curves-as-min-plus-inequalities.md)

## Sources

- J.-Y. Le Boudec and P. Thiran, *Network Calculus: A Theory of Deterministic Queuing Systems for the Internet*, Lecture Notes in Computer Science 2050, Springer, 2001; online version of 2022, <https://leboudec.github.io/netcal/latex/netCalBook.pdf>, whose numbering is used here, Section 1.5.2, Theorem 1.5.1, Lemma 1.5.1, Corollary 1.5.1 and Corollary 1.5.2.
