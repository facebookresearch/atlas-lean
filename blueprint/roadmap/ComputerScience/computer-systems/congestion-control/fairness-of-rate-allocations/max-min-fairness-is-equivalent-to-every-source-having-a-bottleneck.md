# Max-min fairness is equivalent to every source having a bottleneck

In the [network model](network-model-and-feasible-rate-allocations.md), a feasible allocation is [max-min fair](max-min-fair-rate-allocations.md) if and only if every source has a [bottleneck link](bottleneck-links.md).

**Proof sketch.** If every source has a bottleneck, raising $x_s$ requires lowering the rate of another source on its saturated bottleneck, whose rate is at most $x_s$. Conversely, if some source $s$ has no bottleneck, each saturated link $l$ on its route carries a source $\sigma(l)$ with $x_{\sigma(l)} > x_s$; raising $x_s$ by a small $\delta > 0$ and lowering each $x_{\sigma(l)}$ by $\max_{l : \sigma(l) = s'} \delta A_{l,s}/A_{l,s'}$ keeps the allocation feasible and lowers only rates larger than $x_s$, so $x$ is not max-min fair.

## Depends on

- [Max-min fair rate allocations](max-min-fair-rate-allocations.md)
- [Bottleneck links](bottleneck-links.md)

## Sources

- J.-Y. Le Boudec, *Rate adaptation, congestion control and fairness: a tutorial*, EPFL, version of 1 November 2021, <https://leboudec.github.io/leboudec/latex/cc/LEB3132.pdf>, Section 1.2.1, Theorem 1.2.3 with its proof (equations (1.5)–(1.11) and Figure 1.5).
