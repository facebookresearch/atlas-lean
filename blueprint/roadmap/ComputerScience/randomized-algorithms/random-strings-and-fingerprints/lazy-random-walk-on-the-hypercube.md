# Mixing of the lazy random walk on the hypercube

The lazy random walk on $\{0,1\}^n$ picks a coordinate $i$ and a fair bit $b$ uniformly and independently and overwrites coordinate $i$ with $b$; it is reversible with respect to the uniform distribution. Its distance to stationarity after $t$ steps satisfies $d(t) \le n(1 - 1/n)^t \le n e^{-t/n}$, and for every $\varepsilon > 0$ the mixing time satisfies $t_{\mathrm{mix}}(\varepsilon) \le \lceil n\log n + n\log(1/\varepsilon)\rceil$. The ceiling is necessary: for $n = 1$ and $\varepsilon = 2/5$, $t_{\mathrm{mix}}(\varepsilon) = 1 > \log(5/2)$.

## Proof sketch

Couple two copies by using the same coordinate and the same bit; once coordinate $i$ has been chosen the copies agree there forever. A fixed coordinate is never chosen in $t$ steps with probability $(1 - 1/n)^t$, so by a union bound the copies have not coalesced with probability at most $n(1 - 1/n)^t$, which bounds $d(t)$ by the coupling inequality.

## Depends on

- [Being $1/4$-mixed at a given time](../../../Probability/markov-chains/mixing-times-of-markov-chains/is-mixed-at.md)
- [Total variation distance of functions on a finite set](../../../Probability/markov-chains/mixing-times-of-markov-chains/tv-dist.md)

## Sources

- D. A. Levin and Y. Peres, "Markov Chains and Mixing Times", second edition, American Mathematical Society, 2017.
