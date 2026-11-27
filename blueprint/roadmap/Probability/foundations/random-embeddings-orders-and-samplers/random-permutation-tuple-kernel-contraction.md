# Contraction of composed random permutations acting on tuples

Let $T, \alpha$ be finite sets with $|T| \le |\alpha|$. A distribution $\rho$ on permutations of $\alpha$ induces a Markov kernel on injections $T \hookrightarrow \alpha$ by $e \mapsto \pi \circ e$ with $\pi \sim \rho$; the uniform distribution on injections is stationary for every such kernel. If $\rho_1, \dots, \rho_t$ ($t \ge 1$) are distributions on permutations such that, for every $i$ and every starting injection $e$, the law of $\pi \circ e$ with $\pi \sim \rho_i$ is within statistical distance $\delta$ of uniform, then for the composition $\pi = \pi_t \circ \dots \circ \pi_1$ of independent $\pi_i \sim \rho_i$ and every $e$,

$$
\delta\big(\mathrm{law}(\pi \circ e),\ \mathrm{Unif}(T \hookrightarrow \alpha)\big) \le \frac12\,(2\delta)^{t}.
$$

## Proof sketch

Write each one-step kernel as $\mathrm{Unif} + E_i$ where every row of $E_i$ has $\ell_1$ norm at most $2\delta$ and sums to zero. Stationarity of the uniform law makes cross terms involving $\mathrm{Unif}$ collapse, so the $t$-step kernel is $\mathrm{Unif} + E_t \cdots E_1$, whose rows have $\ell_1$ norm at most $(2\delta)^t$; halving gives the statistical distance.

## Depends on

- [Total variation distance between finite measures](../../convergence-of-measures/total-variation-distance/total-variation-dist.md)

## Proof depends on

- [A stochastic matrix contracts total variation](../../markov-chains/mixing-times-of-markov-chains/tv-dist-vec-mul-le.md)

## Sources

- Y. Arbitman, M. Naor and G. Segev, "Backyard Cuckoo Hashing: Constant Worst-Case Operations with a Succinct Representation", Proceedings of the 51st Annual IEEE Symposium on Foundations of Computer Science (FOCS), 2010.
