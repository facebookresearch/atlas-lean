# Contraction of composed random permutations acting on tuples

Let $T, \alpha$ be finite sets with $|T| \le |\alpha|$. A distribution $\rho$ on permutations of $\alpha$ induces a Markov kernel on injections $T \hookrightarrow \alpha$ by $e \mapsto \pi \circ e$ with $\pi \sim \rho$. If, for every starting injection $e$, the law of $\pi \circ e$ with $\pi \sim \rho$ is within statistical distance $\delta$ of uniform, then for every $t \ge 1$, the composition $\pi = \pi_t \circ \dots \circ \pi_1$ of independent $\pi_1, \dots, \pi_t \sim \rho$ and every $e$,

$$
\delta\big(\mathrm{law}(\pi \circ e),\ \mathrm{Unif}(T \hookrightarrow \alpha)\big) \le \frac12\,(2\delta)^{t}.
$$

## Proof sketch

Write the one-step kernel as $\mathrm{Unif} + E$ where every row of $E$ has $\ell_1$ norm at most $2\delta$ and sums to zero. The uniform distribution on injections is stationary for the kernel of every distribution on permutations, so cross terms involving $\mathrm{Unif}$ collapse, and the $t$-step kernel is $\mathrm{Unif} + E^t$, whose rows have $\ell_1$ norm at most $(2\delta)^t$; halving gives the statistical distance.

The following extension is derived here and is not stated in the cited sources: the same bound holds when the $\pi_i$ are independent with possibly different distributions $\rho_1, \dots, \rho_t$, each satisfying the hypothesis, since the argument only multiplies the error kernels $E_t \cdots E_1$.

## Depends on

- [Total variation distance between finite measures](../../convergence-of-measures/total-variation-distance/total-variation-dist.md)

## Proof depends on

- [A stochastic matrix contracts total variation](../../markov-chains/mixing-times-of-markov-chains/tv-dist-vec-mul-le.md)

## Sources

- Y. Arbitman, M. Naor and G. Segev, "Backyard Cuckoo Hashing: Constant Worst-Case Operations with a Succinct Representation", Proceedings of the 51st Annual IEEE Symposium on Foundations of Computer Science (FOCS), 2010; full version arXiv:0912.5424v3, Section 5.3, Theorem 5.6.
- E. Kaplan, M. Naor and O. Reingold, "Derandomized constructions of k-wise (almost) independent permutations", Algorithmica 55(1):113-133, 2009; ECCC TR06-002, Theorem 3.8.
