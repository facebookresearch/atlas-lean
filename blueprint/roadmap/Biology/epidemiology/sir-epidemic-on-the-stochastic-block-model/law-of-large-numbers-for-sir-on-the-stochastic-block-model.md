# Law of large numbers for SIR on the sparse stochastic block model

**Model.** Let $K \in \mathbb{N}$, let $V$ be a set of $n$ vertices with community labels $k(v) \in [K]$, $n_k$ vertices of label $k$, and let $W \in [0,\infty)^{K \times K}$ be symmetric with every row nonzero. The sparse *stochastic block model* $G \sim \mathrm{SBM}(V, W)$ joins each pair $\{u,v\}$ independently with probability $W_{k(u)k(v)}/n$. On $G$ run the Markovian SIR epidemic: every infected vertex transmits along each edge to a susceptible neighbour at rate $\beta > 0$ and recovers at rate $\gamma > 0$. Write $S_k(t), I_k(t)$ for the numbers of susceptible and infected vertices of label $k$, and assume the initial infected and recovered sets are chosen at random given the labels (independently of $G$) with
$$\tfrac1n S_k(0) \xrightarrow{P} s_k(0) > 0, \qquad \tfrac1n I_k(0) \xrightarrow{P} i_k(0) \ge 0 \qquad (k \in [K]).$$

**Theorem (finite horizon).** Let $(s_k, x_k, i_k)_{k \in [K]}$ be the unique solution of
$$\dot s_k = -\beta s_k \sum_{\ell} W_{\ell k} x_\ell, \qquad \dot x_k = -(\beta+\gamma) x_k + \beta s_k \sum_\ell W_{\ell k} x_\ell, \qquad \dot i_k = -\gamma i_k + \beta s_k \sum_\ell W_{\ell k} x_\ell,$$
with $x_k(0) = i_k(0)$. Then for every $0 < t_0 < \infty$ and $\varepsilon > 0$,
$$\mathbb{P}\Big(\sup_{t \in [0,t_0]} \big\| \big(\tfrac1n \vec S(t), \tfrac1n \vec I(t)\big) - \big(\vec s(t), \vec i(t)\big)\big\|_2 > \varepsilon\Big) \xrightarrow[n\to\infty]{} 0 .$$
Here $x_k$ is the limiting density of *active* half-edges (edges from an infected vertex that have not yet transmitted), which is why it decays at rate $\beta+\gamma$ rather than $\gamma$.

**Theorem (uniform in time).** If in addition $W$ is irreducible and $\vec i(0) \ne 0$, the same convergence holds with $\sup_{t \in [0,\infty)}$; in particular $\frac1n \vec S(\infty) \to \vec s(\infty) = \lim_{t\to\infty}\vec s(t)$ in probability, so the final size obeys a law of large numbers.

## Depends on

- [Kermack–McKendrick final-size relation](../kermack-mckendrick-sir-model/final-size.md)

## Expansion

The proof explores the graph and the epidemic simultaneously, revealing an edge only when an infected endpoint tries to transmit along it; in the Poisson version of the SBM this makes the vector of susceptibles and active half-edges a density-dependent Markov chain, to which Kurtz-type martingale estimates apply on bounded time intervals. Extending to $t = \infty$ uses herd immunity: once $\vec s(t)$ is small enough that the matrix $\frac{\beta}{\beta+\gamma} W \operatorname{diag}(\vec s(t))$ has spectral radius below $1$, the remaining epidemic is subcritical, the number of active half-edges decays exponentially, and errors accumulated after that time stay small. On the complete graph ($K=1$) the ODE reduces to the classical Kermack–McKendrick system.

## Sources

- Christian Borgs, Karissa Huang, Christian Ikeokwu, "A Law of Large Numbers for SIR on the Stochastic Block Model: A Proof via Herd Immunity", arXiv:2410.07097 (2024), Section 2 ("Notation and Statements of Results"), finite-time and final-size law-of-large-numbers theorems, <https://doi.org/10.48550/arXiv.2410.07097>.
