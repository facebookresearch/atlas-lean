# Rapid mixing implies a low-congestion flow

Let $P$ be a stochastic matrix, reversible with respect to a probability vector $\pi > 0$, and suppose $d_{TV}(P^t(x,\cdot),\pi) \le 1/4$ for every state $x$ and every $t \ge \tau$. Then there is a [multicommodity flow](multicommodity-flow.md) that puts at most $16\tau\,\pi(u)P(u,v)$ on every oriented edge $(u,v)$: the resistance of the chain is at most $16\tau$. This is Theorem 8 of A. Sinclair, *Improved bounds for mixing rates of Markov chains and multicommodity flow*, Combinatorics, Probability and Computing 1 (1992), 351–370, stated there for ergodic reversible chains with $\tau = \max_x \tau_x(1/4)$; any $\tau$ satisfying the hypothesis is at least that one, and the hypothesis already forces the chain to be irreducible and aperiodic (otherwise some starting state keeps total variation distance at least $1/2$ from $\pi$). The proof routes commodity $(x,y)$ along the $2\tau$-step trajectories of the chain from $x$ to $y$, in proportion to their probabilities, and bypasses cycles. With Theorem 5′ for flows, Sinclair concludes that a reversible chain mixes rapidly if and only if it supports a flow of polynomially bounded congestion (with the caveats of the topic introduction: the smallest eigenvalue and $\pi(x)$ not exponentially small).

## Informally uses

- [Sinclair's Lemma 7](div-eight-le-pow-apply.md): bounds $P^{2\tau}(x,y) \ge \pi(y)/8$, the denominator of the flow on each trajectory.

## Background

- [Being $1/4$-mixed at a given time](../mixing-times-of-markov-chains/is-mixed-at.md): a single-time version of the mixing hypothesis; Sinclair's $\tau_x(\varepsilon)$ requires it at every later time.
