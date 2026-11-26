# The terminal value is forgotten geometrically

Let $M$ be a finite Markov decision process with real rewards and stochastic transitions, and let $0 \le \gamma < 1$. For every Markov policy $\pi$, every $N$ and all terminal values $V$, $W$,

$$\big\|T_{\mu_0} \cdots T_{\mu_{N-1}} V - T_{\mu_0} \cdots T_{\mu_{N-1}} W\big\|_\infty \le \gamma^N \|V - W\|_\infty.$$

Each $T_\mu$ is a $\gamma$-contraction in the sup norm, and a composition of $N$ of them is a $\gamma^N$-contraction.

## Informally uses

- [A policy's Bellman operator is a contraction](../value-iteration/policy-bellman-contracting.md)
