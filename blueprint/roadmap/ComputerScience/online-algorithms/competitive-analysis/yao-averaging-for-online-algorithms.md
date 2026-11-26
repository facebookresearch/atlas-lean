# Yao averaging for online algorithms

Let $\mathcal{D}$ be a probability distribution on request sequences of an online problem, and let $\rho > 0$. If every deterministic online strategy $A$ satisfies $\mathbb{E}_{\sigma \sim \mathcal{D}}[\mathrm{cost}_A(\sigma)] \ge \rho \cdot \mathbb{E}_{\sigma \sim \mathcal{D}}[\mathrm{OPT}(\sigma)]$, then every randomized (mixed) online strategy $R$ has a request sequence $\sigma$ in the support of $\mathcal{D}$ with $\mathbb{E}[\mathrm{cost}_R(\sigma)] \ge \rho \cdot \mathrm{OPT}(\sigma)$; in particular no randomized strategy is $(c, 0)$-competitive with $c < \rho$ against an oblivious adversary when $\mathbb{E}_{\mathcal{D}}[\mathrm{OPT}] > 0$.

## Proof sketch

Averaging the hypothesis over the distribution of deterministic strategies drawn by $R$ and exchanging the order of expectations gives $\mathbb{E}_\sigma[\mathbb{E}\,\mathrm{cost}_R(\sigma) - \rho\, \mathrm{OPT}(\sigma)] \ge 0$, so some $\sigma$ in the support has a nonnegative term.

## Depends on

- [Randomized online strategies against an oblivious adversary](randomized-online-strategies.md)
- [Yao's minimax principle](../../../TheoryOfComputation/randomized-and-quantum-complexity/yao-s-minimax-principle/yao-minimax.md)

## Proof depends on

- [Yao's minimax principle](../../../TheoryOfComputation/randomized-and-quantum-complexity/yao-s-minimax-principle/yao-minimax.md)

## Sources

- A. Borodin and R. El-Yaniv, "Online Computation and Competitive Analysis", Cambridge University Press, 1998.
- A. C.-C. Yao, "Probabilistic Computations: Toward a Unified Measure of Complexity", Proceedings of the 18th IEEE Symposium on Foundations of Computer Science (FOCS), 1977.
