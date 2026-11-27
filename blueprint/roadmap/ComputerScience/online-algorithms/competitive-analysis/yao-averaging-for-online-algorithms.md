# Yao averaging for online algorithms

Consider an online problem restricted to a finite set of deterministic online strategies and a finite set of request sequences (so that every distribution $\mathcal{D}$ on request sequences has finite support and finite $\mathbb{E}_{\sigma \sim \mathcal{D}}[\mathrm{OPT}(\sigma)]$), and let $\rho > 0$. If every deterministic online strategy $A$ satisfies $\mathbb{E}_{\sigma \sim \mathcal{D}}[\mathrm{cost}_A(\sigma)] \ge \rho \cdot \mathbb{E}_{\sigma \sim \mathcal{D}}[\mathrm{OPT}(\sigma)]$, then every randomized (mixed) online strategy $R$ has a request sequence $\sigma$ in the support of $\mathcal{D}$ with $\mathbb{E}[\mathrm{cost}_R(\sigma)] \ge \rho \cdot \mathrm{OPT}(\sigma)$ (Kesselheim, Lecture 5, Theorem 5.1, applied to $\mathrm{cost}_A(\sigma) - \rho \cdot \mathrm{OPT}(\sigma)$); in particular no randomized strategy is $(c, 0)$-competitive with $c < \rho$ against an oblivious adversary when $\mathbb{E}_{\mathcal{D}}[\mathrm{OPT}] > 0$.

## Proof sketch

Averaging the finite-sum hypothesis over the distribution of deterministic strategies drawn by $R$ and exchanging the finite expectations gives $\mathbb{E}_\sigma[\mathbb{E}\,\mathrm{cost}_R(\sigma) - \rho\, \mathrm{OPT}(\sigma)] \ge 0$, so some $\sigma$ in the support of $\mathcal{D}$ has a nonnegative term. Without finiteness (or an explicit integrability assumption $\mathbb{E}_{\mathcal{D}}[\mathrm{OPT}] < \infty$), the statement fails: with unit cost per request ($\mathrm{OPT}(\sigma) = |\sigma|$), $\Pr(|\sigma| = 4^n) = 2^{-n}$ and $\rho = 2$, both expectations are infinite while every strategy is $(1, 0)$-competitive.

## Depends on

- [Randomized online strategies against an oblivious adversary](randomized-online-strategies.md)

## Proof depends on

- [Yao's minimax principle](../../../TheoryOfComputation/randomized-and-quantum-complexity/yao-s-minimax-principle/yao-minimax.md)

## Sources

- A. Borodin and R. El-Yaniv, "Online Computation and Competitive Analysis", Cambridge University Press, 1998.
- A. C.-C. Yao, "Probabilistic Computations: Toward a Unified Measure of Complexity", Proceedings of the 18th IEEE Symposium on Foundations of Computer Science (FOCS), 1977.
- Thomas Kesselheim, "Algorithms and Uncertainty" (University of Bonn, Winter 2017/18), Lecture 5, Theorem 5.1 (Yao's principle for finite classes of deterministic algorithms and request sequences).
