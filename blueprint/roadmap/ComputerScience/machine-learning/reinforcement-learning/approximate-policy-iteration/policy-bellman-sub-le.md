# One-sided contraction of a policy's Bellman operator

Let $M$ be a Markov decision process with finitely many states and stochastic transition probabilities, let $\gamma \ge 0$ and let $\pi$ be a deterministic stationary policy. If $V(s') - W(s') \le m$ for every state $s'$, then $T_\pi V(s) - T_\pi W(s) \le \gamma m$ for every state $s$.

Unlike [A policy's Bellman operator contracts by γ](../../../heuristic-search-and-planning/value-iteration/abs-policy-bellman-sub-le.md), this bound is one-sided, and $m$ may be negative. Approximate policy iteration needs this form, because the loss of a step is bounded above but not below.
