# Combinatorial-actions contract with a binary outcome

A combinatorial contract instance has a finite set $A$ of $n$ actions with positive costs $c : A \to \mathbb{R}_{> 0}$ (additive: $c(S) = \sum_{a \in S} c(a)$, so $c(\emptyset) = 0$), and a success probability function $f : 2^A \to [0, 1]$ that is monotone with $f(\emptyset) = 0$. The agent chooses a set $S \subseteq A$; the project succeeds with probability $f(S)$, yielding the principal a reward normalized to $1$ (failure yields $0$). A contract pays the agent $\alpha \in [0, 1]$ upon success and nothing upon failure. The agent chooses $S$ maximizing $\alpha f(S) - c(S)$ (ties broken in favour of the principal), and the principal's utility is $(1 - \alpha) f(S)$. Write $V(\alpha) = \max\{ f(S) : S \text{ maximizes } \alpha f(S) - c(S) \}$ for $\alpha \in [0, 1]$, the largest success probability among the agent's best responses; for $\alpha < 1$ this is the success probability of every best response that is best for the principal, and at $\alpha = 1$, where the principal's utility is $0$ for every set, $V(1)$ still takes the largest $f(S)$. $V$ is nondecreasing and right-continuous on $[0, 1]$, and the critical values of the instance are the points $\alpha \in (0, 1]$ at which $V$ jumps, i.e. $V(\alpha) \ne V(\alpha - \varepsilon)$ for every $\varepsilon$ with $0 < \varepsilon \le \alpha$.

## Depends on

- [Linear contract and its critical values](../hidden-action-principal-agent-contracts/linear-contract-critical-values.md)
- [Submodular set function](../../../../ComputerScience/approximation-algorithms/maximum-n-times-coverage/is-submodular.md)

## Sources

- P. Dütting, T. Ezra, M. Feldman, T. Kesselheim, "Combinatorial Contracts", FOCS 2021; SIAM Journal on Computing 54(6) (2025), arXiv:2109.14260.
