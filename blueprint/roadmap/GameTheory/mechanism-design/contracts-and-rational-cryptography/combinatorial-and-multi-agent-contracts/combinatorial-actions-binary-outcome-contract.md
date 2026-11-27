# Combinatorial-actions contract with a binary outcome

A combinatorial contract instance has a finite set $A$ of $n$ actions with costs $c : A \to \mathbb{R}_{\ge 0}$ (additive: $c(S) = \sum_{a \in S} c(a)$), and a success probability function $f : 2^A \to [0, 1]$ that is monotone with $f(\emptyset) = 0$. The agent chooses a set $S \subseteq A$; the project succeeds with probability $f(S)$, yielding the principal a reward normalized to $1$ (failure yields $0$). A contract pays the agent $\alpha \in [0, 1]$ upon success and nothing upon failure. The agent chooses $S$ maximizing $\alpha f(S) - c(S)$ (ties broken in favour of the principal, that is, towards a set of largest $f(S)$), and the principal's utility is $(1 - \alpha) f(S)$. Write $V(\alpha)$ for the success probability $f(S)$ of the set the agent chooses at $\alpha$; it is nondecreasing and right-continuous in $\alpha$, and the critical values of the instance are the points $\alpha \in (0, 1]$ at which $V$ jumps, i.e. $V(\alpha) \ne V(\alpha - \varepsilon)$ for every $\varepsilon > 0$.

## Depends on

- [Linear contract and its critical values](../hidden-action-principal-agent-contracts/linear-contract-critical-values.md)
- [Submodular set function](../../../../ComputerScience/approximation-algorithms/maximum-n-times-coverage/is-submodular.md)

## Sources

- P. Dütting, T. Ezra, M. Feldman, T. Kesselheim, "Combinatorial Contracts", FOCS 2021; SIAM Journal on Computing 54(6) (2025), arXiv:2109.14260.
