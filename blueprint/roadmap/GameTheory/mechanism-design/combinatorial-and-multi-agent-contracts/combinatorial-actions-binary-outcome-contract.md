# Combinatorial-actions contract with a binary outcome

A combinatorial contract instance has a finite set $A$ of $n$ actions with costs $c : A \to \mathbb{R}_{\ge 0}$ (additive: $c(S) = \sum_{a \in S} c(a)$), and a success probability function $f : 2^A \to [0, 1]$ that is monotone with $f(\emptyset) = 0$. The agent chooses a set $S \subseteq A$; the project succeeds with probability $f(S)$, yielding reward $1$ to the principal. A contract pays the agent $\alpha \in [0, 1]$ upon success and nothing upon failure. The agent chooses $S$ maximizing $\alpha f(S) - c(S)$ (ties broken in favour of the principal), and the principal's utility is $(1 - \alpha) f(S)$. The values of $\alpha$ at which the agent's demanded set changes are the critical values of the instance.

## Depends on

- [Linear contract and its critical values](../hidden-action-principal-agent-contracts/linear-contract-critical-values.md)
- [Submodular set function](../../../ComputerScience/approximation-algorithms/maximum-n-times-coverage/is-submodular.md)

## Sources

- P. Dütting, T. Ezra, M. Feldman, T. Kesselheim, "Combinatorial Contracts", FOCS 2021, arXiv:2109.14260.
