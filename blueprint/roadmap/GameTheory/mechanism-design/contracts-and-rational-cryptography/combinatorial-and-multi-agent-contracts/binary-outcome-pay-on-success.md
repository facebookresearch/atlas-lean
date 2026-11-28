# With a binary outcome, contracts paying only on success are without loss

In a principal-agent instance with two outcomes, failure (reward $0$) and success (reward $1$), every contract $t = (t_0, t_1) \ge 0$ is weakly dominated for the principal by the contract $(0, t_1 - t_0)$ when $t_1 \ge t_0$, and by the zero contract otherwise. Hence optimal contracts may be taken of the form $(0, \alpha)$, which are linear contracts; in particular the optimal contract of a combinatorial instance with binary outcome is a linear contract.

## Proof sketch

Paying $t_0$ in both outcomes is a constant transfer that does not change the agent's ranking of actions, so subtracting it preserves the best response (including tie-breaking) and saves the principal $t_0$. If $t_1 < t_0$, the contract rewards failure, and paying zero induces an action whose success probability is at least as high while saving all payments.

## Depends on

- [Combinatorial-actions contract with a binary outcome](combinatorial-actions-binary-outcome-contract.md)
- [Hidden-action principal-agent instance and contract](../hidden-action-principal-agent-contracts/hidden-action-principal-agent-instance.md)
- [Linear contract and its critical values](../hidden-action-principal-agent-contracts/linear-contract-critical-values.md)

## Sources

- P. Dütting, T. Ezra, M. Feldman, T. Kesselheim, "Combinatorial Contracts", FOCS 2021; SIAM Journal on Computing 54(6) (2025), arXiv:2109.14260.
- P. Dütting, T. Roughgarden, I. Talgam-Cohen, "Simple versus Optimal Contracts", EC 2019, arXiv:1808.03713.
