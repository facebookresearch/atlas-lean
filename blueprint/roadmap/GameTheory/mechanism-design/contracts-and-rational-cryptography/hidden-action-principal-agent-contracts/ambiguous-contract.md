# Ambiguous contract and max-min agent

In a principal-agent instance, an ambiguous contract $\langle \tau, i \rangle$ consists of a nonempty finite set $\tau = \{t^1, \dots, t^k\}$, $k \ge 1$, of contracts and a recommended action $i$. The agent, who is ambiguity averse, evaluates each action $i'$ by its worst-case utility $U_A(i' \mid \tau) = \min_{\ell} \bigl(T_{i'}(t^\ell) - c_{i'}\bigr)$. The ambiguous contract is incentive compatible, and then implements $i$, if $i$ maximizes $U_A(\cdot \mid \tau)$ over all actions; the agent follows the recommendation of an incentive-compatible ambiguous contract. It is consistent if every contract of $\tau$ yields the same expected payment at the recommended action, $T_i(t^\ell) = T_i(t^{\ell'})$ for all $\ell, \ell'$, so the principal, who selects which contract of $\tau$ to apply, is indifferent among them. For a consistent incentive-compatible ambiguous contract write $T_i(\tau)$ for this common payment; the principal's utility is $R_i - T_i(\tau)$ and the agent's is $T_i(\tau) - c_i$. With $k = 1$ this is a classic contract together with a recommended best response.

## Depends on

- [Hidden-action principal-agent instance and contract](hidden-action-principal-agent-instance.md)

## Sources

- P. Dütting, M. Feldman, D. Peretz, L. Samuelson, "Ambiguous Contracts", EC 2023; Econometrica 92(6) (2024), arXiv:2302.07621.
