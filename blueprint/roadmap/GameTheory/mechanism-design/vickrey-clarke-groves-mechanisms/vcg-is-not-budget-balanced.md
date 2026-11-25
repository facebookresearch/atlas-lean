# Efficiency and truthfulness do not imply budget balance

Consider a public decision between building a project and not, with two agents whose values for building are $v_1 = 2$ and $v_2 = -1$ and for not building $0$. The Vickrey–Clarke–Groves mechanism with Clarke pivot payments builds (total value $1 > 0$), is efficient and makes truthful reporting dominant. Its payments are $p_1 = \max(0, -1) - (-1) = 1$ and $p_2 = \max(2, 0) - 2 = 0$, so it collects $1 \ne 0$ and is not budget balanced. It is also not envy-free: agent 1's utility is $2 - 1 = 1$, while agent 1's utility for agent 2's position (the same decision with payment $0$) is $2$; envy compares one agent's utility for their own outcome and payment with that same agent's utility for another agent's.

## Proof depends on

- [Clarke pivot term](clarke-pivot.md): the Clarke pivot payments.
- [VCG with Clarke pivot payments is incentive compatible](is-incentive-compatible-clarke.md): truthful reporting is dominant.

## Sources

- The statement is derived on this page from its definitions and the linked results; no external source is followed.
