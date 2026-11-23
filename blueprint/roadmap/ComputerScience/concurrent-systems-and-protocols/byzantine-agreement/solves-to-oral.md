# Byzantine agreement yields the Byzantine generals problem

Let $Q$ be a [synchronous Byzantine agreement protocol](agreement-protocol.md) that reaches Byzantine agreement with at most $m$ faulty processes in $T$ rounds. Then for every commander $c$, default order $d$ and default message $m_0$, the [commander protocol built from $Q$](to-oral.md) solves the Byzantine generals problem with commander $c$ and at most $m$ traitors in $T + 1$ rounds.

The reduction is the standard one between the two problems: in an extra first round the commander sends its order to everyone, and each general then runs the agreement protocol with the order it received as input. Agreement gives condition IC1; validity gives IC2, because a loyal commander sends the same order to every loyal general.

## Informally uses

- [The commander protocol simulates the agreement protocol](state-to-oral.md): after round $r + 1$ every loyal general holds its state after round $r$ of the agreement protocol.

## Background

- [Solving the Byzantine generals problem](../byzantine-generals-problem/solves.md): the target notion.
