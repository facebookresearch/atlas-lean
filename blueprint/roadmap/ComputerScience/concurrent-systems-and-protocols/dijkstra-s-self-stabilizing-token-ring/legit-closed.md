# Legitimate configurations of Dijkstra's token ring are closed

In Dijkstra's token ring, machines $0, \dots, n$, indexed by $\mathbb{Z}/(n+1)$ (a single machine when $n = 0$), sit on a ring with states in $\mathbb{Z}/K$; machine $0$ is privileged when its state equals its predecessor's and then increments it, and every other machine is privileged when its state differs from its predecessor's and then copies it. Under a central daemon one privileged machine moves per step, and a configuration is legitimate when exactly one machine is privileged. For $K \ne 0$ this is Dijkstra's $K$-state protocol, with states $0, \dots, K-1$ added modulo $K$; for $K = 0$ the states are integers, since $\mathbb{Z}/0 = \mathbb{Z}$, so the same definitions describe a variant with unbounded integer states. Every step from a legitimate configuration leads to a legitimate configuration, for every $n$ and every $K$, including $n = 0$ and $K = 0$.

## Sources

- E. W. Dijkstra, "Self-stabilizing systems in spite of distributed control", *Communications of the ACM* 17 (1974).
