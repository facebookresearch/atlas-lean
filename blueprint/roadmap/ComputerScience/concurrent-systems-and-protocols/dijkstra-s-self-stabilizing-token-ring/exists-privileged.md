# Dijkstra's token ring never deadlocks

In Dijkstra's $K$-state token ring, machines $0, \dots, n$ sit on a ring with states in $\mathbb{Z}/K$; machine $0$ is privileged when its state equals its predecessor's and then increments it, and every other machine is privileged when its state differs from its predecessor's and then copies it. Under a central daemon one privileged machine moves per step, and a configuration is legitimate when exactly one machine is privileged. Every configuration has a privileged machine.

## Sources

- E. W. Dijkstra, "Self-stabilizing systems in spite of distributed control", *Communications of the ACM* 17 (1974).
