# Legitimate configurations of Dijkstra's token ring are closed

In Dijkstra's $K$-state token ring, machines $0, \dots, n$ sit on a ring with states in $\mathbb{Z}/K$; machine $0$ is privileged when its state equals its predecessor's and then increments it, and every other machine is privileged when its state differs from its predecessor's and then copies it. Under a central daemon one privileged machine moves per step, and a configuration is legitimate when exactly one machine is privileged. Every step from a legitimate configuration leads to a legitimate configuration.

## Sources

- E. W. Dijkstra, "Self-stabilizing systems in spite of distributed control", *Communications of the ACM* 17 (1974).
