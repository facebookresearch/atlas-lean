# Equivalence of general threshold and cascade models

Every order-independent cascade model on a finite graph induces a general threshold model (with $g_v(A)$ the probability that some member of $A$ activates $v$) whose distribution of final active sets, from every seed set, coincides with that of the cascade model; and every general threshold model arises from a cascade model in this way. The independent cascade model corresponds to $g_v(A) = 1 - \prod_{u \in A}(1 - p_{uv})$.

## Proof sketch

Couple the two processes vertex by vertex: the probability that $v$ is still inactive after a set $A$ of its neighbours has tried is $1 - g_v(A)$ in both models, independently of order, so the final sets have the same law.

## Depends on

- [General threshold, linear threshold and cascade models of influence](general-threshold-linear-threshold-and-cascade-models-of-influence.md)

## Sources

- David Kempe, Jon Kleinberg and Eva Tardos, "Influential Nodes in a Diffusion Model for Social Networks", Automata, Languages and Programming (ICALP 2005), 2005.
- Jon Kleinberg, "Cascading Behavior in Networks: Algorithmic and Economic Issues", Algorithmic Game Theory, Cambridge University Press, 2007.
