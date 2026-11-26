# The state equation of a Petri net

Let $N$ be a pure [Petri net](place-transition-petri-nets.md), one with no place that is both an input and an output of the same transition, with $n$ transitions and $m$ places. Its *incidence matrix* is the $n \times m$ integer matrix $A$ with $a_{ij} = w(t_i, p_j) - w(p_j, t_i)$. If $M_0 [\sigma\rangle M_d$ and $x \in \mathbb{N}^n$ counts how often each transition occurs in $\sigma$, then

$$M_d = M_0 + A^T x.$$

So if $M_d$ is reachable from $M_0$, the equation $M_d - M_0 = A^T x$ has a solution in nonnegative integers; the converse fails in general.

## Depends on

- [Place/transition Petri nets](place-transition-petri-nets.md)
- [Reachability set and reachability graph](reachability-set-and-reachability-graph.md)

## Sources

- T. Murata, "Petri nets: Properties, analysis and applications", *Proceedings of the IEEE* 77(4):541–580, 1989, Section V-B ("Incidence matrix and state equation"): the incidence matrix (2), the state equation (4), the summed equation (10) giving the necessary reachability condition, and Theorem 2.
