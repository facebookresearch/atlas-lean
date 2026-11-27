# Glauber dynamics for proper colorings with a frozen boundary

Let $G = (V,E)$ be a finite graph with $n \ge 1$ vertices and maximum degree $\Delta$, let $q \ge 1$, and let $U \subseteq V$ be nonempty, so that a vertex of $U$ can be sampled. *Glauber dynamics updating $U$* is the Markov chain on all colorings $x : V \to \{1, \dots, q\}$ (proper or not) that, from $x$, picks a vertex $w \in U$ uniformly at random and replaces $x(w)$ by a color chosen uniformly from the colors not used by $x$ on the neighbors of $w$ (leaving $x(w)$ unchanged if no color is allowed). The case $U = V$ is the standard Glauber (heat-bath) dynamics for $q$-colorings. For a proper coloring $b$, the set $X_U(b)$ of proper colorings agreeing with $b$ off $U$ is the *frozen-boundary* state space.

## Depends on

- [Stochastic matrix](../../kolmogorov-s-criterion-for-reversibility/stochastic-matrix.md)

## Sources

- David A. Levin and Yuval Peres, "Markov Chains and Mixing Times", 2nd ed., American Mathematical Society, 2017.
