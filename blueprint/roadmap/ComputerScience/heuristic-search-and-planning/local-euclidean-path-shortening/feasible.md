# Feasible polyline

Let $F \subseteq \mathbb{R}^2$. Feasibility of a finite list of points of the Euclidean plane in $F$ is defined recursively:

- the empty list is feasible;
- a one-point list $(x)$ is feasible when $x \in F$;
- $(a, b, p_3, \dots, p_n)$ is feasible when the closed segment $[a, b]$ lies in $F$ and $(b, p_3, \dots, p_n)$ is feasible.

Hence a nonempty polyline is feasible exactly when all its vertices and all closed segments between consecutive vertices lie in $F$.
