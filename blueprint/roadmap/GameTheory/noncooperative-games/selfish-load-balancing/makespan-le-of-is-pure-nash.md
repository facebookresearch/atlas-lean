# Price of anarchy for pure equilibria on identical machines

Let $I$ be a finite set of tasks with weights $w_i \in \mathbb{R}$, let $m$ be a number of identical machines, and for an assignment $A : I \to \{1, \dots, m\}$ let $\ell_j(A) = \sum_{i : A(i) = j} w_i$ be the load of machine $j$.
For $m \ge 1$ identical machines and nonnegative weights, every pure Nash equilibrium $A$ satisfies
$\max_j \ell_j(A) \le \bigl(2 - \tfrac{2}{m + 1}\bigr) \max_j \ell_j(B)$ for every assignment $B$, in
particular for an optimal one.

## Informally uses

- [Price of anarchy for pure equilibria on identical machines (multiplicative form)](succ-mul-makespan-le.md): divide by $m + 1$.

## Background

- [Price of anarchy 4/3 for affine latencies](../selfish-routing-and-the-price-of-anarchy/cost-le-of-affine.md): the nonatomic routing analogue, for a utilitarian social cost.

## Sources

- B. Vöcking, "Selfish load balancing", *Algorithmic Game Theory* (Cambridge University Press 2007), Theorem 20.5. The bound is tight (Exercise 20.2 there; the two-machine instance of Section 20.1.2 attains $4/3$).
