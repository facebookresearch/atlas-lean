# Price of anarchy for pure equilibria on identical machines (multiplicative form)

Let $I$ be a finite set of tasks with weights $w_i \in \mathbb{R}$, let $m$ be a number of identical machines, and for an assignment $A : I \to \{1, \dots, m\}$ let $\ell_j(A) = \sum_{i : A(i) = j} w_i$ be the load of machine $j$.
Let $m \ge 1$ and let the weights be nonnegative. If $A$ is a pure Nash equilibrium and $B$ is any
assignment, then $(m + 1) \cdot \max_j \ell_j(A) \le 2m \cdot \max_j \ell_j(B)$.

Proof (Vöcking, *Algorithmic Game Theory*, Theorem 20.5): let $j^*$ carry the maximal load $C$. If no task
sits on $j^*$, then $C = 0$; if exactly one task sits on $j^*$, then $C$ is its weight, hence at most the
makespan of $B$. Otherwise some
task $i^*$ on $j^*$ has $w_{i^*} \le C/2$, and the equilibrium condition for $i^*$ forces every other
machine to carry load at least $C - w_{i^*} \ge C/2$; so the total weight is at least $(m + 1) C / 2$,
while it is at most $m$ times the makespan of $B$.

## Informally uses

- [Average load bound](sum-weight-le-mul-makespan.md): the total weight is at most $m$ times any makespan.
- [A single task bounds every makespan](weight-le-makespan.md): the case of at most one task on the busiest machine.
- [Loads add up to the total weight](sum-load.md): summing the equilibrium lower bounds on the loads.

## Background

- [List scheduling on identical machines](../../../ComputerScience/approximation-algorithms/list-scheduling-on-identical-machines/README.md): Graham's analysis of the greedy algorithm, which this argument follows (Vöcking, Section 20.2.1).
