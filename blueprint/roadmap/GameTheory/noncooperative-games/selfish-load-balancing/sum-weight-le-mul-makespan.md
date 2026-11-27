# Average load bound

Let $I$ be a finite set of tasks with weights $w_i \in \mathbb{R}$, let $m$ be a number of identical machines, and for an assignment $A : I \to \{1, \dots, m\}$ let $\ell_j(A) = \sum_{i : A(i) = j} w_i$ be the load of machine $j$.
For $m \ge 1$, every assignment $B$ has makespan at least the average load:
$\sum_{i} w_i \le m \cdot \max_j \ell_j(B)$ (the lower bound on the optimum used in the proof of Vöcking,
*Algorithmic Game Theory*, Theorem 20.5).

## Informally uses

- [Loads add up to the total weight](sum-load.md): rewrite the total weight as a sum of $m$ loads.
