# Pure Nash equilibrium of the load balancing game

Let $I$ be a finite set of tasks with weights $w_i \in \mathbb{R}$, let $m$ be a number of identical machines, and for an assignment $A : I \to \{1, \dots, m\}$ let $\ell_j(A) = \sum_{i : A(i) = j} w_i$ be the load of machine $j$.
The assignment $A$ is a pure Nash equilibrium if no task can lower its cost by moving alone: for every task
$i$ and every machine $k \ne A(i)$, $\ell_{A(i)}(A) \le \ell_k(A) + w_i$, the load that $i$ would experience
on $k$ (Vöcking, *Algorithmic Game Theory*, Proposition 20.2, specialised to identical machines).

## Remarks

- Moving to its own machine is not a deviation, so the condition is required only for $k \neq A(i)$; for nonnegative weights it would hold trivially there.
