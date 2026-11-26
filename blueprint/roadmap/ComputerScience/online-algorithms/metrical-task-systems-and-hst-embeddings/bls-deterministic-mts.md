# Borodin–Linial–Saks: deterministic MTS has ratio exactly $2n - 1$

On every metric space with $n$ points, the best competitive ratio of a deterministic online algorithm for metrical task systems is exactly $2n - 1$: there is a $(2n-1)$-competitive deterministic algorithm, and no deterministic algorithm achieves a ratio below $2n - 1$.

## Proof sketch

The upper bound is a work-function algorithm that stays in its state until the accumulated work-function value there exceeds the cheapest alternative by the distance to it, analyzed by traversing a minimum spanning tree in a balanced way. The lower bound uses a cruel adversary that always puts a tiny cost on the algorithm's current state, forcing it to move; averaging over the $n$ possible offline strategies that each stay at one state gives the factor $2n - 1$.

## Depends on

- [Metrical task systems](metrical-task-system.md)

## Sources

- Allan Borodin, Nathan Linial, Michael E. Saks, "An Optimal On-Line Algorithm for Metrical Task System", Journal of the ACM 39(4) (1992).
