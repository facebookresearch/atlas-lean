# Dynamic programming over a well-founded subproblem order

Let $\mathcal{P}$ be a finite set of subproblems with a well-founded dependency relation $\prec$, and for each $s \in \mathcal{P}$ let $F_s$ compute a value from the values of the subproblems $s' \prec s$. Then the recurrence $V(s) = F_s((V(s'))_{s' \prec s})$ has a unique solution $V$; bottom-up evaluation in any topological order of $\prec$ and top-down evaluation with memoization both return $V(s)$ for every $s$; and under a cost model that charges the evaluation of each $F_s$, bottom-up evaluation costs $\sum_{s \in \mathcal{P}} \mathrm{cost}(F_s)$ plus table overhead, while top-down evaluation of $V(s_0)$ costs the same sum restricted to the subproblems reachable from $s_0$ under $\prec$, hence at most the full sum, since each subproblem is solved at most once.

## Depends on

- [Cost-instrumented computations](../../sorting-and-searching/algorithm-analysis-models/cost-instrumented-computations.md)

## Sources

- J. Erickson, *Algorithms*, 1st ed., 2019, <https://jeffe.cs.illinois.edu/teaching/algorithms/>
- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*, 4th ed., MIT Press, 2022
