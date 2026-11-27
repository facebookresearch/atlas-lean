# Soundness of the simplex method with Dantzig's rule

The simplex method with **Dantzig's largest-coefficient rule** (enter a nonbasic variable of largest reduced cost $c_s > 0$, smallest index on ties; leave by the ratio test, smallest index on ties) is sound. Call a solution of a dictionary over an ordered field **feasible** if every variable is nonnegative; pivoting preserves the solution set, so all dictionaries of one run have the same feasible set. Whenever the method stops at a feasible dictionary, it either reports an optimal basic solution, which is feasible and maximizes the objective over all feasible solutions, or reports unboundedness, in which case the objective is unbounded above on the feasible solutions. (Unlike Bland's rule, Dantzig's rule may cycle on degenerate programs.)

## Depends on

- [Simplex dictionaries and pivoting](simplex-dictionaries.md)

## Sources

- V. Chvátal, "Linear Programming", W. H. Freeman, 1983.
