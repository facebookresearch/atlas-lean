# Soundness of the simplex method with Dantzig's rule

The simplex method with **Dantzig's largest-coefficient rule** (enter a nonbasic variable of largest reduced cost $c_s > 0$, smallest index on ties; leave by the ratio test, smallest index on ties) is sound. Call a solution of a dictionary over an ordered field **feasible** if every variable is nonnegative; pivoting preserves the solution set, so all dictionaries of one run have the same feasible set. Whenever the method stops at a feasible dictionary, it either reports an optimal basic solution, which is feasible and maximizes the objective over all feasible solutions, or reports unboundedness, in which case the objective is unbounded above on the feasible solutions. The method stops at a feasible dictionary $z = z_0 + \sum_j c_j x_j$ when no $c_j$ is positive, and then the basic solution is optimal, or when the entering variable $x_s$ has $c_s > 0$ and $a_{is} \ge 0$ in every row, and then the objective is unbounded along a feasible ray; these are the optimality and unboundedness criteria of the simplex method (Orlin, MIT 15.053 Lecture 5, slides 6 and 7; Todd, Cornell OR 630 Lecture 10, Theorems 1 and 2). (Unlike Bland's rule, Dantzig's rule may cycle on degenerate programs.)

## Depends on

- [Simplex dictionaries and pivoting](simplex-dictionaries.md)

## Sources

- V. Chvátal, "Linear Programming", W. H. Freeman, 1983.
- J. Orlin, "Simplex Method Continued" (Lecture 5), 15.053 Optimization Methods in Management Science, MIT OpenCourseWare, Spring 2013, slides 6 ("Ending conditions: Optimality") and 7 ("Ending conditions: Unboundedness"): <https://ocw.mit.edu/courses/15-053-optimization-methods-in-management-science-spring-2013/32b25e3b5058d23335e27a34e948e5f5_MIT15_053S13_lec5.pdf>.
- M. Todd, OR 630 Mathematical Programming, Lecture 10 (September 27, 2005; notes by N. Diener), Cornell University, Theorem 1 (Optimality Criterion) and Theorem 2 (Unboundedness Criterion): <https://people.orie.cornell.edu/miketodd/or630/lecture10.pdf>.
