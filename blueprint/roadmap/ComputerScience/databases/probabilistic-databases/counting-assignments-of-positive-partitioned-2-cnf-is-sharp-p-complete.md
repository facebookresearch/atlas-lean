# Counting satisfying assignments of positive partitioned 2-CNF formulas is #P-complete

Let $X_1, \dots, X_{n_1}$ and $Y_1, \dots, Y_{n_2}$ be disjoint sets of Boolean variables and
$E \subseteq [n_1] \times [n_2]$ a bipartite graph. The positive partitioned 2-CNF formula defined by $E$ is
$\Phi_E = \bigwedge_{(i, j) \in E} (X_i \vee Y_j)$. The function that maps (an encoding of) $E$ to the number of
satisfying assignments of $\Phi_E$ is $\#P$-complete.

## Depends on

- [$\#P$-complete functions](../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/sharp-pcomplete.md)

## Sources

- N. Dalvi and D. Suciu, "The dichotomy of probabilistic inference for unions of conjunctive queries", *Journal of the ACM* 59(6), Article 30, 2012, with theorem numbers as in the authors' copy <https://homes.cs.washington.edu/~suciu/jacm-dichotomy.pdf>: Theorem 5.1, credited there to J. S. Provan and M. O. Ball, "The complexity of counting cuts and of computing
  the probability that a graph is connected", *SIAM Journal on Computing* 12(4), 1983.
