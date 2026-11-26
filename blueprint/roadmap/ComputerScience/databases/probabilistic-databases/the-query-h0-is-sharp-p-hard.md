# The non-hierarchical query R(x), S(x, y), T(y) is #P-hard

Computing the probability of the Boolean query $h_0 = R(x), S(x, y), T(y)$ on tuple-independent probabilistic
databases is $\#P$-hard. Given a bipartite graph $E \subseteq [n_1] \times [n_2]$, take $R = [n_1]$ and $T = [n_2]$
with all probabilities $1/2$ and $S = E$ with probability $1$; then the number of satisfying assignments of the
positive partitioned formula $\bigvee_{(i, j) \in E} X_i Y_j$ equals $2^{n_1 + n_2}\, p(h_0)$, and counting the
satisfying assignments of positive partitioned 2-CNF formulas (equivalently of these 2-DNF formulas, by complementing)
is $\#P$-complete.

## Depends on

- [Tuple-independent probabilistic databases and query probability](tuple-independent-probabilistic-databases.md)
- [$\#P$-complete functions](../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/sharp-pcomplete.md)

## Sources

- N. Dalvi and D. Suciu, "The dichotomy of probabilistic inference for unions of conjunctive queries", *Journal of the ACM*, 2012; authors' manuscript <https://homes.cs.washington.edu/~suciu/jacm-dichotomy.pdf>, Theorem 5.1 (credited there to Provan and Ball, 1983) and Proposition 5.2.
