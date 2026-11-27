# Intersections of k matroids are k-systems

Every matroid is a $1$-system, and the intersection of $k \ge 1$ matroids on the same ground set is a $k$-system. More generally, an independence system is a $p$-system if and only if every independent set that is blocked (cannot be extended within $Y$) has size at least $1/p$ times every independent subset of $Y$.

## Proof sketch

If $A$ and $B$ are maximal in $Y$ for the intersection, each element of $A \setminus B$ is blocked from $B$ in at least one matroid; in each matroid the elements blocked by $B$ that are independent together number at most $|B \setminus A|$, so $|A \setminus B| \le k |B \setminus A|$.

## Depends on

- [p-systems](p-systems.md)
- [Edmonds' matroid intersection theorem](../../../Combinatorics/matroid-theory/matroid-intersection-theorem/edmonds-matroid-intersection.md)

## Sources

- T. A. Jenkyns, "The Efficacy of the Greedy Algorithm", Proceedings of the 7th Southeastern Conference on Combinatorics, Graph Theory and Computing, 1976.
- G. Călinescu, C. Chekuri, M. Pál and J. Vondrák, "Maximizing a Monotone Submodular Function Subject to a Matroid Constraint", SIAM Journal on Computing 40(6), 2011.
