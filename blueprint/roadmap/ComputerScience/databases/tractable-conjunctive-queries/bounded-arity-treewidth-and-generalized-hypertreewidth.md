# Bounded arity makes treewidth and generalized hypertreewidth equivalent

Let $q$ be a conjunctive query over a schema whose relation names have arity at most $c \ge 1$, and let $k \ge 1$.
If $q \in \mathrm{GHW}(k)$ then $q \in \mathrm{TW}(ck - 1)$, and if $q \in \mathrm{TW}(k)$ then
$q \in \mathrm{GHW}(k + 1)$. Hence a class of conjunctive queries over schemas of bounded arity has bounded treewidth
if and only if it has bounded generalized hypertreewidth. Without the arity bound this fails: for $n \ge 3$ the
Boolean query $q_n$ with all atoms $E(x_i, x_j)$, $1 \le i, j \le n$, and the atom $T_n(x_1, \dots, x_n)$ is
acyclic, so in $\mathrm{GHW}(1)$, while its Gaifman graph is the complete graph on $x_1, \dots, x_n$, so
$\mathrm{tw}(q_n) = n - 1$ and the class $\{q_n : n \ge 3\}$ has unbounded treewidth.

## Depends on

- [Treewidth of a conjunctive query](treewidth-of-a-conjunctive-query.md)
- [Generalized hypertree decompositions and generalized hypertreewidth](generalized-hypertree-decompositions-and-width.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, the example preceding Lemma 23.1 and Lemma 23.1 (p. 192).
