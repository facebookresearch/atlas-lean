# Conjunctive queries of bounded generalized hypertreewidth are evaluable in polynomial time

Fix $k \ge 1$. $\mathrm{GHW}(k)$-Evaluation, the problem of deciding, for a conjunctive query $q$ of generalized
hypertreewidth at most $k$, a database $D$ and a tuple $\bar a$, whether $\bar a \in q(D)$, can be solved in time
$O(\lVert D \rVert^{2k} \cdot \lVert q \rVert^{2k})$, by the $k$-consistency procedure, which needs no
decomposition as input.

## Depends on

- [Generalized hypertree decompositions and generalized hypertreewidth](generalized-hypertree-decompositions-and-width.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Algorithm 9 ($k$-Consistency) and Propositions 22.4 and 22.5 (pp. 185–187) and Theorem 22.6 (p. 187).
