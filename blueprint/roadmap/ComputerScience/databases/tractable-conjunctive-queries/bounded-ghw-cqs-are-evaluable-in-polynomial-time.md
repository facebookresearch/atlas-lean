# Conjunctive queries of bounded generalized hypertreewidth are evaluable in polynomial time

Fix $k \ge 1$. For every Boolean conjunctive query $q$ of generalized hypertreewidth at most $k$ and every database
$D$, $q(D)$ is true if and only if the [$k$-consistency procedure](k-consistency-procedure.md) on $q$ and $D$ does not
fail. Hence $\mathrm{GHW}(k)$-Evaluation, the problem of deciding, for a conjunctive query $q$ of generalized
hypertreewidth at most $k$, a database $D$ and a tuple $\bar a$, whether $\bar a \in q(D)$, can be solved in time
$O(\lVert D \rVert^{2k} \cdot \lVert q \rVert^{2k})$ with no decomposition as input. A candidate $\bar a$ that assigns different values to
two positions of the output tuple holding the same variable, or a value other than $c$ to a position holding a
constant $c$, is rejected; otherwise substituting its values for the distinct output variables gives a Boolean query
whose generalized hypertreewidth is still at most $k$.

## Depends on

- [Generalized hypertree decompositions and generalized hypertreewidth](generalized-hypertree-decompositions-and-width.md)
- [The k-consistency procedure for Boolean conjunctive queries](k-consistency-procedure.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Algorithm 9 ($k$-Consistency) and Propositions 22.4 and 22.5 (pp. 185–187) and Theorem 22.6 (p. 187).
