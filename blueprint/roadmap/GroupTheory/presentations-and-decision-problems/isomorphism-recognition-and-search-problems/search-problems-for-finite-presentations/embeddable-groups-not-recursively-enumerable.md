# A finitely presented group whose embeddable finitely presented groups are not recursively enumerable

There is a finitely presented group $G$ such that the set of finite presentations of groups that embed in $G$ is not recursively enumerable.

By Theorem 6.8 of the source, there exists a finitely presented group $G$ such that the set of all finite presentations $P$ for which $\overline{P}$ embeds in $G$ is not recursively enumerable. Here $\overline{P}$ is the group presented by $P$, and embeds means is isomorphic to a subgroup.

## Depends on

- [Group](../../../group-basics/group.md)

## Proof depends on

- [Halting is undecidable](../../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

Let $\mathrm{TorOrd}(G)$ be the set of orders $n \ge 2$ of non-trivial torsion elements of $G$. Take a recursively enumerable non-recursive set $W$ and the recursive presentation $\langle x_0, x_1, \dots \mid x_i^{p_i} = 1 \ (i \ge 0),\ x_j = 1 \ (j \in W) \rangle$, with $p_i$ the $i$-th prime; its torsion orders are the primes $p_j$ with $j \notin W$. Embeddings into a two-generator recursively presented group and then, by Higman's embedding theorem, into a finitely presented group $Q$, all built from free products with amalgamation and HNN extensions, preserve the set of torsion orders (Lemma 6.11). Since $\langle t \mid t^m \rangle$ embeds in $Q$ exactly when $m \in \mathrm{TorOrd}(Q)$, an enumeration of the finite presentations embedding in $Q$ would enumerate the complement of $W$ in the indices.

## Sources

- M. Chiodo, "Finding non-trivial elements and splittings in groups", Journal of Algebra 331 (2011), no. 1, 271–284, https://doi.org/10.1016/j.jalgebra.2010.12.013; arXiv:1002.2786v3 (Lemma 6.11 and Theorem 6.8 of arXiv:1002.2786v3).
