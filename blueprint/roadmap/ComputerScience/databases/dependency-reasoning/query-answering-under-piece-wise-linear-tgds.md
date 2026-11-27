# Query answering under piece-wise linear TGDs is undecidable

Certain answering of conjunctive queries under piece-wise linear sets of tuple-generating dependencies is undecidable already in data complexity: one fixed set of such rules and one fixed Boolean conjunctive query suffice. Adding wardedness brings the problem down to NLOGSPACE.

**Theorem (Berger, Gottlob, Pieris and Sallinger).** $\mathsf{CQAns}(\mathsf{PWL})$ is undecidable in data complexity: there are a fixed [piece-wise linear](piece-wise-linear-sets-of-tgds.md) set $\Sigma$ of TGDs and a fixed Boolean conjunctive query $q$ such that no algorithm decides, given a database $D$, whether the empty tuple belongs to $\mathrm{cert}(q, D, \Sigma)$.

By contrast, for sets that are both warded and piece-wise linear the problem is PSPACE-complete in combined complexity and NLOGSPACE-complete in data complexity, and for warded sets alone it is EXPTIME-complete in combined and PTIME-complete in data complexity. The source presents the undecidability as the formal justification for combining piece-wise linearity with wardedness.

## Depends on

- [Piece-wise linear sets of TGDs](piece-wise-linear-sets-of-tgds.md)
- [Tuple- and equality-generating dependencies and the chase](../dependencies-and-the-chase/tuple-and-equality-generating-dependencies-and-the-chase.md)
- [Answers of a conjunctive query](../conjunctive-queries/answers-of-a-conjunctive-query.md)
- [Data, expression and combined complexity of query evaluation](../query-language-expressiveness/data-expression-and-combined-complexity-of-query-evaluation.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof reduces from a tiling problem of van Emde Boas. A tiling system $(T, L, R, H, V, a, b)$ has a finite set $T$ of tiles, disjoint sets $L, R \subseteq T$ of left and right border tiles, horizontal and vertical constraints $H, V \subseteq T^2$, a start tile $a$ and a finish tile $b$; a tiling is a map $f : [n] \times [m] \to T$ for some $n, m > 0$ with $f(1,1) = a$, $f(1,m) = b$, $f(1,i) \in L$ and $f(n,i) \in R$ for every $i$, respecting $H$ and $V$. Whether a tiling exists is undecidable. The database $D_{\mathbb{T}}$ stores the tiling system with unary predicates Tile, Left, Right, Start, Finish and binary predicates $H$, $V$. The fixed TGDs build all rows respecting $H$ as atoms $\mathrm{Row}(p, c, s, e)$ (previous row id, current id, first and last tile), using existential variables for fresh row ids; then the pairs of rows compatible under $V$ (predicate Comp); then the candidate tilings with their bottom-left tile (predicate CTiling), each TGD having at most one body atom mutually recursive with its head. The query $q \leftarrow \mathrm{CTiling}(x, y), \mathrm{Finish}(y)$ checks the finish condition, and $\mathbb{T}$ has a tiling iff $() \in \mathrm{cert}(q, D_{\mathbb{T}}, \Sigma)$.

A good expansion links the undecidability of this rectangle tiling problem (with border tiles, start and finish tiles); the plane tiling problem has a page, but this variant does not.

## Sources

- Gerald Berger, Georg Gottlob, Andreas Pieris and Emanuel Sallinger, "The Space-Efficient Core of Vadalog", Proceedings of the 38th ACM SIGMOD-SIGACT-SIGAI Symposium on Principles of Database Systems (PODS 2019), pp. 270–284, 2019, <https://doi.org/10.1145/3294052.3319688>. Read in arXiv:1809.05951v1, <https://arxiv.org/abs/1809.05951v1>; Theorem 5.1 with its proof in Section 5, Theorem 4.2 and Proposition 3.2 (decidable cases), numbering of arXiv:1809.05951v1.
- Gerald Berger, Georg Gottlob, Andreas Pieris and Emanuel Sallinger, "The Space-Efficient Core of Vadalog", ACM Transactions on Database Systems 47(1), pp. 1–46, 2022, <https://doi.org/10.1145/3488720> (journal version, not read).
