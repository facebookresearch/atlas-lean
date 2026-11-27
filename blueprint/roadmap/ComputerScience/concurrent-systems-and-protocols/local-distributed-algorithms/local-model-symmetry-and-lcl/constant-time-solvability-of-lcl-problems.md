# Constant-time solvability of locally checkable labeling problems is undecidable

In the LOCAL model of distributed computing, no algorithm decides whether a given locally checkable labeling problem can be solved in a constant number of rounds; this holds already on two-dimensional grids with boundary, though not on toroidal grids.

**Setting.** In the LOCAL model, the nodes of a graph of bounded maximum degree carry unique identifiers and compute in synchronous rounds; in $t$ rounds each node learns its radius-$t$ neighborhood and then chooses its output. A *locally checkable labeling* (LCL) problem $P$ assigns to each graph $G$ a set $P(G)$ of feasible labelings $f : V(G) \to X$ with a finite output set $X$, such that for some constant $r$ a labeling is feasible if and only if every radius-$r$ neighborhood is labeled compatibly with some feasible labeling; $P$ is given by its finite list of allowed labeled neighborhoods. $P$ is *solvable in constant time* if some algorithm solves it in a number of rounds that does not depend on the size of the graph.

**Theorem (Naor and Stockmeyer).** It is undecidable, given an LCL problem, whether it can be solved in constant time in the LOCAL model. This remains undecidable when the inputs are restricted to two-dimensional grids with boundary (non-toroidal grids, with nodes of degree $2$ and $3$ on the boundary).

On toroidal two-dimensional grids, in contrast, constant-time solvability is trivial to decide, since only problems admitting a constant output are solvable in constant time; there, deciding between the complexities $\Theta(\log^* n)$ and $\Theta(n)$ is undecidable instead (Brandt, Hirvonen, Korhonen, Lempiäinen, Östergård, Purcell, Rybicki, Suomela and Uznański).

## Depends on

- [The LOCAL model](../../distributed-execution-models/the-local-model.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Halting is undecidable](../../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

For a Turing machine $M$, the LCL problem asks for the complete execution history of $M$ on the empty tape to be written in the lower-left corner of the grid, and allows padding everywhere else; the history can be checked locally, row by row. If $M$ halts after $t$ steps, a node decides in $O(t) = O(1)$ rounds whether it lies within distance $\Theta(t)$ of the corner and outputs either its part of the history or padding. The source states that the problem is solvable in constant time if and only if $M$ halts.

## Sources

- Moni Naor and Larry Stockmeyer, "What can be computed locally?", in *Proceedings of the 25th Annual ACM Symposium on Theory of Computing (STOC 1993)*, ACM, 1993, pp. 184–193, doi:[10.1145/167088.167149](https://doi.org/10.1145/167088.167149), and *SIAM Journal on Computing* 24(6), 1995, pp. 1259–1277, doi:[10.1137/S0097539793254571](https://doi.org/10.1137/S0097539793254571), the original result; not read, cited beside the source below.
- Sebastian Brandt, Juho Hirvonen, Janne H. Korhonen, Tuomo Lempiäinen, Patric R. J. Östergård, Christopher Purcell, Joel Rybicki, Jukka Suomela and Przemysław Uznański, "LCL Problems on Grids", in *Proceedings of the ACM Symposium on Principles of Distributed Computing (PODC 2017)*, ACM, 2017, pp. 101–110, doi:[10.1145/3087801.3087833](https://doi.org/10.1145/3087801.3087833); read in arXiv:1702.05456v2 ([arXiv](https://arxiv.org/abs/1702.05456v2)), which presents the result as established: Section 2 (related work, existence of algorithms and algorithm synthesis), the definitions of LCL problems in Section 3, and the comparison with Naor and Stockmeyer's construction after Theorem 3 in Section 6.
