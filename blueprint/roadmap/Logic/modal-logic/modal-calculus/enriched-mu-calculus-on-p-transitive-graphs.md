# The enriched μ-calculus over a single P-transitive relation is undecidable

Satisfiability of the modal μ-calculus with a nominal and counting and inverse counting modalities is undecidable over graphs whose single relation is P-transitive, and hence over 3-transitive graphs, although the plain μ-calculus is decidable there.

**P-transitive graphs.** A graph $G = (V, R, P, \overline{P}, \dots)$ has its vertices coloured by two complementary atoms $P$ and $\overline{P}$ (and possibly other atoms). $G$ is *$P$-transitive* if for all vertices $x, y$ such that $x$ reaches $y$ (by a path of one or more $R$-edges, so no loops are forced) and $x, y$ have the same colour, $xRy$; equivalently (Lemma 4.2 of the source), $xRy$ whenever $x, y$ have the same colour and are joined by a path of length 2 or 3. For $k \ge 1$, $G$ is *$k$-transitive* if whenever $x$ reaches $y$ in $k + 1$ steps it reaches $y$ in at most $k$ steps. Every transitive graph is $P$-transitive and every $P$-transitive graph is 3-transitive.

**Enriched μ-calculus.** The [modal μ-calculus](mu-formula.md) over one relation $R$, interpreted [in Kripke models](sat.md), is enriched with a nominal $N$ (an atom interpreted by a singleton), counting modalities $\langle\ \rangle^{>n}\varphi$ (more than $n$ successors satisfy $\varphi$) and $[\ ]^{\le n}\varphi$ (at most $n$ successors fail $\varphi$), and the corresponding inverse counting modalities over predecessors.

**Theorem (Lenzi).** The enriched μ-calculus over a single $P$-transitive relation is undecidable: no algorithm decides whether a given formula of the enriched μ-calculus is satisfied in some $P$-transitive graph (Theorem 5.1 of the source). Consequently the enriched μ-calculus over a single 3-transitive relation is undecidable (Corollary 5.1).

By contrast the plain μ-calculus is decidable on $P$-transitive graphs (Corollary 4.1 of the source), and, by a result of Bonatti, Lutz, Murano and Vardi that the source cites, the enriched μ-calculus with only the trivial counting bound $n = 0$ is decidable, which is why the counting modalities are needed.

## Depends on

- [Formulas of the modal μ-calculus](mu-formula.md)
- [Satisfaction in the modal μ-calculus](sat.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The tiling problem is undecidable](../../../TheoryOfComputation/undecidable-problems/wang-tiles/the-tiling-problem-is-undecidable.md)

## Expansion

Following Bonatti and Peron, a domino system $D$ is encoded by a formula $\psi_D$ such that $D$ tiles $\mathbb{N} \times \mathbb{N}$ if and only if $\psi_D$ is satisfied by a $P$-transitive graph. The horizontal and vertical successor relations of the grid are coded by the single relation $R$ together with four atoms, with the colours chosen so that the encoding is compatible with $P$-transitivity; the nominal marks the origin and the counting modalities control the number of successors and predecessors. Undecidability of the tiling problem for the quadrant transfers. The quadrant version of the tiling problem used here, tiling $\mathbb{N} \times \mathbb{N}$, is equivalent to the tiling problem for the plane by a compactness argument (a tile set tiles the quadrant iff it tiles arbitrarily large squares iff it tiles the plane); a good expansion links a page for that equivalence.

## Sources

- Giacomo Lenzi, "On P-transitive graphs and applications", in *Proceedings of the 2nd International Symposium on Games, Automata, Logics and Formal Verification (GandALF 2011)*, Electronic Proceedings in Theoretical Computer Science 54:222–236, 2011, doi:[10.4204/EPTCS.54.16](https://doi.org/10.4204/EPTCS.54.16). Numbering of the version read, arXiv:1106.1243v1: Theorem 5.1, Corollary 5.1, Corollary 4.1 and Sections 3 to 5.
