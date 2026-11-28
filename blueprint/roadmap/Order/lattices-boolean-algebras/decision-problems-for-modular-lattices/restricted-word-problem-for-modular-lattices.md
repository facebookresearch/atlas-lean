# The restricted word problem and the triviality problem for modular lattices are unsolvable

There is a finite lattice presentation for which no algorithm decides which relations it implies in all modular lattices, and no algorithm decides whether a finite presentation forces a trivial model; five generators suffice.

Let $\mathcal{C}$ be a class of lattices. A finite *presentation* $(\Pi, \bar c)$ consists of generator symbols $\bar c = (c_1, \dots, c_n)$ and finitely many relations $t(\bar c) = s(\bar c)$ between lattice terms. A *model* of $\Pi$ in a lattice $A$ is a tuple $\bar a$ in $A$ satisfying all relations of $\Pi$, and a relation $\rho(\bar c)$ is a *consequence* of $\Pi$ in $\mathcal{C}$ if every model of $\Pi$ in a member of $\mathcal{C}$ satisfies $\rho$. The *restricted word problem* for $\mathcal{C}$ is *unsolvable* if there is one finite presentation $\Pi$ such that no algorithm decides, for every relation $\rho(\bar c)$, whether $\rho$ is a consequence of $\Pi$ in $\mathcal{C}$. The *triviality problem* for $\mathcal{C}$ asks, given a finite conjunction of equations, whether every assignment satisfying it within $\mathcal{C}$ generates a one-element sublattice, that is, whether all its models in members of $\mathcal{C}$ are trivial (all generators equal); it is the complement of the consistency problem, as defined by Herrmann, Tsukamoto and Ziegler (Section 1 of the source cited below).

**Theorem (Hutchinson; Lipshitz).** Let $\mathcal{C}$ be a class of [modular lattices](../modular-lattice.md) that contains the subspace lattice of some infinite-dimensional vector space; for example, the class of all modular lattices. Then:

1. the restricted word problem for $\mathcal{C}$ is unsolvable, already for a presentation with $5$ generators;
2. the triviality problem for $\mathcal{C}$ is unsolvable.

Equivalently, for $\mathcal{C}$ the class of all modular lattices, there is a finitely presented modular lattice with unsolvable word problem. For classes of finite modular lattices the restricted word problem is a separate question, answered by Herrmann through Slobodskoi's theorem on finite groups; and the word problem for the free modular lattice on five generators, a uniform question about all presentations without relations, is Freese's theorem.

## Depends on

- [Modular lattice](../modular-lattice.md)
- [Submodule](submodule.md)
- [Finite-dimensional vector space](../../../LinearAlgebra/bases-and-dimension/bases-and-coordinates/dimension/finite-dimensional.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Novikov–Boone theorem (unsolvability of the word problem)](../../../GroupTheory/presentations-and-decision-problems/word-problem-for-groups/novikov-unsolvable.md)

## Expansion

The reduction uses von Neumann's coordinate rings of frames. To a finite group presentation $(\Pi, \bar g)$ one adds to a $4$-frame $\Phi$ one generator for each $g_i$, the relations that make it a unit of the coordinate ring $R(\Phi)$, and the relations $w_i(\bar g) = c_{13}$ for the group relations $w_i = e$, with $c_{13}$ the unit of $R(\Phi)$. If $w = e$ follows from $\Pi$ in all groups, then $w(\bar g) = c_{13}$ follows in all modular lattices, since the units of $R(\Phi, L)$ form a group. Conversely, a group $G$ with $w(\bar h) \ne e$ gives a model inside the subspace lattice of a vector space of dimension $4|G|$ over a field, through the lattice of submodules of $F[G]^4$; for infinite $G$ this vector space is infinite-dimensional. A finitely presented group with unsolvable word problem then gives a lattice presentation with unsolvable restricted word problem, and frames have equivalent presentations with $4$ generators, which brings the count down to $5$.

A good expansion adds and links pages for von Neumann's coordinatization of frames in modular lattices, the reduction of $n$-frames to equivalent presentations with $4$ generators, and the reduction behind the triviality problem; the finitely presented group with unsolvable word problem is the linked Novikov–Boone theorem.

## Sources

- George A. Hutchinson, *Recursively unsolvable word problems of modular lattices and diagram-chasing*, Journal of Algebra 26 (1973), no. 3, 385–399, https://doi.org/10.1016/0021-8693(73)90001-X, and Leonard Lipshitz, *The undecidability of the word problems for projective geometries and modular lattices*, Transactions of the American Mathematical Society 193 (1974), 171–180, https://doi.org/10.1090/S0002-9947-1974-0364040-2, the original sources, cited beside the papers read below.
- Christian Herrmann, *On the equational theory of finite modular lattices*, Order 42 (2025), no. 3, 755–784, https://doi.org/10.1007/s11083-025-09707-y; read as arXiv:2406.04237v5: Section 1 states both clauses with the condition on infinite-dimensional subspace lattices, Subsection 2.1 defines presentations, consequences and the restricted word problem, and Section 9 gives the reduction and the reduction to $5$ generators.
- Christian Herrmann, Yasuyuki Tsukamoto and Martin Ziegler, "On the consistency problem for modular lattices and related structures", *International Journal of Algebra and Computation* 26(8), 2016, pp. 1573–1595, doi:[10.1142/S0218196716500697](https://doi.org/10.1142/S0218196716500697); read as arXiv:1607.03315v1, <https://arxiv.org/abs/1607.03315v1>: Section 1 (the consistency and triviality problems).
- Michael S. Roddy, *On the word problem for orthocomplemented modular lattices*, Canadian Journal of Mathematics 41 (1989), no. 6, 961–1004, https://doi.org/10.4153/CJM-1989-044-8; read in the open-access copy at https://www.cambridge.org/core/services/aop-cambridge-core/content/view/67589D2BC3EED1BE3F5310EC9F8416B9/S0008414X00002480a.pdf, Section 0.3, Example 4 (a finitely presented modular lattice with unsolvable word problem, by Hutchinson and Lipshitz).
