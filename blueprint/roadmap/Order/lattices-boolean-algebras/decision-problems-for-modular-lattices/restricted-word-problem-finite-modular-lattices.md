# The restricted word problem is unsolvable for finite modular lattices with subspace lattices of unbounded dimension

For any class of finite modular lattices containing subspace lattices of arbitrarily large finite dimension, there is a finite lattice presentation for which no algorithm decides which relations it implies in the class.

**Setting (Herrmann).** A finite *presentation* $(\Pi, \bar c)$ consists of generator symbols $\bar c = (c_1, \ldots, c_n)$ and finitely many relations $t(\bar c) = s(\bar c)$ between lattice terms. A *model* of $\Pi$ in a lattice $A$ is a tuple $\bar a$ in $A$ satisfying all relations of $\Pi$. For a class $\mathcal C$ of lattices, a relation $\rho(\bar c)$ is a *consequence* of $\Pi$ in $\mathcal C$ if every model of $\Pi$ in a member of $\mathcal C$ satisfies $\rho$. The *restricted word problem* for $\mathcal C$ is *unsolvable* if there is a finite presentation $\Pi$ such that no algorithm decides, for every relation $\rho(\bar c)$, whether $\rho$ is a consequence of $\Pi$ in $\mathcal C$.

**Theorem (Herrmann).** Let $\mathcal C$ be a class of finite [modular lattices](modular-lattices-and-subspace-lattices.md) such that for every $d \in \mathbb N$ some [subspace lattice](modular-lattices-and-subspace-lattices.md) $\mathrm L(V_d)$ of a vector space $V_d$ over a division ring $F_d$ with $\dim V_d \ge d$ belongs to $\mathcal C$. Then the restricted word problem for $\mathcal C$ is unsolvable (Corollary 9.1 of the source).

The number of generators of the presentation can be reduced to $5$. In particular this holds for the class of all finite modular lattices and for the class of all subspace lattices of finite vector spaces.

## Depends on

- [Modular lattices and lattices of subspaces](modular-lattices-and-subspace-lattices.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof reduces Slobodskoi's theorem, that the restricted word problem for finite groups is unsolvable, which has no page here. A group presentation is translated into a lattice presentation by adding a $4$-frame and one lattice generator for each group generator, and turning each group relation into a lattice relation via von Neumann's coordinate ring of the frame, whose units form a group. If a word is a consequence of the group presentation in finite groups, its translation is a consequence of the lattice presentation in finite modular lattices; if some finite group $G$ refutes it, the lattice of submodules of $R^4$ with $R = F[G]$ gives a finite model refuting the translation, and it embeds into the subspace lattice of a vector space of dimension $4|G|$ over $F$. The reduction to $5$ generators uses an equivalent four-generator presentation of frames.

## Sources

- Christian Herrmann, "On the equational theory of finite modular lattices", *Order* 42(3), 2025, pp. 755–784, doi:[10.1007/s11083-025-09707-y](https://doi.org/10.1007/s11083-025-09707-y); read as arXiv:2406.04237v5, <https://arxiv.org/abs/2406.04237v5>, whose numbering is used: Theorem 1.1 in Section 1, the definitions of presentations, consequences and the restricted word problem in Subsection 2.1, and Corollary 9.1 with the reduction preceding it in Section 9 ("Remarks").
