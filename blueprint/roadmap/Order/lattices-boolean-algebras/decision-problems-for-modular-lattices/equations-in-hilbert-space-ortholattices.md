# Satisfiability of an equation in finite-dimensional Hilbert space ortholattices is undecidable

No algorithm decides, for a term in five variables in the language of ortholattices, whether it takes the value 1 for some assignment in the lattice of subspaces of some nonzero finite-dimensional real, complex or quaternionic Hilbert space.

**Setting (Herrmann, Tsukamoto and Ziegler).** An *ortholattice* is a bounded lattice with a dual automorphism $x \mapsto x^\perp$ of order $2$ such that $x \vee x^\perp = 1$ and $x \wedge x^\perp = 0$. If $V$ is a finite-dimensional vector space over a division ring $F$ with involution, with an anisotropic hermitian form $\Phi$, then $U \mapsto U^\perp = \{v \in V : \Phi(v, u) = 0 \text{ for all } u \in U\}$ turns the [subspace lattice](submodule.md) $\mathrm L(V)$ into an ortholattice $\mathrm L^\perp(V)$.

**Theorem (Herrmann, Tsukamoto and Ziegler).** Let $\mathcal V$ be a class of such spaces whose underlying vector spaces consist of finite-dimensional spaces over division rings finite-dimensional over their centers and contain, for every $0 < d < \aleph_0$, a space of dimension $4d$ whose characteristic does not divide $d + 1$. There is no algorithm that, given a $5$-variable term $t(\bar x)$ in the language of ortholattices, decides whether $\exists \bar x\, t(\bar x) = 1$ holds in $\mathrm L^\perp(V)$ for some $V \in \mathcal V$ with $\dim V > 0$ (Corollary 25 of the source).

Examples of $\mathcal V$ are the classes of all finite-dimensional real, complex and quaternionic Hilbert spaces. This answers negatively the question of deciding "quantum satisfiability in indefinite (yet finite) dimension". For these Hilbert-space classes, in contrast, deciding whether $\exists \bar x\, t(\bar x) > 0$ holds in some $\mathrm L^\perp(V)$ ("weak satisfiability") is decidable, as the source notes, citing its reference [12].

## Depends on

- [Modular lattice](../modular-lattice.md)
- [Submodule](submodule.md)
- [Finite-dimensional vector space](../../../LinearAlgebra/bases-and-dimension/bases-and-coordinates/dimension/finite-dimensional.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The consistency problem for modular lattices is unsolvable](consistency-problem-for-modular-lattices.md)

## Expansion

By the five-variable form of the consistency theorem applied to the underlying subspace lattices, it is undecidable whether a conjunction of lattice equations in five variables has a non-trivial solution in some $\mathrm L(V)$, $V \in \mathcal V$. Since the bounded case of that theorem persists in every expansion, it applies to the ortholattices $\mathrm L^\perp(V)$, which expand the bounded lattices $\mathrm L(V)$ by the orthocomplement. Within modular ortholattices every conjunction of equations is equivalent to a single equation of the form $t = 1$ (Fact 26 of the source), which gives the stated form; a good expansion links this equivalence.

## Sources

- Christian Herrmann, Yasuyuki Tsukamoto and Martin Ziegler, "On the consistency problem for modular lattices and related structures", *International Journal of Algebra and Computation* 26(8), 2016, pp. 1573–1595, doi:[10.1142/S0218196716500697](https://doi.org/10.1142/S0218196716500697); read as arXiv:1607.03315v1, <https://arxiv.org/abs/1607.03315v1>, whose numbering is used: Section 8 ("Complemented modular lattices"), Corollary 24, Corollary 25 and Fact 26.
