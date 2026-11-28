# The equational theory of finite modular lattices is undecidable in a bounded number of variables

There is a number N such that no algorithm decides, for lattice identities in at most N variables, whether they hold in every finite modular lattice.

**Theorem (Herrmann).** Let $n$ be the number of generator symbols in a finite group presentation for which the restricted word problem over finite groups is unsolvable (Slobodskoi). Then the set of lattice identities in $n + 6$ variables that are valid in all finite [modular lattices](../modular-lattice.md) is not recursive (Theorem 1.2 of the source).

The result adapts to every class of finite modular lattices that contains the particular lattices built in the proof from the finite groups of a class with unsolvable restricted word problem. For modular lattices in general, undecidability of the restricted word problem (with $5$ generators) and of the triviality problem goes back to Hutchinson and Lipshitz and holds for every class containing the subspace lattice of an infinite-dimensional vector space.

## Depends on

- [Modular lattice](../modular-lattice.md)
- [Group](../../../GroupTheory/group-basics/group.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof reduces Slobodskoi's theorem, that the restricted word problem for finite groups is unsolvable. Following Freese's technique, group presentations are captured within free modular lattices: towers of skew frames combine $n$ frames, one for each group generator; reductions of frames force group relations on elements that remain stable under reduction; and glueing constructions over lattices of submodules of free $(\mathbb Z/p\mathbb Z)G$-modules provide the finite models. Quasi-identities over such projective presentations are then reduced to identities in a bounded number of variables. A good expansion links Slobodskoi's theorem and each of these steps.

## Sources

- Christian Herrmann, "On the equational theory of finite modular lattices", *Order* 42(3), 2025, pp. 755–784, doi:[10.1007/s11083-025-09707-y](https://doi.org/10.1007/s11083-025-09707-y); read as arXiv:2406.04237v5, <https://arxiv.org/abs/2406.04237v5>, whose numbering is used: the abstract, Theorem 1.1 (Slobodskoi) and Theorem 1.2 in Section 1, the reduction of quasi-identities to identities in Subsection 2.4, and Section 8 ("Unsolvability").
