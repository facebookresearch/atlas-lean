# Automorphism groups of uncountable sofic shifts have finitely generated subgroups with undecidable torsion problem

For every uncountable sofic subshift $X \subseteq A^{\mathbb{Z}}$, the automorphism group of $X$ contains a finitely generated subgroup in which no algorithm decides whether a given element has finite order.

Let $A$ be a finite alphabet and $\sigma$ the shift on $A^{\mathbb{Z}}$. A subshift $X \subseteq A^{\mathbb{Z}}$ is a closed $\sigma$-invariant subset; it is sofic if it is the image of a subshift of finite type under a continuous map commuting with the shifts. The automorphism group $\mathrm{Aut}(X)$ is the group of homeomorphisms $X \to X$ commuting with $\sigma$ (the reversible cellular automata on $X$). If $X$ is an uncountable sofic $\mathbb{Z}$-subshift, there is a finitely generated subgroup $G \le \mathrm{Aut}(X)$ whose torsion problem is undecidable: no algorithm decides, for a word over a finite generating set of $G$, whether it represents an element of finite order (Corollary 1.3 of the source).

## Depends on

- [Order problem and torsion problem of a finitely generated group](order-problem.md)
- [Group](../../../group-basics/group.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Full shift space](../../../../Dynamics/topological-symbolic-dynamics/full-shift-and-cellular-automata/full-shift-space.md)

## Proof depends on

None.

## Expansion

The source shows that the finitely generated group of elementary reversible Turing machines with $n \ge 2$ symbols, $k \ge 1$ states and dimension $d \ge 1$ has undecidable torsion problem (Theorem 1.2), by simulating the complete reversible Turing machines of Kari and Ollinger, whose periodicity is undecidable, with elementary machines on a fixed alphabet. A computable map from this group to $\mathrm{Aut}(A^{\mathbb{Z}})$ that preserves finiteness of orders, though not a homomorphism, sends the generators into a finitely generated subgroup that inherits undecidable torsion problem (Lemmas 4.7 and 4.8), which gives a finitely generated subgroup of $\mathrm{Aut}(A^{\mathbb{Z}})$ with undecidable torsion problem for some alphabet $A$ with at least two symbols (Corollary 4.10). By a lemma of Salo, $\mathrm{Aut}(A^{\mathbb{Z}})$ embeds in $\mathrm{Aut}(X)$ for every finite set $A$ and every uncountable sofic subshift $X$, which gives the corollary.

## Sources

- S. Barbieri, J. Kari and V. Salo, "The group of reversible Turing machines: subgroups, generators, and computability", Forum of Mathematics, Sigma 13 (2025), article e176, https://doi.org/10.1017/fms.2025.10118 (corrigendum: article e186, https://doi.org/10.1017/fms.2025.10142); read in arXiv:2303.17270v1 (Theorem 1.2, Corollary 1.3, Lemmas 4.7 and 4.8 and Corollary 4.10 of arXiv:2303.17270v1).
