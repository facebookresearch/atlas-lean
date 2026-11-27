# Whether finitely many automorphisms of a full shift generate a given infinite abelian group is undecidable

For a suitable finite alphabet and any fixed infinite finitely generated abelian group $G$, no algorithm decides whether finitely many given reversible cellular automata on the full shift generate a group isomorphic to $G$.

Let $S$ be a finite alphabet and $\mathrm{Aut}(S^{\mathbb{Z}})$ the automorphism group of the full shift $S^{\mathbb{Z}}$, the reversible cellular automata, each given to an algorithm by a local rule $F\colon S^{2r+1} \to S$ with $f(x)_i = F(x_{[i-r,i+r]})$.

**Theorem.** Let $G$ be any infinite finitely generated abelian group, fixed. Then, given a finite set $F \subset \mathrm{Aut}(S^{\mathbb{Z}})$, it is undecidable whether $\langle F \rangle \cong G$ (Proposition 4 of the source). Here $S$ is an alphabet for which the torsion problem of $\mathrm{Aut}(S^{\mathbb{Z}})$ is undecidable; such an alphabet exists (Theorem 3 of the source).

By contrast, given a finite set $F \subset \mathrm{Aut}(S^{\mathbb{Z}})$, it is decidable whether $\langle F \rangle$ is isomorphic to a given finite group, and whether $\langle F \rangle$ is abelian (Propositions 2 and 3 of the source).

## Depends on

- [Automorphism group of the full shift](automorphism-group.md)
- [Full shift space](full-shift-space.md)
- [One-dimensional cellular automaton](is-one-dimensional-ca.md)
- [Abelian group](../../../GroupTheory/group-basics/abelian-group.md)

## Proof depends on

None.

## Expansion

For $|S| \ge 2$ the class of groups embeddable in $\mathrm{Aut}(S^{\mathbb{Z}})$ is closed under direct products (Theorem 1 of the source, for endomorphism monoids, and its corollary for automorphism groups): the actions of two automorphism groups are placed on alternating "conveyor belts" of a larger full shift and act independently. The source obtains the proposition by combining this closure property, the structure theorem for finitely generated abelian groups and the undecidability of the torsion problem of $\mathrm{Aut}(S^{\mathbb{Z}})$ for some alphabet $S$, a result of Kari quoted as Theorem 3; it states the reduction without detailed proof. Thus one can decide whether finitely many automorphisms generate an abelian group, but not which infinite abelian group they generate.

## Sources

- V. Salo, "A note on subgroups of automorphism groups of full shifts", Ergodic Theory and Dynamical Systems 38 (2018), no. 4, 1588–1600, https://doi.org/10.1017/etds.2016.95; read in arXiv:1507.00820v1 (Theorems 1 and 3 and Propositions 2, 3 and 4 of arXiv:1507.00820v1).
