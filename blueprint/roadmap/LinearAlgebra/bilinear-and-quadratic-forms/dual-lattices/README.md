# Dual lattices

Let $A$ be a Noetherian integral domain with fraction field $K$, let $V$ be a vector space over $K$, viewed as an $A$-module, and let $B$ be a nondegenerate bilinear form on $V$. An $A$-lattice in $V$ is a finitely generated $A$-submodule $M$ that spans $V$ over $K$, and its dual is $M^\vee = \{x \in V : B(x, y) \in A \text{ for all } y \in M\}$. The dual of an $A$-lattice is again an $A$-lattice.

## Idea

Lattices are the integral structures inside a vector space: $\mathbb{Z}^n$ inside $\mathbb{Q}^n$, or the ring of integers inside a number field. A bilinear form turns each lattice $M$ into a second one, its dual, made of the vectors that pair integrally with all of $M$. For the standard dot product on $\mathbb{Q}^n$ and $M = 2\mathbb{Z}^n$, the dual is $\tfrac12 \mathbb{Z}^n$. The proof has two halves: $M^\vee$ spans $V$ because, for each $x \in V$, the finitely many values $B(x, m_j)$ on generators $m_j$ of $M$ have a common denominator, and $M^\vee$ is finitely generated because it embeds in the dual module $\operatorname{Hom}_A(M, A)$ over a Noetherian ring. Under further hypotheses the pairing identifies $M^\vee$ with that dual module, and taking duals twice returns $M$. The inverse different of a number field is the dual of its ring of integers under the trace form.

## Statements

- [The dual of a lattice is a lattice](dual-submodule-is-lattice.md)
- [The dual of a lattice is finitely generated](dual-submodule-fg.md): one half of the proof
- [The dual of a finitely generated submodule spans](dual-submodule-span-eq-top.md): the other half of the proof
- [The dual lattice and the dual module](dual-submodule-is-lattice-and-dual-submo.md): a stronger form: the dual lattice is also the dual module
- [Bijectivity of the dual pairing](dual-submodule-to-dual-bijective.md): the pairing identifies the dual with the dual module
- [Surjectivity of the dual pairing](dual-submodule-to-dual-surjective.md): used to prove bijectivity
- [The dual submodule is the dual module](dual-submodule-linear-equiv.md): the identification as a linear isomorphism
- [A spanning submodule localizes to the whole space](is-localized-module-subtype-of-span-eq-t.md): a localization lemma used for surjectivity
- [Dual submodules commute with localization](dual-submodule-span-localization.md): duals commute with localization
- [Double dual of a reflexive lattice](dual-submodule-flip-dual-submodule-of-is.md): taking duals twice returns the lattice
- [Double dual of a lattice over a Dedekind domain](dual-submodule-dual-submodule-of-is-latt.md): double duality over a Dedekind domain, for a symmetric form
