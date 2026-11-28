# The ∀∃∀-theory of finite distributive lattices is hereditarily undecidable

The set of $\Pi_3$ sentences, of the form $\forall\exists\forall$, true in all finite distributive lattices is hereditarily undecidable, and so is the set of $\Sigma_3$ sentences true in them.

**Theorem (Nies).** Let F-DistrLattices be the class of finite distributive lattices, viewed as structures in the language of partial orders. Then, in the sense of [hereditarily undecidable theories](interpretability-and-hereditary-undecidability.md):

1. $\Sigma_3\text{-}\mathrm{Th}(\text{F-DistrLattices})$ is hereditarily undecidable (Corollary 4.4);
2. $\Pi_3\text{-}\mathrm{Th}(\text{F-DistrLattices})$ is hereditarily undecidable (Theorem 4.8).

In particular both fragments are undecidable. According to the source, $\Pi_2\text{-}\mathrm{Th}$ of finite distributive lattices in the lattice language is decidable, and whether $\Sigma_2\text{-}\mathrm{Th}(\text{F-DistrLattices})$ is undecidable is left open.

## Depends on

- [Hereditarily undecidable theories of classes of structures](interpretability-and-hereditary-undecidability.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The ∃∀-theory of finite nice bipartite graphs is hereditarily undecidable](sigma-2-theory-of-restricted-finite-bipartite.md)

## Expansion

Clause 1 combines a $\Sigma_2$ definition of finite partial orders in finite distributive lattices (Proposition 4.1) with Schmerl's hereditary undecidability of $\Sigma_2\text{-}\mathrm{Th}$ of finite lattices and partial orders (Theorem 4.3), through the Transfer Lemma. Clause 2 defines the class of finite bipartite graphs with at least three vertices on each side, every vertex of degree at least two and complement without isolated vertices in finite distributive lattices by a $\Sigma_1$ scheme with parameters, and transfers the hereditary undecidability of its $\Sigma_2$ theory (Corollary 4.7). A good expansion links Schmerl's theorem and the Transfer Lemma.

## Sources

- A. Nies, "Undecidable fragments of elementary theories", *Algebra Universalis* 35(1):8–33, 1996, doi:10.1007/BF01190967; read in the author's open-access copy at <https://www.cs.auckland.ac.nz/~nies/papers/Fragments.pdf>: Section 1, the conventions before Section 2, Section 3 (the Transfer Lemma), Proposition 4.1, Theorem 4.3, Corollaries 4.4 and 4.7, Theorem 4.8 and Table 2.
