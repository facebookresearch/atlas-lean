# The ∃∀-theory of finite bipartite graphs is hereditarily undecidable

The set of $\Sigma_2$ sentences, of the form $\exists\forall$, true in all finite bipartite graphs is hereditarily undecidable; already for some finite relational language the $\Sigma_2$ sentences true in all finite structures form a hereditarily undecidable set.

**Bipartite graphs.** A bipartite graph is a structure in the language with unary predicates $\mathrm{Le}$, $\mathrm{Ri}$ and a binary predicate $E$ satisfying $\forall x\,(\mathrm{Le}\,x \leftrightarrow \neg\mathrm{Ri}\,x)$ and $\forall x\,\forall y\,(E\,xy \to \mathrm{Le}\,x \wedge \mathrm{Ri}\,y)$; F-BiGraphs is the class of finite bipartite graphs.

**Theorem (Nies).** In the sense of [hereditarily undecidable theories](interpretability-and-hereditary-undecidability.md):

1. there is a finite relational language $L$ with equality such that the $\Sigma_2$ theory of the class of finite $L$-structures is hereditarily undecidable (Theorem 2.1);
2. $\Sigma_2\text{-}\mathrm{Th}(\text{F-BiGraphs})$ is hereditarily undecidable (Corollary 4.5).

## Depends on

- [Hereditarily undecidable theories of classes of structures](interpretability-and-hereditary-undecidability.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

Theorem 2.1 is proved by a direct coding of computations in finite $L$-structures; finite $L$-structures are then defined in finite undirected graphs by $\Sigma_1$ schemes (Theorem 4.2), and Corollary 4.5 follows by building the coding graph as a bipartite graph, which is possible because all cycles used have even length. A good expansion links the undecidable problem coded in Theorem 2.1.

## Sources

- A. Nies, "Undecidable fragments of elementary theories", *Algebra Universalis* 35(1):8–33, 1996, doi:10.1007/BF01190967; read in the author's open-access copy at <https://www.cs.auckland.ac.nz/~nies/papers/Fragments.pdf>: Section 2 (Theorem 2.1), the definition of bipartite graphs and Corollary 4.5 in Section 4.
