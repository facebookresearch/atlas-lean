# The ∃∀-theory of finite nice bipartite graphs is hereditarily undecidable

The set of $\Sigma_2$ sentences, of the form $\exists\forall$, true in all finite bipartite graphs with at least three vertices on each side, every vertex joined to at least two vertices and missing at least one vertex on the other side, is hereditarily undecidable.

**Nice bipartite graphs.** Bipartite graphs are structures $(\mathrm{Le}, \mathrm{Ri}, E)$ in the language with unary predicates $\mathrm{Le}$, $\mathrm{Ri}$ and a binary predicate $E$, satisfying $\forall x\,(\mathrm{Le}\,x \leftrightarrow \neg\mathrm{Ri}\,x)$ and $\forall x\,\forall y\,(E\,xy \to \mathrm{Le}\,x \wedge \mathrm{Ri}\,y)$. F-BiGraphs* (the source's name; "nice" is this page's name for its members) is the class of finite bipartite graphs with $|\mathrm{Le}| \ge 3$ and $|\mathrm{Ri}| \ge 3$ in which every vertex is joined by $E$ to at least two vertices and the complement graph $(\mathrm{Le}, \mathrm{Ri}, \mathrm{Le} \times \mathrm{Ri} \setminus E)$ has no isolated vertices.

**Theorem (Nies).** $\Sigma_2\text{-}\mathrm{Th}(\text{F-BiGraphs*})$ is hereditarily undecidable, in the sense of [hereditarily undecidable theories](interpretability-and-hereditary-undecidability.md) (Corollary 4.7 of the source).

Hereditary undecidability of the $\Sigma_2$ theory of all finite bipartite graphs does not by itself give this: the subclass has more true sentences. The source obtains the corollary from the proof of its Corollary 4.5, whose coding graphs lie in F-BiGraphs*. These graphs are the finite nice bipartite graphs that the reductions for finite distributive lattices and for free lattices start from.

## Depends on

- [Hereditarily undecidable theories of classes of structures](interpretability-and-hereditary-undecidability.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The ∃∀-theory of finite bipartite graphs is hereditarily undecidable](sigma-2-theory-of-finite-bipartite-graphs-is.md)

## Expansion

The proof of Corollary 4.5 codes computations in finite structures of a finite relational language (Theorem 2.1), defines these structures in finite graphs by $\Sigma_1$ schemes (Theorem 4.2), and builds the coding graph as a bipartite graph, possible because all cycles used have even length. Every vertex of that graph lies on a cycle of length at least $6$, so it has at least two neighbors and at least one non-neighbor on the other side, and the graph lies in F-BiGraphs*. A good expansion links the undecidable problem coded in Theorem 2.1 and the definability of finite structures in finite graphs (Theorem 4.2), and checks that the coding graphs lie in F-BiGraphs*.

## Sources

- A. Nies, "Undecidable fragments of elementary theories", *Algebra Universalis* 35(1):8–33, 1996, doi:10.1007/BF01190967; read in the author's open-access copy at <https://www.cs.auckland.ac.nz/~nies/papers/Fragments.pdf>: Theorem 2.1, Theorem 4.2, Corollary 4.5 and its proof, the definition of BiGraphs* and Corollary 4.7 in Section 4.
