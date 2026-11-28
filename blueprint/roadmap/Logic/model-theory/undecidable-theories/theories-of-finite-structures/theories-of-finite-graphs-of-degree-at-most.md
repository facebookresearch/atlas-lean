# Theories of finite graphs of degree at most 3 and of finite sets with two permutations are hereditarily undecidable

The first-order theory of the class of finite graphs of vertex-degree at most 3, that of finite nonvoid sets with two distinguished permutations, and that of finite-dimensional vector spaces over a finite field with two distinguished endomorphisms are hereditarily undecidable.

**Classes.** For $k \geq 1$, $k\text{-}\mathcal{G}$ is the class of graphs of vertex-degree at most $k$; for $n \geq 2$, $n\text{-}\mathcal{P}$ is the class of nonvoid sets with $n$ distinguished permutations; for a finite field $K$, $\mathcal{M}^2_{K,\mathrm{end}}$ is the class of $K$-vector spaces with two distinguished endomorphisms. Hereditary undecidability is meant in Willard's interpretability sense ([hereditarily undecidable theories](interpretability-and-hereditary-undecidability.md)).

**Theorem (Willard).**

1. $\mathrm{Th}(3\text{-}\mathcal{G}_{\mathrm{fin}})$ and $\mathrm{Th}(2\text{-}\mathcal{P}_{\mathrm{fin}})$ are hereditarily undecidable (Theorem 2.3(1)).
2. For each finite field $K$, $\mathrm{Th}((\mathcal{M}^2_{K,\mathrm{end}})_{\mathrm{fin}})$ is hereditarily undecidable (Theorem 2.3(2)).
3. For all $k \geq 3$ and $n \geq 2$, $\mathrm{Th}(k\text{-}\mathcal{G}_{\mathrm{fin}})$, $\mathrm{Th}(3\text{-}\mathcal{G}_{\mathrm{fin}})$, $\mathrm{Th}(n\text{-}\mathcal{P}_{\mathrm{fin}})$ and $\mathrm{Th}(2\text{-}\mathcal{P}_{\mathrm{fin}})$ are mutually interpretable in the sense of $\leq$ (Theorem 2.1(2)), so all of them are hereditarily undecidable.

## Depends on

- [Hereditarily undecidable theories of classes of structures](interpretability-and-hereditary-undecidability.md)
- [Finite simple graph](../../../../GraphTheory/planar-graphs-and-minors/graph-minors/fin-graph.md)
- [Finite-dimensional vector space](../../../../LinearAlgebra/bases-and-dimension/bases-and-coordinates/dimension/finite-dimensional.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof uses a result of Gurevich and Lewis on the word problem for finite semigroups: the set of quasi-identities true in all semigroups and the set of quasi-identities refuted in some finite cancellation semigroup are recursively inseparable in a strong sense (Lemma 2.2 of the source). Quasi-identities $\psi$ in $n$ letters translate into sentences $\hat{\psi}$ about $n$ partial injective unary functions with a zero, true in all such structures iff $\psi$ is true in all semigroups and refuted in suitable finite structures otherwise; Theorem 2.1 transfers the result to graphs of bounded degree (via Vizing's theorem) and to permutations. A good expansion links the Gurevich–Lewis theorem.

## Sources

- R. Willard, "Hereditary undecidability of some theories of finite structures", *Journal of Symbolic Logic* 59(4):1254–1262, 1994, doi:10.2307/2275703; read in the author's open-access copy at <https://math.uwaterloo.ca/~rdwillar/documents/Publications/graphs.pdf>: the abstract, Section 1, Theorem 2.1, Lemma 2.2 and Theorem 2.3 with its proof.
