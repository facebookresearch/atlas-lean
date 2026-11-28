# Satisfiability of non-recursive SHACL with sequence paths and equality is undecidable

For the shape constraint language of RDF validation, written as a fragment of first-order logic, satisfiability is undecidable even for documents without recursion that combine sequence paths with property-pair equality constraints. Several other combinations of path and constraint features are undecidable too, with a bounded number of binary relations.

**Setting (Pareti, Konstantinidis and Mogavero).** The *shape constraint logic* SCL is a first-order language over RDF terms (constants), unary *shape relations* $s$, unary *filter relations*, and binary relations $R$ (the properties of an RDF graph). Its sentences are conjunctions of *target axioms*, of the forms $s(c)$, $\forall x\,(\mathit{isA}(x, c) \to s(x))$ and $\forall x\, y\,(R^{\pm}(x, y) \to s(x))$, and *constraint axioms* $\forall x\,(s(x) \leftrightarrow \psi(x))$. In the base grammar, constraints $\psi(x)$ are built from $\top$, $x = c$, filter and shape atoms, negation, conjunction and $\exists y\,(\pi(x, y) \wedge \psi(y))$, where a *path* $\pi$ is a binary relation or its inverse. Further features, each named by a letter, extend the paths with sequence $\exists z\,(\pi(x, z) \wedge \pi(z, y))$ (S), zero-or-one $x = y \vee \pi(x, y)$ (Z), alternative $\pi \vee \pi$ (A) and transitive closure (T), and extend the constraints with property-pair disjointness (D), property-pair equality $\forall y\,(\pi(x, y) \leftrightarrow R(x, y))$ (E), property-pair order (O) and counting $\exists^{\ge n} y\,(\pi(x, y) \wedge \psi(y))$ (C). These correspond to the SHACL components of the same names, for example `sh:equals` for E and qualified value shapes for C. A sentence is *non-recursive* when no shape depends on itself through constraint axioms. *Sentence satisfiability* asks whether a sentence has a model; *formula satisfiability* asks whether a constraint formula $\psi(x)$ is satisfiable.

**Theorem (Pareti, Konstantinidis and Mogavero).**

1. Sentence satisfiability and formula satisfiability for the non-recursive SE fragment of SCL are undecidable.
2. Sentence satisfiability for the non-recursive SAC, SEC and SZAE fragments of SCL is undecidable already with $3$, $4$ and $8$ binary relations respectively.

By the correspondence between SCL and SHACL documents, the same holds for satisfiability of the corresponding SHACL fragments. The source also proves that the base grammar alone has an EXPTIME-complete satisfiability problem.

## Depends on

- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The tiling problem is undecidable](../../../../TheoryOfComputation/undecidable-problems/wang-tiles/the-tiling-problem-is-undecidable.md)

## Expansion

Clause 1 reduces from the subsumption problem for role-value maps in description logic, which Schmidt-Schauß proved undecidable by a reduction from the word problem for groups: equalities between compositions of roles become property-pair equality constraints along sequence paths. Clause 2 reduces from the domino problem on the quadrant $\mathbb{N} \times \mathbb{N}$: a sentence labels every element with exactly one tile, requires horizontal and vertical successors to carry matching tiles, and uses the stated features to force every model to contain the infinite grid, so it is satisfiable exactly when the tile set tiles the quadrant. A good expansion links a page for the undecidability of subsumption of role-value maps.

## Sources

- Paolo Pareti, George Konstantinidis and Fabio Mogavero, *Satisfiability and containment of recursive SHACL*, Journal of Web Semantics 74 (2022), article 100721, https://doi.org/10.1016/j.websem.2022.100721; the definition of SCL, the correspondence table of SHACL components and SCL expressions, and the two undecidability theorems for the S E fragment and the domino-based fragments in the section on SCL satisfiability, read in arXiv:2108.13063v2. Locators in arXiv:2108.13063v2: Theorems 14, 15 and 16.
