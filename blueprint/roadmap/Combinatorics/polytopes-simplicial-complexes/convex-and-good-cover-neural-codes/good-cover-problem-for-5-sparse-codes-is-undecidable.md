# Whether a 5-sparse neural code has a good cover is undecidable

No algorithm decides whether a neural code whose codewords have at most five neurons is locally good, equivalently whether it can be realized by a good cover; for codewords of at most three neurons the question is decidable.

**Theorem (Chen–Frick–Shiu).** There is no algorithm that decides, given a [$5$-sparse](sparse-neural-codes.md) [neural code](neural-codes-and-their-realizations.md) $\mathcal{C}$ (given by its number of neurons and the finite list of its codewords, each with at most $5$ neurons), whether $\mathcal{C}$ is [locally good](locally-good-codes.md), equivalently whether $\mathcal{C}$ is a [good-cover code](convex-and-good-cover-codes.md).

Codes, good covers, local goodness and sparsity are as in the linked definitions. For $3$-sparse codes the problem is decidable, since the relevant links are graphs and a graph is contractible exactly when it is a tree. For $4$-sparse codes the question is open, because it is not known whether contractibility of $3$-dimensional simplicial complexes is undecidable. Whether convexity of a code is decidable is left open in the source.

## Depends on

- [Neural codes and their realizations](neural-codes-and-their-realizations.md)
- [Convex and good-cover neural codes](convex-and-good-cover-codes.md)
- [Locally good neural codes](locally-good-codes.md)
- [Sparse neural codes](sparse-neural-codes.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof reduces from Tancer's theorem that no algorithm decides whether a given $4$-dimensional simplicial complex is contractible. Given such a complex $\Delta$, let $\Delta'$ be the cone over $\Delta$ on a new vertex $v$ and $\mathcal{C} = \Delta' \setminus \{\{v\}\}$, a $5$-sparse code with $\Delta(\mathcal{C}) = \Delta'$. The only face of $\Delta'$ missing from $\mathcal{C}$ is $\{v\}$, whose link is $\Delta$; by the criterion of Curto et al. ($\mathcal{C}$ is locally good exactly when it contains all mandatory codewords; Proposition 2.18 of the source), $\mathcal{C}$ is locally good exactly when $\Delta$ is contractible. The equivalence of local goodness with having a good cover is the source's Theorem 3.13.

A good expansion adds and links pages for Tancer's undecidability of contractibility of $4$-dimensional simplicial complexes, the mandatory-codeword criterion for local goodness, and the theorem that locally good codes are good-cover codes.

## Sources

- Aaron Chen, Florian Frick and Anne Shiu, *Neural codes, decidability, and a new local obstruction to convexity*, SIAM Journal on Applied Algebra and Geometry 3 (2019), no. 1, 44–66, https://doi.org/10.1137/18M1186563; read as arXiv:1803.11516v2: Theorem 4.3 with its proof, Lemma 4.2, Definition 2.8 (the cone) and Proposition 2.18, Proposition 4.4 (the $3$-sparse case), the remarks on $4$-sparse codes in Section 4.1, and Question 4.5.
- Martin Tancer, *Recognition of collapsible complexes is NP-complete*, Discrete & Computational Geometry 55 (2016), no. 1, 21–38, https://doi.org/10.1007/s00454-015-9747-1, for the undecidability of contractibility of $4$-dimensional complexes, as cited in the paper above.
