# HyperCTL* satisfiability is Σ²₁-complete

Whether a HyperCTL* sentence has a model, a transition system of arbitrary cardinality, is $\Sigma^2_1$-complete: as hard as existential third-order arithmetic, and outside the analytical hierarchy.

**Theorem (Fortin, Kuijer, Totzke and Zimmermann).** Fix a finite set $AP$ of atomic propositions. A *transition system* $\mathcal T = (V, E, v_I, \lambda)$ has a nonempty set $V$ of vertices of any cardinality, edges $E \subseteq V \times V$ such that every vertex has an outgoing edge, an initial vertex $v_I$ and a labelling $\lambda : V \to 2^{AP}$. [HyperCTL*](../hyperctl-star.md) sentences are evaluated on such systems with path quantifiers ranging over the infinite paths that start at the current vertex of the most recently quantified path (at $v_I$ for the first quantifier), every temporal operator lying in the scope of a path quantifier. The problem asking, given a HyperCTL* sentence $\varphi$ over $AP$, whether some transition system satisfies $\varphi$, is $\Sigma^2_1$-complete (Theorem 5.1 of the source).

Here $\Sigma^2_1$ is the class of sets $\{x \in \mathbb N \mid \exists F_0 \cdots \exists F_k\ \psi(x, F_0, \ldots, F_k)\}$, where the $F_i$ range over functions $(\mathbb N \to \mathbb N) \to \mathbb N$ and $\psi$ is a formula of arithmetic with arbitrary quantification over natural numbers and over functions $\mathbb N \to \mathbb N$. The model is not required to be finite, countable or finitely branching: restricted to finite systems the problem is $\Sigma^0_1$-complete (Proposition 5.8 of the source, attributed to Finkbeiner, Rabe and Sánchez and to Finkbeiner and Hahn), and restricted to countable or to finitely branching systems it is interreducible with truth in second-order arithmetic (Theorem 5.9).

## Depends on

- [HyperCTL*](../hyperctl-star.md)

## Proof depends on

None.

## Expansion

*Membership.* Every satisfiable HyperCTL* sentence has a model of cardinality at most that of the continuum (Lemma 5.2, a transfinite Skolem-function argument). A model of that size, together with Skolem functions witnessing satisfaction, can be coded by functions of type $(\mathbb N \to \mathbb N) \to \mathbb N$, and checking the quantifier-free part is second-order arithmetical, which places the problem in $\Sigma^2_1$ (Lemma 5.3).

*Hardness.* A satisfiable sentence $\varphi_c$ forces its models to contain pairwise disjoint paths realizing every trace over a fixed set of propositions, so every model has cardinality at least that of the continuum (Lemma 5.4); a HyperLTL sentence pins down an encoding of addition and multiplication (Lemma 5.5). On top of these, every sentence of existential third-order arithmetic is translated effectively into an equisatisfiable HyperCTL* sentence (Lemma 5.6), with sets of sets of numbers represented by sets of paths. Applying this to the sentences $\exists F_0\cdots\exists F_k\,\psi(n, F_0,\ldots,F_k)$ gives a computable map from $n$ to a sentence that is satisfiable iff $n$ belongs to the given $\Sigma^2_1$ set (Lemma 5.7).

This strengthens the $\Sigma^1_1$-hardness of [HyperCTL* satisfiability](../hyperctl-star-satisfiability-is-undecidable.md) shown by Clarkson, Finkbeiner, Koleini, Micinski, Rabe and Sánchez.

## Sources

- M. Fortin, L. B. Kuijer, P. Totzke and M. Zimmermann, "HyperLTL Satisfiability Is Highly Undecidable, HyperCTL* is Even Harder", *Logical Methods in Computer Science* 21(1), 2025, article 3, <https://doi.org/10.46298/lmcs-21(1:3)2025>; numbers from arXiv:2303.16699v5, <https://arxiv.org/abs/2303.16699v5>: Section 2 (transition systems and the semantics of HyperCTL*), Section 2.3 (the class $\Sigma^2_1$), Theorem 5.1 with Lemmas 5.2 to 5.7, Proposition 5.8 and Theorem 5.9.
