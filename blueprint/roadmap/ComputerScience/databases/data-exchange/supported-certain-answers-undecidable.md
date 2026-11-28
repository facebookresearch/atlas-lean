# Supported certain answers in data exchange can be undecidable

For data exchange under the supported-solution semantics, which admits only target facts supported by the source and the dependencies, there is a fixed setting with only TGDs and a fixed first-order query whose supported certain answers are undecidable. For weakly acyclic settings the problem is coNP-complete.

**Setting (Calautti, Greco, Molinaro and Trubitsyna).** A *data exchange setting* $\mathcal{S} = \langle \mathbf{S}, \mathbf{T}, \Sigma_{st}, \Sigma_t \rangle$ has disjoint source and target schemas, a finite set $\Sigma_{st}$ of source-to-target TGDs (bodies over $\mathbf{S}$, heads over $\mathbf{T}$) and a finite set $\Sigma_t$ of target TGDs and EGDs over $\mathbf{T}$. Queries are [relational calculus queries](../relational-calculus/relational-calculus-and-domain-independence.md), first-order formulas evaluated under active-domain semantics; in the source (Section 2, footnote 1) quantifiers range over the terms of the given instance only, whereas the linked page's active domain also adds the constants of the formula. An *existential choice* $\gamma$ assigns, to every TGD $\rho$ and every tuple of constants for its frontier variables, a constant for each existential variable of $\rho$; $\Sigma^\gamma$ replaces every TGD by its ground versions coherent with $\gamma$. For a source database $I$, a target instance $J$ is a *supported solution* if for some $\gamma$, $I \cup J$ satisfies $\Sigma_{st}^\gamma$ and $J$ satisfies $\Sigma_t^\gamma$, and no proper subset of $J$ does so. The *supported certain answers* of a query $Q$ are $\mathrm{scert}(I, Q, \mathcal{S}) = \bigcap_{J} Q(J)$ over all supported solutions $J$ of $I$. For a fixed $\mathcal{S}$ and $Q$, the problem $\mathrm{SCert}(\mathcal{S}, Q)$ asks, given a source database $I$ and a tuple $\bar{t}$ of constants, whether $\bar{t} \in \mathrm{scert}(I, Q, \mathcal{S})$.

**Theorem (Calautti, Greco, Molinaro and Trubitsyna).** There exist a data exchange setting $\mathcal{S}$ whose target dependencies are only TGDs and a query $Q$ over its target schema such that $\mathrm{SCert}(\mathcal{S}, Q)$ is undecidable.

The same paper shows that the problem is in coNP for every weakly acyclic setting and coNP-hard for some, and that for positive queries supported and classical certain answers coincide.

## Depends on

- [Tuple- and equality-generating dependencies and the chase](../dependencies-and-the-chase/tuple-and-equality-generating-dependencies-and-the-chase.md)
- [Relational calculus and domain independence](../relational-calculus/relational-calculus-and-domain-independence.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The reduction is from the embedding problem for finite semigroups: given a finite set $A$ and a partial function $f : A \times A \to A$, is there a finite $B \supseteq A$ with a total associative $g : B \times B \to B$ extending $f$? This problem is undecidable (Kolaitis, Panttaja and Tan). The setting copies a ternary source relation $F$, the graph of $f$, into a target relation $G$, and one target TGD extends $G$ with new terms; the query, taken from the proof of Proposition 6.1 of Hernich, Libkin and Schweikardt ("Closed world data exchange", 2011), is true when $G$ fails to encode a total associative function. Then the empty tuple is not a supported certain answer on the instance encoding $(A, f)$ exactly when $(A, f)$ embeds into a finite semigroup.

A good expansion links pages for the undecidability of the embedding problem for finite semigroups (Kolaitis, Panttaja and Tan), and for the query of Hernich, Libkin and Schweikardt that detects when $G$ fails to encode a total associative function.

## Sources

- Marco Calautti, Sergio Greco, Cristian Molinaro and Irina Trubitsyna, "Querying Data Exchange Settings Beyond Positive Queries", Theory and Practice of Logic Programming 24(2), pp. 250–278, 2024, <https://doi.org/10.1017/S1471068423000339>; the definitions of Sections 2 and 3 (existential choices, supported solutions and supported certain answers), the problem $\mathrm{SCert}(\mathcal{S}, Q)$ and Theorem 6 (main statement) in Section 4, Theorems 7 and 8 (coNP membership for weakly acyclic settings and coNP-hardness), and Theorem 3 (positive queries) in Section 3 of arXiv:2307.03071v1, read at <https://arxiv.org/abs/2307.03071v1>.
