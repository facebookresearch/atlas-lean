# Complete rewriting over views defined by unions of conjunctive queries is Π2p-complete

Let $Q$ be a union of conjunctive queries and let each view of $\mathcal V$ be a union of conjunctive queries over the
database relation names, without built-in comparison atoms. A complete rewriting of $Q$ using $\mathcal V$ is a union of
conjunctive queries over the view names alone whose expansion, obtained by replacing each view atom by the view's
definition and distributing conjunction over the resulting unions, is equivalent to $Q$; for $Q(x) = R(x) \vee S(x)$ and
the views $V_R(x) \mathrel{:-} R(x)$ and $V_S(x) \mathrel{:-} S(x)$ it is $V_R(x) \vee V_S(x)$, which no single conjunctive
query expresses. Deciding whether $Q$ has a complete rewriting using $\mathcal V$ is $\Pi_2^p$-complete, and it is
$\Pi_2^p$-hard already when $Q$ is a single conjunctive query. The expansion of one conjunctive query over union-valued
views can have exponentially many disjuncts: writing out the expansion can take exponential space, so the NP bound
for containment of two explicitly given unions does not give an NP upper bound in the original input size. The 1995 paper that introduced the problem stated NP-completeness; the later analysis corrected
this. When $Q$ and every view are conjunctive queries the problem is NP-complete,
by the [result for conjunctive views](finding-small-and-complete-rewritings-is-np-complete.md).

## Depends on

- [Rewritings of conjunctive queries using views](rewritings-of-conjunctive-queries-using-views.md)
- [Positive relational algebra = unions of conjunctive queries = positive existential calculus](../relational-calculus/positive-relational-algebra-unions-of-conjunctive-queries-po.md)
- [The universal levels of the polynomial hierarchy](../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/pi-k.md)
- [Finding small and complete rewritings of conjunctive queries is NP-complete](finding-small-and-complete-rewritings-is-np-complete.md)

## Proof depends on

- [CQ minimization (cores) and UCQ containment](../conjunctive-queries/cq-minimization-and-ucq-containment.md)
- [$\mathrm{QSAT}_k$ is $\Sigma_k^p$-complete, uniformly in $k$](../../../TheoryOfComputation/completeness-other-classes/quantified-boolean-formulas-with-bounded-alterna/qsat-k-sigma-k-complete.md)

## Sources

- C. Lutz, J. Marti and L. Sabellek, "Query expressibility and verification in ontology-based data access", *Proceedings of the 16th International Conference on Principles of Knowledge Representation and Reasoning (KR)*, 2018; theorem numbers as in arXiv:2011.09176 <https://arxiv.org/abs/2011.09176>: Theorem 10 (the $\Pi_2^p$ upper bound for expressing a union of conjunctive queries as one over views given by GAV mappings, that is, by unions of conjunctive queries), Theorem 11 (the $\Pi_2^p$ lower bound already for a conjunctive query and the empty ontology, by reduction from the validity of $\forall\exists$ quantified Boolean formulas) and the paragraph before Theorem 11, which corrects the NP-completeness statement of the 1995 paper.
- M. Benedikt, S. Kikot, P. Ostropolski-Nalewaja and M. Romero, "On monotonic determinacy and rewritability for recursive queries and views", *Proceedings of the 39th ACM PODS*, 2020, <https://www.cs.ox.ac.uk/standa.zivny/publications/Benedikt20pods.pdf>, Tables 1–2 (the columns for conjunctive and for union views) and Proposition 9.
- A. Y. Levy, A. O. Mendelzon, Y. Sagiv and D. Srivastava, "Answering queries using views", *Proceedings of the 14th ACM Symposium on Principles of Database Systems (PODS)*, 1995, pp. 95–104, Theorem 3.9 (p. 100), which states the problem; its NP-completeness claim is corrected by the first source.
