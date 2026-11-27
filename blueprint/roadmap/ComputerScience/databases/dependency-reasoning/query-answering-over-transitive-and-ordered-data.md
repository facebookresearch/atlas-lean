# Query answering with transitive relations, transitive closure and linear orders

Open-world query answering asks whether a finite set of facts and first-order constraints entail a Boolean query over all, possibly infinite, extensions of the facts. Here some binary relations are distinguished and must be transitive, the transitive closure of a base relation, or a strict linear order.

**Signatures, facts and queries.** A relational signature $\sigma$ gives each relation an arity; a fact $R(\vec{a})$ is a relation with a tuple of elements of the right length, and an instance is a finite or infinite set of facts. Constraints and queries are first-order sentences without constants. A conjunctive query (CQ) is an existentially quantified conjunction of atoms, here always Boolean, and a union of conjunctive queries (UCQ) is a finite disjunction of CQs.

**Query answering.** For a finite set of facts $F_0$, constraints $\Sigma$ and a query $Q$, $F_0$ and $\Sigma$ entail $Q$ if every (possibly infinite) set of facts $F \supseteq F_0$ that satisfies $\Sigma$ satisfies $Q$; equivalently, $F_0 \wedge \Sigma \wedge \neg Q$ has no model, finite or infinite. The signature is split as $\sigma = \sigma_B \sqcup \sigma_D$ into base relations and distinguished relations, all distinguished relations being binary. The three variants restrict the sets $F$ considered:

- over transitive relations, written $\mathrm{QA}^{tr}(F_0, \Sigma, Q)$: each distinguished relation $R^+_i$ must be transitive in $F$ (not necessarily reflexive);
- over transitive closure, written $\mathrm{QA}^{tc}(F_0, \Sigma, Q)$: each distinguished relation $R^+_i$ must be the transitive closure in $F$ of a corresponding binary base relation $R_i \in \sigma_B$;
- over linear orders, written $\mathrm{QA}^{lin}(F_0, \Sigma, Q)$: each distinguished relation $<_i$ must be a strict linear order (transitive, irreflexive and total) on the elements of $F$.

## Depends on

- [Answers of a conjunctive query](../conjunctive-queries/answers-of-a-conjunctive-query.md)

## Proof depends on

None.

## Expansion

Transitivity itself, $R^+(x, y) \wedge R^+(y, z) \rightarrow R^+(x, z)$, is not frontier-guarded (a tuple-generating dependency is frontier-guarded if one body atom contains all variables shared by body and head, and base frontier-guarded if that atom is over a base relation), so these semantics are not expressible within the guarded constraint languages they are combined with. Query answering is decidable over transitive relations and over transitive closure for base frontier-guarded TGDs (more generally the base-guarded negation fragment) and UCQs, and over linear orders for base-covered constraints and base-covered UCQs (a CQ is base-covered if each of its $\sigma_D$-atoms has a $\sigma_B$-atom of the query containing all its variables); the guardedness and coverage conditions are what the undecidability results of the same source show to be needed.

## Sources

- Antoine Amarilli, Michael Benedikt, Pierre Bourhis and Michael Vanden Boom, "Query answering with transitive and linear-ordered data", in *Proceedings of the 25th International Joint Conference on Artificial Intelligence (IJCAI 2016)*, pp. 893–898, 2016; extended journal version in *Journal of Artificial Intelligence Research* 63, pp. 191–264, 2018, doi:[10.1613/jair.1.11240](https://doi.org/10.1613/jair.1.11240); read in arXiv:1607.00813v1 ([arXiv](https://arxiv.org/abs/1607.00813v1)), the conference article with its appendix, whose numbering is used: Section 2 (Preliminaries: problems considered, dependencies, guarded logics) of that version.
