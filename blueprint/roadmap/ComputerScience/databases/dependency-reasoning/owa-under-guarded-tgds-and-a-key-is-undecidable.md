# Open-world query answering under guarded TGDs and one key is undecidable

There is a fixed Boolean conjunctive query and a fixed set of guarded tuple-generating dependencies together with a single key constraint for which deciding, given a database instance, whether the query holds in every model of the instance and the constraints is undecidable.

**Theorem.** There are a Boolean conjunctive query $q$ and a finite set $\Sigma$ consisting of guarded TGDs and a single key constraint such that the problem $\mathrm{OWA}_{q,\Sigma}$ is undecidable.

Here a *guarded TGD* is a sentence $\forall \bar x, \bar y\, (\phi(\bar x, \bar y) \to \exists \bar z\, \psi(\bar y, \bar z))$ with $\phi$, $\psi$ conjunctions of relational atoms whose body $\phi$ contains an atom (the guard) in which all body variables occur together; a *key constraint* is a sentence $\forall \bar x\, y\, z\, (F(\bar x, y) \land F(\bar x, z) \to y = z)$ for a relation symbol $F$. For a query $q$ and a set $\Sigma$ of constraints, $\mathrm{OWA}_{q,\Sigma}$ is the problem: given a finite instance $I$, decide whether $I, \Sigma \models_{\mathrm{OWA}} q$, that is, whether $q$ is true in every instance, finite or infinite, that contains all facts of $I$ and satisfies $\Sigma$ (equivalently, whether $I \cup \Sigma \cup \{\neg q\}$ is unsatisfiable, with the elements of $I$ read as constants). The query and the constraints are fixed; only $I$ is the input.

*Proof sketch.* Open-world answering relative to TGDs and equality-generating dependencies reduces to evaluating $q$ on the (possibly infinite) chase model of $I$ and $\Sigma$. The proof fixes a Turing machine $M$ and presents an input word as a successor chain of letter-labeled elements in $I$. Guarded TGDs alone produce only tree-like chase models; the key constraint identifies witnesses and so forces a grid onto which the guarded rules chart a computation of $M$ on the input word, row by row. The query $q = \exists x\, S_{acc}(x)$ detects the accepting state, so $I, \Sigma \models_{\mathrm{OWA}} q$ exactly when $M$ accepts the encoded word; choosing $M$ with an undecidable language makes $\mathrm{OWA}_{q,\Sigma}$ undecidable. The construction combines ideas of Grädel on guarded logics and of Calì, Gottlob and Kifer on guarded TGDs.

Without the key constraint the problem is in polynomial time for every conjunctive query and every set of guarded or frontier-guarded TGDs. The same source shows that there is a Boolean query with guarded negation (an SGNQ) and a single key constraint $\sigma$ with $\mathrm{OWA}_{q,\{\sigma\}}$ undecidable. Undecidability for the uniform problem, where the query is part of the input, was known for weaker formalisms; the point here is a fixed query.

## Depends on

- [Tuple- and equality-generating dependencies and the chase](../dependencies-and-the-chase/tuple-and-equality-generating-dependencies-and-the-chase.md)
- [Guarded and weakly guarded tgds](guarded-tgds/guarded-and-weakly-guarded-tgds.md)
- [Answers of a conjunctive query](../conjunctive-queries/answers-of-a-conjunctive-query.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Halting is undecidable](../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)


## Sources

- Vince Bárány, Balder ten Cate and Martin Otto, "Queries with guarded negation", *Proceedings of the VLDB Endowment* 5(11), 2012, pp. 1328–1339, <https://doi.org/10.14778/2350229.2350250>; read as the full version arXiv:1203.0077v1, <https://arxiv.org/abs/1203.0077v1>: item (i) of Theorem 7.8 in Section 7.2 ("Open-World Query Answering") and its proof in Appendix A.8, as numbered in that version.
