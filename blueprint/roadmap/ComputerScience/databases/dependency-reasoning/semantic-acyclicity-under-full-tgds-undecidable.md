# Semantic acyclicity under full tgds is undecidable

A conjunctive query is semantically acyclic under a set of tuple-generating dependencies if it is equivalent, over all instances satisfying the dependencies, to an acyclic conjunctive query. Deciding this is undecidable already for full tgds (no existential variables), for which containment of conjunctive queries is decidable.

**Setting (Barceló, Gottlob and Pieris).** A *tuple-generating dependency* (tgd) is a sentence $\forall \bar{x}\, \forall \bar{y}\, (\phi(\bar{x}, \bar{y}) \rightarrow \exists \bar{z}\, \psi(\bar{x}, \bar{z}))$ with conjunctions of relational atoms $\phi$ and $\psi$; it is *full* if $\bar{z}$ is empty. For a set $\Sigma$ of tgds, conjunctive queries $q, q'$ are *equivalent under $\Sigma$*, $q \equiv_\Sigma q'$, if $q(I) = q'(I)$ for every instance $I$, finite or infinite, that satisfies $\Sigma$. A conjunctive query is *acyclic* if the instance formed by its atoms (with variables replaced by fresh nulls) has a join tree. For a class $\mathcal{C}$ of sets of tgds, the problem $\mathrm{SA}(\mathcal{C})$ asks, given a conjunctive query $q$ and a finite set $\Sigma \in \mathcal{C}$, whether there is an acyclic conjunctive query $q'$ with $q \equiv_\Sigma q'$.

**Theorem (Barceló, Gottlob and Pieris).** $\mathrm{SA}(\mathsf{FULL})$, semantic acyclicity under finite sets of full tgds, is undecidable.

The reduction produces Boolean queries and full tgds over a fixed signature of five binary and two unary predicates. The same paper shows that $\mathrm{SA}(\mathcal{C})$ is undecidable for every class $\mathcal{C}$ with undecidable restricted containment, and decidable for guarded, non-recursive and sticky tgds: for guarded and non-recursive tgds with the same complexity as containment of conjunctive queries under them (2EXPTIME-complete, Theorem 11, and NEXPTIME-complete, Theorem 18), and for sticky tgds in NEXPTIME and EXPTIME-hard (Theorem 20), while containment under sticky tgds is EXPTIME-complete.

*Proof sketch.* The reduction is from the Post correspondence problem over $\{a, b\}$. For lists $w_1, \dots, w_n$ and $w'_1, \dots, w'_n$ it builds a Boolean conjunctive query $q$ and a set $\Sigma$ of full tgds over binary predicates $P_a, P_b, P_\#, P_\ast, \mathrm{sync}$ and unary predicates $\mathrm{start}, \mathrm{end}$. An acyclic query whose graph is a path encodes a word, and the tgds define $\mathrm{sync}$ on it: an initialization rule synchronizes the first letter position with itself, one rule per index $i$ propagates $\mathrm{sync}$ along $w_i$ and $w'_i$, and a finalization rule, applicable when both words of some index sequence end at the same position, creates a copy of the cyclic query $q$ in the chase. Hence $q$ is equivalent under $\Sigma$ to some acyclic query if and only if the instance has a solution.

## Depends on

- [Join tree](../join-processing/has-join-tree.md)
- [Answers of a conjunctive query](../conjunctive-queries/answers-of-a-conjunctive-query.md)
- [Tuple- and equality-generating dependencies and the chase](../dependencies-and-the-chase/tuple-and-equality-generating-dependencies-and-the-chase.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../../../TheoryOfComputation/undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)


## Sources

- Pablo Barceló, Georg Gottlob and Andreas Pieris, "Semantic Acyclicity Under Constraints", Proceedings of the 35th ACM SIGMOD-SIGACT-SIGAI Symposium on Principles of Database Systems (PODS 2016), pp. 343–354, 2016, <https://doi.org/10.1145/2902251.2902302>; the problem $\mathrm{SA}(\mathcal{C})$ (written $\mathrm{SemAc}(\mathcal{C})$ there), Corollary 6 (the reduction from restricted containment) and Theorem 7 (full tgds) in Section 3, "Semantic Acyclicity with TGDs", the decidability results of Section 4 (Theorem 11, guarded tgds) and Section 5 (Theorems 18 and 20, non-recursive and sticky tgds), Propositions 2 to 4 on containment, and the definitions of Section 2, "Preliminaries", of arXiv:1602.01366v2, read at <https://arxiv.org/abs/1602.01366v2>.
