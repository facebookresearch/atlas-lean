# Piece-wise linear sets of TGDs

A set of tuple-generating dependencies is piece-wise linear if every rule has at most one body atom whose predicate is mutually recursive with a predicate of its head. Certain answering of conjunctive queries under such sets is the reasoning task studied for them.

**Certain answers (Berger, Gottlob, Pieris and Sallinger).** Tuple-generating dependencies (TGDs) and their satisfaction are as in [tuple- and equality-generating dependencies](../dependencies-and-the-chase/tuple-and-equality-generating-dependencies-and-the-chase.md); here bodies and heads are conjunctions of atoms without constants and nulls. For a database $D$ (a finite set of facts) and a finite set $\Sigma$ of TGDs, a *model* is an instance $I \supseteq D$ satisfying every TGD of $\Sigma$, possibly infinite and possibly containing labeled nulls. The *certain answers* to a conjunctive query $q(\bar x)$ are

$$
\mathrm{cert}(q, D, \Sigma) = \bigcap \{ q(I) \mid I \text{ a model of } D \text{ and } \Sigma \}.
$$

For a class $\mathsf{C}$ of sets of TGDs, $\mathsf{CQAns}(\mathsf{C})$ is the problem: given $D$, $\Sigma \in \mathsf{C}$, a conjunctive query $q(\bar x)$ and a tuple $\bar c$ of constants of $D$, is $\bar c \in \mathrm{cert}(q, D, \Sigma)$? Its *data complexity* is its complexity when $\Sigma$ and $q$ are fixed and only $D$ and $\bar c$ vary.

**Piece-wise linearity.** The *predicate graph* of $\Sigma$ has the predicates of $\Sigma$ as vertices and an edge from $P$ to $R$ whenever some TGD of $\Sigma$ has $P$ in its body and $R$ in its head. Two predicates are *mutually recursive* if some cycle of the predicate graph contains both. $\Sigma$ is *piece-wise linear* if for each $\sigma \in \Sigma$ at most one atom of the body of $\sigma$ has a predicate that is mutually recursive with a predicate of the head of $\sigma$. $\mathsf{PWL}$ denotes the class of piece-wise linear sets of TGDs.

Piece-wise linear sets generalize intensionally linear sets, where each TGD has at most one body atom with an intensional predicate. Combined with *wardedness*, a syntactic restriction that confines the body variables that can be bound to nulls and propagated to the head to a single body atom (the ward), piece-wise linearity yields the logical core of the Vadalog system, for which $\mathsf{CQAns}$ is PSPACE-complete in combined complexity and NLOGSPACE-complete in data complexity.

## Depends on

- [Tuple- and equality-generating dependencies and the chase](../dependencies-and-the-chase/tuple-and-equality-generating-dependencies-and-the-chase.md)
- [Answers of a conjunctive query](../conjunctive-queries/answers-of-a-conjunctive-query.md)
- [Data, expression and combined complexity of query evaluation](../query-language-expressiveness/data-expression-and-combined-complexity-of-query-evaluation.md)

## Proof depends on

None.

## Expansion

The class transfers the piece-wise linear recursion of Datalog to rules with existentially quantified head variables. The source reports that about 70 percent of the TGD sets in its benchmarks and industrial scenarios use recursion only in this restricted way, which motivates combining it with wardedness.

## Sources

- Gerald Berger, Georg Gottlob, Andreas Pieris and Emanuel Sallinger, "The Space-Efficient Core of Vadalog", Proceedings of the 38th ACM SIGMOD-SIGACT-SIGAI Symposium on Principles of Database Systems (PODS 2019), pp. 270–284, 2019, <https://doi.org/10.1145/3294052.3319688>. Read in arXiv:1809.05951v1, <https://arxiv.org/abs/1809.05951v1>; Section 2 (preliminaries), Definition 3.1 (wardedness), Definition 4.1 (piece-wise linearity) and Theorem 4.2, numbering of arXiv:1809.05951v1.
- Gerald Berger, Georg Gottlob, Andreas Pieris and Emanuel Sallinger, "The Space-Efficient Core of Vadalog", ACM Transactions on Database Systems 47(1), pp. 1–46, 2022, <https://doi.org/10.1145/3488720> (journal version, not read).
