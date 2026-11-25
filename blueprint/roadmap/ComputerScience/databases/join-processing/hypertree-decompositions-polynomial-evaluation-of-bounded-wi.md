# Hypertree decompositions: polynomial evaluation of bounded-width CQs

This node collects evaluation of conjunctive queries given a hypertree decomposition of bounded width,
and the separate complexity results about hypertree width.

## Expansion

A sound expansion has separate pages for:

1. **Hypertree decompositions.** The four conditions of Gottlob, Leone and Scarcello (edge coverage,
   connectedness, $\chi \subseteq \mathrm{var}(\lambda)$, and the special descendant condition) and the
   width. A decomposition is complete when every atom $A$ lies in some $\lambda(p)$ with
   $\mathrm{var}(A) \subseteq \chi(p)$; every width-$k$ decomposition can be completed without increasing
   its width.
2. **Evaluation with a supplied decomposition.** For each fixed $k \ge 1$, given a safe conjunctive query,
   a database and a valid decomposition of width at most $k$, the answers can be computed in time polynomial
   in the sizes of the query, database, decomposition and output, by materializing a relation for each node
   (at most $M^k$ tuples, $M$ the largest relation, with encoding costs stated separately) and evaluating the
   resulting acyclic query.
3. **Normal form.** Every decomposition of width $k$ can be transformed into one in normal form of the
   same width $k$, and a normal-form decomposition has at most $\lvert \mathrm{var}(Q) \rvert + 1$ nodes. The
   bound $\lvert \mathrm{var}(Q) \rvert$ printed in the source needs the root's $\chi$-label to be nonempty: for
   $Q = a(X)$, a root with $\lambda = \chi = \emptyset$ above a node with $\lambda = \{a\}$ and $\chi = \{X\}$ is
   a normal-form decomposition with two nodes.
4. **Complexity results,** each a separate page, for each fixed $k$: Boolean evaluation with a supplied
   width-$k$ decomposition is LOGCFL-complete; deciding whether a query has hypertree width at most $k$
   is in LOGCFL; a width-$k$ decomposition in normal form, when one exists, is computed by an
   $\mathrm{L}^{\mathrm{LOGCFL}}$ transducer; and with no decomposition supplied, Boolean evaluation of
   queries of hypertree width at most $k$ is LOGCFL-complete and their answers are computed in time
   polynomial in the sizes of the input and the output.
5. Constants, repeated variables, nullary atoms and head projections as explicit extensions of the source's
   query class.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Conjunctive queries, answers and canonical databases.

## Depends on

- [Characterizations of acyclic database schemas](characterizations-of-acyclic-database-schemas.md)

## Proof depends on

- [Output-polynomial evaluation of projected acyclic CQs](output-polynomial-evaluation-of-projected-acyclic-cqs.md)
- [Yannakakis' algorithm for acyclic join queries](yannakakis-algorithm-for-acyclic-join-queries.md)

## Sources

- Hypertree Decompositions and Tractable Queries (Gottlob, Leone, Scarcello), arXiv cs/9812022v1 manuscript — Authors' arXiv manuscript cs/9812022v1, numbering of that version: Definition 4.1, Lemmas 4.3 and 4.5, Theorems 4.6 and 4.7, Definition 5.1, Theorem 5.4, Lemma 5.7, Theorems 5.15 and 5.17, Corollaries 5.18 and 5.19. <https://arxiv.org/pdf/cs/9812022>
