# Positional indexes and phrase/proximity queries

Let the positional index store, for each term, its postings as pairs $(d, P_d)$ with $P_d$ the sorted list of
positions of the term in document $d$, ordered by $d$. A document $d$ matches the phrase query
$t_1 t_2 \cdots t_k$ if there is a position $p$ such that $t_i$ occurs at position $p + i - 1$ for every $i$
(repeated terms included), and matches the proximity query $t_1 \mathbin{/m} t_2$, for a fixed $m \ge 1$, if
some occurrence of $t_1$ and some occurrence of $t_2$ are at distance at most $m$. For the phrase
query, merging the document lists and, in each common document, intersecting the position lists of the
$t_i$ shifted by $i - 1$ returns exactly the matching documents in time
$O(\sum_i \lvert \text{postings}(t_i) \rvert)$, where postings length counts positions and a repeated term
counts once per occurrence in the query. For the proximity query, the two-list positional merge returns
exactly the matching documents in time linear in the two postings lengths, and returning all pairs of
matching occurrences adds the number of such pairs. The time bounds are elementary merge arguments.

## Expansion

This node states a precise result.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Inverted index and postings-merge correctness.

## Sources

- Introduction to Information Retrieval (Manning, Raghavan, Schutze) — Cambridge University Press 2008; authors' online edition, Section 2.4.2 (positional indexes and phrase queries) and Figure 2.12 (positional intersection for proximity queries), pp. 41–43. <https://nlp.stanford.edu/IR-book/pdf/irbookonlinereading.pdf>
