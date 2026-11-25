# Top-k retrieval with additive scores; WAND safety

Let a finite collection of documents with distinct identifiers be scored by
$\mathrm{score}(d, q) = \sum_{t \in q \cap d} w(t, d)$ with $w \ge 0$, and fix $1 \le k$. The target output is the list of
the documents of positive score ranked by decreasing score, ties broken by increasing identifier, cut after its
first $k$ entries (all of them if fewer than $k$ documents have positive score). WAND visits candidate documents in
increasing identifier order, with per-term upper bounds $\mathrm{UB}_t \ge \max_d w(t, d)$ and a threshold $\theta$
that is $0$ while fewer than $k$ documents are held and is otherwise the score of the held $k$-th best document. It
fully evaluates a candidate only if the sum of upper bounds of the terms whose cursors are at or before it exceeds
$\theta$, and then holds it, displacing the held $k$-th best document when $k$ are held, if its score exceeds
$\theta$. Because candidates are visited in increasing identifier order, a later document whose score equals
$\theta$ ranks after the held $k$-th document, so the strict comparisons are the tie-aware rule. With this rule, WAND
returns exactly the target list, the same documents in the same order with the same scores as exhaustive
document-at-a-time evaluation, which is the reference.

## Expansion

This node states a precise result.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Inverted index and postings-merge correctness.

## Sources

- S. Ding and T. Suel, *Faster top-k document retrieval using block-max indexes*, SIGIR 2011, Section 2.6 and Figure 2: WAND (Broder, Carmel, Herscovici, Soffer and Zien, CIKM 2003) keeps the terms sorted by current document identifier, sums the per-list maximum scores until the threshold is reached to choose the pivot, takes as threshold the lowest score in the heap of the current top-k results, and is safe, returning the same top-k results in the same order and with the same scores as exhaustive evaluation. <https://research.engineering.nyu.edu/~suel/papers/bmw.pdf>
