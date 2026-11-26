# Vector space model: tf-idf weighting and cosine ranking

This node collects the vector space model with tf-idf weights and cosine ranking.

## Expansion

A sound expansion has separate pages for:

1. **Weights.** Documents and queries are vectors indexed by the vocabulary. For a corpus of $N \ge 1$ documents
   and a term $t$ with document frequency $\mathrm{df}(t) \ge 1$, $\mathrm{idf}(t) = \log(N / \mathrm{df}(t))$, with
   the logarithm to a fixed base greater than $1$, and $w(t, d) = \mathrm{tf}(t, d) \cdot \mathrm{idf}(t)$ (variants
   such as sublinear tf stated separately); query terms that occur in no document are dropped or given a stated
   default weight.
2. **Cosine similarity** is the inner product divided by the product of norms, defined only when both vectors
   are nonzero; a stated convention (for example score $0$) covers zero vectors.
3. **Facts.** For nonzero vectors with nonnegative weights, cosine similarity lies in $[0,1]$; rankings are
   invariant under positive scaling of either vector and under strictly increasing transforms of the score;
   a term that occurs in every document has $\mathrm{idf} = 0$.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Document collections, vocabulary and Boolean retrieval semantics.

## Sources

- C. D. Manning, P. Raghavan and H. Schütze, *Introduction to Information Retrieval*, Cambridge University Press, 2008 (online edition, 2009), Section 6.2.1, Eq. (6.7) (inverse document frequency), Section 6.2.2, Eq. (6.8) (tf-idf weight), and Section 6.3.1, Eq. (6.10) (cosine similarity). <https://nlp.stanford.edu/IR-book/pdf/06vect.pdf>
