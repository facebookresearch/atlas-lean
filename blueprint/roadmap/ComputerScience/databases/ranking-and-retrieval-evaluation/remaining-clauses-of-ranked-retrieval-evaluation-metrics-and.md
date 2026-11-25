# Average precision and test collections

This node collects the ranked-retrieval evaluation notions beyond precision at $k$, recall at $k$, DCG at $k$ and
nDCG at $k$.

## Expansion

A sound expansion has separate pages for:

1. **Average precision** for a ranking of a finite candidate set with a nonempty set $R$ of relevant documents:
   $\mathrm{AP} = \frac{1}{|R|} \sum_{d \in R} \mathrm{Prec}(d)$, where $\mathrm{Prec}(d)$ is the precision of the
   ranking cut just after $d$, taken as $0$ when $d$ is not retrieved; a stated convention covers $R = \emptyset$.
   Mean average precision is its average over a finite set of information needs.
2. **Test collections:** a document collection, a set of information needs (topics) and relevance judgments for
   some topic-document pairs, with the treatment of unjudged documents stated explicitly (for example as
   nonrelevant when the judged documents are a pool of the top documents of several systems, one of several
   conventions).

## Sources

- C. D. Manning, P. Raghavan and H. Schütze, *Introduction to Information Retrieval*, Cambridge University Press, 2008 (online edition, 2009), Section 8.1 (test collections, p. 152), Section 8.4, Eq. (8.8) (average precision and mean average precision, p. 160) and Section 8.5 (pooling). <https://nlp.stanford.edu/IR-book/pdf/08eval.pdf>
- On the history of evaluation in IR (Robertson), Journal of Information Science 2008, author preprint — Journal of Information Science 34(4) 2008 (author preprint), Section 4 (TREC topics, relevance judgments and the pooling method). <https://staff.city.ac.uk/~sbrp622/papers/JIS_history_preprint.pdf>
