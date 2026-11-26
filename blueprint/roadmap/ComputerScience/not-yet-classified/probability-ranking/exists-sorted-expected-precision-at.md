# Sorting by relevance marginal maximizes expected precision

Let $\mu$ be any real weight on relevance vectors for $N$ documents, let the marginal of document $i$ be $\sum_{\text{rel}} \mu(\text{rel})\,[\text{rel}_i]$, and let $k \le N$. There is a ranking of the documents in nonincreasing order of marginal whose first $k$ entries have expected precision at $k$ at least that of every injective list of $k$ documents.
