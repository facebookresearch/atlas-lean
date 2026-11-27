# Perfect simulation preserves the output distribution

Let $P$ and $Q$ be signatures, fix a sampling family, and let $h$ assign to each query $a$ of $P$ a computation $h(a)$ over $Q$ with sampling that returns an answer to $a$. Let $O$ be a randomized oracle for $P$ and $O'$ one for $Q$. Suppose that for each $a$, the output distribution of $h(a)$, with sampling answered by the family and queries answered by $O'$, is $O(a)$. Then for every computation $c$ over $P$ with sampling, the output distribution of its [simulation](simulate.md) by $h$, run with the family and $O'$, equals the output distribution of $c$ run with the family and $O$.

Only the output distribution is preserved. The statement says nothing about costs, query counts or transcripts.
