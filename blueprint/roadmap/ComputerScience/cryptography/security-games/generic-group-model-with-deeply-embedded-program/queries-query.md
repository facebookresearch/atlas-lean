# Query transcript of one query followed by a continuation

Let $L$ be a label type, $O : \mathrm{Query}(L) \to L$ an oracle, $x \in \mathrm{Query}(L)$ a query and $k$ a continuation from answers in $L$ to oracle computations with queries in $\mathrm{Query}(L)$, answers in $L$ and a label as result. The query transcript against $O$ of the computation that queries $x$ and continues with $k$ is $x$ followed by the transcript of $k(O(x))$.

This is the instance, at these types, of the general recurrence for [the queries of an oracle algorithm](../oracle-algorithms/queries.md).
