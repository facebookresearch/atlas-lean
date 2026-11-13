# Parent writes are bounded by the rank gap

Let $S$ be a union-find structure, let $R$
be one more than the maximum rank of a node of $S$, and let $x < |S|$ be a node. The number of
parent writes performed by the cost-counted FIND auxiliary on $x$ (the second coordinate of its
cost) is at most $R - \operatorname{rank}(x)$.

This is a per-call bound, not a logarithmic or amortized inverse-Ackermann bound.
