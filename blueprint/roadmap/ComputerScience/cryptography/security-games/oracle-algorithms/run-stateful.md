# Running against a stateful oracle

Let $s$ give, for each value $i$ of a query counter, an answer $s(i, x) \in Y$ to every query
$x \in X$. The run of an oracle computation against the stateful oracle $s$ from counter $i$ answers
the query asked when the counter is $i'$ by $s(i', x)$ and increments the counter after each query;
it returns the output and the transcript of (query, answer) pairs. This is how a stateful signer is
run in a forgery experiment (Katz and Lindell, Section 12.6).
