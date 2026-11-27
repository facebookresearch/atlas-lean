# The distinguisher built from a forger

For a list $L$ of messages in $M$ and a forger $c$,
an adaptive oracle algorithm with queries in $M$, answers in $T$ and output in $M \times T$, the
MAC reduction is the oracle algorithm with the same queries and answers and a Boolean output,
defined by recursion on $c$. If $c$ stops with output $(m, t)$, it queries $m$ and, on answer
$t'$, stops with output true exactly when $t' = t$ and $m \notin L$. If $c$ queries $x$ and
continues with $c_y$ on answer $y$, it queries $x$ and, on answer $y$, continues as the MAC
reduction of $c_y$ with $x$ added to $L$.

Started with the empty list, it runs the forger, logging its queries, then queries the forged
message and accepts when the answer is the forged tag and the message is fresh.
