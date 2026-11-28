# Presampled answers are lazily sampled answers

Let $\alpha$ be a finite nonempty set and
$c$ an adaptive oracle algorithm with queries in $P$ and answers in $\alpha$ that makes at most
$q$ queries along every path, whatever the answers. Let $n + q \le Q$ and let $T$ be a table.
Running $c$ against the lazy table with a uniformly random tape of $Q$ answers, started at counter
$n$ with the table $T$, has the output distribution of running $c$ against the lazy random
function from $T$, which answers each fresh query with a fresh uniform value in $\alpha$.
