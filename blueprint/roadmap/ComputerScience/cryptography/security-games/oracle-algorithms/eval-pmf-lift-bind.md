# Randomized run of a query step

Let $O$ be a randomized oracle. The computation that asks the query $a$ and, on answer $b$,
continues with $k(b)$ runs against $O$ as follows: sample $b$ from $O(a)$, then run $k(b)$ against
$O$.
