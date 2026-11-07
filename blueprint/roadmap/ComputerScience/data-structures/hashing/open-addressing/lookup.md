# Lookup in an open-addressing table

Let $T$ be an open-addressing hash table with $m$ slots
and probe sequence $p$, and let $k$ be a key. The lookup of $k$ in $T$ inspects the slots
$p(k, 0), p(k, 1), \dots, p(k, m - 1)$ in this order. It returns the value $v$ of the first
inspected slot that holds a pair $(k, v)$, and returns nothing if an empty slot is inspected
first or if none of the $m$ inspected slots holds the key $k$.
