# Parallel composition of comparator lists on adjacent blocks

Let $a$, $m$, $b$, $d$ be
natural numbers, and let $p$ and $q$ be lists of comparators on wires indexed by $\mathbb{N}$, where
every comparator of $p$ joins two wires in $[a, m)$ and every comparator of $q$ joins two wires in
$[m, b)$. If $p$ and $q$ both have depth at most $d$, then the concatenation of $p$ followed by
$q$ also has depth at most $d$: the two lists run in parallel.
