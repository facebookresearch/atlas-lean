# Sorting comparator lists on $n$ wires have depth at least $\log_2 n$

Let $ps$ be a list
of comparators on wires indexed by $\mathbb{N}$, all of whose wires lie in $[0, n)$, and let $d$
be a natural number. Suppose that for every Boolean input $v$ on the wires $0, \dots, n - 1$,
extended by $\mathrm{false}$ to the wires $\ge n$, the output $w$ of $ps$ satisfies
$w_i \le w_j$ whenever $i \le j < n$ (with $\mathrm{false} < \mathrm{true}$). If $ps$ has depth at
most $d$, then $n \le 2^d$.

The smallest output depends on every input, and a wire at level $d$ depends on at most $2^d$
inputs.
