# Every sorting network on $n$ wires has depth at least $\log_2 n$

Let $C$ be a comparator
network on $n$ wires and $d$ a natural number. If $C$ sorts every Boolean input (its output is
monotone in the wire order for every input in $\{\mathrm{false}, \mathrm{true}\}^n$, with
$\mathrm{false} < \mathrm{true}$) and $C$ has depth at most $d$, then $n \le 2^d$.

By the 0-1 principle, the hypothesis implies that $C$ sorts every input over every linear order.
