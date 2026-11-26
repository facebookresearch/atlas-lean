# Depth certificate for setup with gate delays between $0$ and $D$

Let $c$ be a circuit with gate delays $d_j$ and input arrival times $a_i$, and let
$\operatorname{depth}(c)$ be its depth: the largest depth of a designated output ($0$ if there is
none), where an input wire has depth $0$ and a gate has depth $1$ plus the largest depth, taken from
$0$, of the wires it reads, so that a constant gate has depth $1$. Let $t_q, D, t_s, u, T$ be reals.
If

- $0 \le d_j \le D$ for every gate $j$,
- $a_i \le t_q$ for every input $i$, with $t_q \ge 0$, and
- $t_q + D \operatorname{depth}(c) + t_s + u \le T$,

then the [setup constraint](setup-met.md) holds. Indeed every designated output arrives by
$t_q + D \operatorname{depth}(c)$ in the gate-delay model. In the timing reading $t_q$ is the
clock-to-Q bound of the launching register.
