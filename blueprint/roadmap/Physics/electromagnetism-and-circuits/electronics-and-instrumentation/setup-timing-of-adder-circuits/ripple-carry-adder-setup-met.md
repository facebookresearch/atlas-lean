# Setup certificate of the $n$-bit ripple-carry adder for $n \ge 1$

Let $n \ge 1$ and consider the $n$-bit [ripple-carry adder](../../../../TheoryOfComputation/circuit-complexity/ripple-carry-adder/ripple-carry-adder.md),
a circuit with $2n + 1$ inputs (the bits of the two summands and the carry-in) whose
[depth is $2n + 1$](../../../../TheoryOfComputation/circuit-complexity/kogge-stone-adder/ripple-carry-adder-depth.md).
Let its gate delays $d_j$ satisfy $0 \le d_j \le D$, let its inputs arrive at times $a_i \le t_q$
with $t_q \ge 0$, and let $t_s, u, T$ be reals. If

$$t_q + D (2n + 1) + t_s + u \le T,$$

the [setup constraint](setup-met.md) holds: every output of the adder settles at least $t_s + u$
before the capturing edge at $T$. This is the [depth certificate](setup-met-of-depth.md) at depth
$2n + 1$.
