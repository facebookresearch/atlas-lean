# Setup certificate of the Kogge–Stone adder for $K \ge 1$, $n \ge 2$

Let $n \ge 2$ and $K \ge 1$, and consider the $n$-bit
[Kogge–Stone carry-lookahead adder with $K$ levels](../../../../TheoryOfComputation/circuit-complexity/kogge-stone-adder/carry-lookahead-adder.md),
a circuit with $2n + 1$ inputs (the bits of the two summands and the carry-in) whose
[depth is $2K + 3$](../../../../TheoryOfComputation/circuit-complexity/kogge-stone-adder/carry-lookahead-adder-depth.md).
Let its gate delays $d_j$ satisfy $0 \le d_j \le D$, let its inputs arrive at times $a_i \le t_q$
with $t_q \ge 0$, and let $t_s, u, T$ be reals. If

$$t_q + D (2K + 3) + t_s + u \le T,$$

the [setup constraint](setup-met.md) holds. This is the [depth certificate](setup-met-of-depth.md)
at depth $2K + 3$; it holds for every $K \ge 1$, whether or not $n \le 2^K$, a condition under which
the circuit's outputs are the bits of the sum.
