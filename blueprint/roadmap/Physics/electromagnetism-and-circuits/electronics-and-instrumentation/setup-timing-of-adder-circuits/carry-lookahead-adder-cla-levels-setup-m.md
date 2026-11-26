# Kogge–Stone setup certificate with $\lfloor\log_2 n\rfloor + 1$ levels

Let $n \ge 2$ and consider the $n$-bit Kogge–Stone carry-lookahead adder with
[$\lfloor \log_2 n \rfloor + 1$ levels](../../../../TheoryOfComputation/circuit-complexity/kogge-stone-adder/cla-levels.md),
enough for $n \le 2^{\lfloor \log_2 n \rfloor + 1}$, so that its outputs are the bits of the sum;
its [depth is $2 \lfloor \log_2 n \rfloor + 5$](../../../../TheoryOfComputation/circuit-complexity/kogge-stone-adder/carry-lookahead-adder-depth-cla-levels.md).
Let its gate delays $d_j$ satisfy $0 \le d_j \le D$, let its inputs arrive at times $a_i \le t_q$
with $t_q \ge 0$, and let $t_s, u, T$ be reals. If

$$t_q + D \bigl(2 \lfloor \log_2 n \rfloor + 5\bigr) + t_s + u \le T,$$

the [setup constraint](setup-met.md) holds. This is the
[certificate for $K$ levels](carry-lookahead-adder-setup-met.md) at
$K = \lfloor \log_2 n \rfloor + 1$.
