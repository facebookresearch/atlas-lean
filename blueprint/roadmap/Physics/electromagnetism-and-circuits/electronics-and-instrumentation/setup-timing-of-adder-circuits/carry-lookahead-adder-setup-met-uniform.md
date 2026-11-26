# Uniform Kogge–Stone setup certificate is exact, $K \ge 1$, $n \ge 2$

Let $n \ge 2$ and $K \ge 1$, give every gate of the $n$-bit
[Kogge–Stone carry-lookahead adder with $K$ levels](../../../../TheoryOfComputation/circuit-complexity/kogge-stone-adder/carry-lookahead-adder.md)
the same delay $D \ge 0$, and let all its $2n + 1$ inputs arrive exactly at $t_q \ge 0$. Then for
all reals $t_s$, $u$ and $T$, the [setup constraint](setup-met.md) holds if and only if

$$t_q + D (2K + 3) + t_s + u \le T.$$

So $T < t_q + D (2K + 3) + t_s + u$ is a setup violation of the model, whatever values the inputs
carry and whether or not $n \le 2^K$, a condition under which the circuit computes the sum. The
adder's gates are binary [XOR, AND and OR gates](../../../../TheoryOfComputation/circuit-complexity/ripple-carry-adder/arith-signature.md),
none of them a constant, and its [depth is $2K + 3$](../../../../TheoryOfComputation/circuit-complexity/kogge-stone-adder/carry-lookahead-adder-depth.md).
