# Exact ripple-carry setup certificate under uniform timing, $n \ge 1$

Let $n \ge 1$, give every gate of the $n$-bit
[ripple-carry adder](../../../../TheoryOfComputation/circuit-complexity/ripple-carry-adder/ripple-carry-adder.md)
the same delay $D \ge 0$, and let all its $2n + 1$ inputs arrive exactly at $t_q \ge 0$. Then for
all reals $t_s$, $u$ and $T$, the [setup constraint](setup-met.md) holds if and only if

$$t_q + D (2n + 1) + t_s + u \le T.$$

So $T < t_q + D (2n + 1) + t_s + u$ is a setup violation of the model, whatever values the inputs
carry. The adder's gates are binary [XOR, AND and OR gates](../../../../TheoryOfComputation/circuit-complexity/ripple-carry-adder/arith-signature.md),
none of them a constant, and its [depth is $2n + 1$](../../../../TheoryOfComputation/circuit-complexity/kogge-stone-adder/ripple-carry-adder-depth.md).
