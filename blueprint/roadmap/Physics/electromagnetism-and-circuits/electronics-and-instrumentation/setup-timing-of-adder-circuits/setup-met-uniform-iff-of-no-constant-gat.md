# Exact setup certificate for uniform timing and no constant gates

Let $c$ be a circuit with at least one designated output in which every gate reads at least one
wire, so that no gate is a constant; the signature itself may offer constants. Give every gate the
same delay $D \ge 0$ and let every input arrive exactly at $t_q \ge 0$. Then for all reals $t_s$,
$u$ and $T$, the [setup constraint](setup-met.md) holds if and only if

$$t_q + D \operatorname{depth}(c) + t_s + u \le T,$$

where $\operatorname{depth}(c)$ is the largest depth of a designated output. Indeed each output
arrives exactly at $t_q$ plus $D$ times its depth, and some output has depth
$\operatorname{depth}(c)$. So under these premises the [depth certificate](setup-met-of-depth.md) is
exact: when it fails, setup fails.

The premises on the gates, the inputs and the outputs are needed. A constant gate arrives at its
delay alone while counting one level of depth. Inputs that only settle by $t_q$, some of them
earlier, can meet setup below the certificate: if every input arrives at $0$, setup holds exactly
when $D \operatorname{depth}(c) + t_s + u \le T$. A circuit without outputs meets setup for every
$T$.
