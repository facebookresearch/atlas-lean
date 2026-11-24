# Exact setup certificate under uniform timing, constant-free signature

Let every operation of the signature take at least one argument, and let $c$ be a circuit over it
with at least one designated output. Give every gate the same delay $D \ge 0$ and let every input
arrive exactly at $t_q \ge 0$. Then for all reals $t_s$, $u$ and $T$, the
[setup constraint](setup-met.md) holds if and only if

$$t_q + D \operatorname{depth}(c) + t_s + u \le T,$$

where $\operatorname{depth}(c)$ is the largest depth of a designated output. Over such a signature
no gate is a constant, so this is a special case of the
[exact certificate for circuits without constant gates](setup-met-uniform-iff-of-no-constant-gat.md).
