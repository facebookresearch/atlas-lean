# Posterior decoding maximizes the expected number of correctly decoded states

**Posterior decoding maximizes the expected number of correctly decoded states**: let $g$ be a
hidden Markov model with states $\{0, \dots, n - 1\}$, $n \ge 1$, and weights in a linearly
ordered semifield $K$ in which addition preserves the order ($b \le c$ implies $a + b \le a + c$),
let $x_0, x_1, \dots$ be observations and $T \in \mathbb{N}$. For every state path
$z = (z_0, \dots, z_T)$, the [posterior expected number of correctly decoded states](expected-correct.md)
of $z$ is at most that of the [posterior decoding path](posterior-path.md).
