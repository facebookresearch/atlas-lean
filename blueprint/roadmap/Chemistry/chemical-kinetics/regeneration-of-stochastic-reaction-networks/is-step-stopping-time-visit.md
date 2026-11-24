# Visit times are stopping times of the step sequence

Let $S$ be a set, $x_0, x \in S$ and $k \in \mathbb{N}$. The [$k$-th visit](visit.md)
$V_k(x_0, x, \cdot)$ to $x_0$, counting from $0$, of the jump chain started at $x$, a function from
step sequences to $\mathbb{N} \cup \{\infty\}$, is a
[stopping time of the step sequence](is-step-stopping-time.md): if $V_k(x_0, x, \omega) = n$ for a
natural number $n$ and $\omega'_i = \omega_i$ for all $i < n$, then $V_k(x_0, x, \omega') = n$.
