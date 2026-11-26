# Restricting a finite Markov kernel along an increasing reindexing

Let $(K_t)_{t \ge 0}$ be Markov kernels on a measurable space $E$ satisfying the Chapman–Kolmogorov
equations, let $t_0 < t_1 < \dots < t_{n-1}$ be times with $s \le t_i$ for every $i$, and let
$e : \{0, \dots, m-1\} \to \{0, \dots, n-1\}$ be strictly increasing. Then for every $x \in E$ the
image of the [finite-dimensional kernel](finite-chain-kernel.md) $F_{s, (t_0, \dots, t_{n-1})}(x, \cdot)$
under $(z_0, \dots, z_{n-1}) \mapsto (z_{e(0)}, \dots, z_{e(m-1)})$ is
$F_{s, (t_{e(0)}, \dots, t_{e(m-1)})}(x, \cdot)$.
