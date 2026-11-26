# Deleting one time from a finite Markov chain kernel

Let $(K_t)_{t \ge 0}$ be Markov kernels on a measurable space $E$ satisfying the Chapman–Kolmogorov
equations, and let $s \le t_0 < t_1 < \dots < t_n$ be times. For every $j \in \{0, \dots, n\}$, the
image of the [finite-dimensional kernel](finite-chain-kernel.md) $F_{s, (t_0, \dots, t_n)}(x, \cdot)$
under [removal of the $j$-th coordinate](erase-coordinate.md) is
$F_{s, (t_0, \dots, t_{j-1}, t_{j+1}, \dots, t_n)}(x, \cdot)$, for every $x \in E$: deleting one
requested time composes the two adjacent transition kernels.
