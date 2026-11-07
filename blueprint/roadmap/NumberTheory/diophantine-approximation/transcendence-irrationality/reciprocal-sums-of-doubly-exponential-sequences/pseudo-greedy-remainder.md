# Pseudo-greedy remainder sequence

For a real number $r$, the remainder sequence
$(x_n)_{n \ge 0}$ of the pseudo-greedy expansion of $r$ is defined by $x_0 = r$ and
$x_{n+1} = x_n - 1/a_n$, where $a_n = \lfloor x_n^{-1} + 1 + 1/2 \rfloor$ is the integer
nearest to $x_n^{-1} + 1$, with halves rounded up.

Here $0^{-1}$ and $1/0$ are read as $0$.

## Sources

- Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential Sequences*, INTEGERS 26 (2026), Article A28, Section 2 (definitions of the pseudo-greedy expansion and its remainder sequence).
