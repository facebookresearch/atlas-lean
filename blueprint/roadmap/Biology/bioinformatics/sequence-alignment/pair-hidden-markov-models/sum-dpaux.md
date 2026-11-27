# Fuel-bounded sum recursion over alignments

For an [alignment automaton](alignment-automaton.md) with weights in a semiring, define $S_n(q, x, y)$ by

- $S_0(q, x, y) = 0$ and $S_{n+1}(q, \text{empty}, \text{empty}) = f(q)$;
- $S_{n+1}(q, \text{empty}, b y) = w(q, (-, b))\, S_n(\nu(q, (-, b)), \text{empty}, y)$ and $S_{n+1}(q, a x, \text{empty}) = w(q, (a, -))\, S_n(\nu(q, (a, -)), x, \text{empty})$;
- $S_{n+1}(q, a x, b y)$ is the sum of $w(q, (a, b))\, S_n(\nu(q, (a, b)), x, y)$, $w(q, (a, -))\, S_n(\nu(q, (a, -)), x, b y)$ and $w(q, (-, b))\, S_n(\nu(q, (-, b)), a x, y)$.
