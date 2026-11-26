# Emptiness of difference-bound matrices and octagons

With the notation of [difference-bound matrices and octagons](difference-bound-matrices-and-octagons.md):

1. For a DBM $m$, $D(m) = \emptyset$ if and only if the potential graph $G(m)$ has a cycle of strictly negative weight.
2. For a coherent DBM $m^+$ over a numerical set $\mathbb{I} \ne \mathbb{Z}$, $D(m^+) = \emptyset$ if and only if $D^+(m^+) = \emptyset$. So emptiness of an octagon is decided by searching $G(m^+)$ for a negative cycle, in time $O(N^3)$ with the Bellman–Ford algorithm.
3. Over $\mathbb{Z}$, $D(m^+) = \emptyset$ implies $D^+(m^+) = \emptyset$, but not conversely. For example, the constraints $v_1 - v_0 \le 0$, $v_0 + v_1 \le 3$ and $2 v_1 \ge 3$ have integer bounds in their encoding as a DBM over the four forms, whose potential graph has no cycle of strictly negative weight; but the only real solution is $v_0 = v_1 = 3/2$, so the octagon has no integer point.

## Depends on

- [Difference-bound matrices and octagons](difference-bound-matrices-and-octagons.md)

## Sources

- A. Miné, "The octagon abstract domain", arXiv:cs/0703084v2, 2007, <https://arxiv.org/abs/cs/0703084>: Section V.A, Theorem 2 (parts 1 and 3) and the use of the Bellman–Ford algorithm, with the counterexample of Figure 6.
