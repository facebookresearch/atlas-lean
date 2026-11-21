# Fuel-based auxiliary merge of leftist heaps

Over a linear order, the auxiliary merge of two leftist heaps with a fuel $f \in \mathbb{N}$ is
defined recursively as follows.

- If the first heap is empty, the result is the second heap; otherwise, if the second heap is
  empty, the result is the first heap.
- If both heaps are nodes and the fuel is $0$, the result is the empty heap.
- For fuel $f + 1$ and nodes $h_1 = \langle k_1, x, \ell_1, r_1 \rangle$ and
  $h_2 = \langle k_2, y, \ell_2, r_2 \rangle$: if $x \le y$, the result is the node built (by the
  node constructor restoring the leftist property) from $x$, $\ell_1$ and the auxiliary merge with
  fuel $f$ of $r_1$ and $h_2$; otherwise it is the node built from $y$, $\ell_2$ and the auxiliary
  merge with fuel $f$ of $h_1$ and $r_2$.

Subheaps that are not merged keep their stored ranks.
