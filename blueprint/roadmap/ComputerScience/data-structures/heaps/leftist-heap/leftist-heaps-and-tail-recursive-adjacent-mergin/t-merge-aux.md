# Fuel-based auxiliary cost of merging

Over a linear order, the auxiliary merge cost of two leftist heaps with a fuel $f \in \mathbb{N}$
is defined recursively as follows.

- If either heap is empty, the cost is $0$.
- If both heaps are nodes and the fuel is $0$, the cost is $0$.
- For fuel $f + 1$ and nodes $\langle k_1, x, \ell_1, r_1 \rangle$ and
  $\langle k_2, y, \ell_2, r_2 \rangle$: if $x \le y$, the cost is $1$ plus the auxiliary cost
  with fuel $f$ of $r_1$ and $\langle k_2, y, E, r_2 \rangle$; otherwise it is $1$ plus the
  auxiliary cost with fuel $f$ of $\langle k_1, x, E, r_1 \rangle$ and $r_2$.

Only merge steps are counted; the left subheaps play no role, so they are replaced by the empty
heap $E$.
