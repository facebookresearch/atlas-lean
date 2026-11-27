# Boolean quadtree lookup

The lookup of a cell $(i, j) \in \mathbb{N}^2$ at scale $n \in \mathbb{N}$ in a Boolean region
quadtree is defined recursively.

- A leaf $L(b)$ gives $b$, whatever the scale and the cell.
- A branch at scale $0$ gives false.
- A branch $Q(t_0, t_1, t_2, t_3)$ at scale $n + 1$ gives the lookup at scale $n$ of the cell
  $(i \bmod 2^n, j \bmod 2^n)$ in the child $t_0$ if $i < 2^n$ and $j < 2^n$, $t_1$ if $i < 2^n$
  and $j \ge 2^n$, $t_2$ if $i \ge 2^n$ and $j < 2^n$, and $t_3$ if $i \ge 2^n$ and $j \ge 2^n$.
