# Adjacency relation of the 3 by 3 grid

The adjacency relation of the $3 \times 3$ grid on $\{0, 1, \dots, 8\}$, as a Boolean-valued function: with $c_i = i \bmod 3$ and $r_i = \lfloor i/3 \rfloor$, it is true on $(i, j)$ when $c_i = c_j$ and $|r_i - r_j| = 1$, or $r_i = r_j$ and $|c_i - c_j| = 1$.
