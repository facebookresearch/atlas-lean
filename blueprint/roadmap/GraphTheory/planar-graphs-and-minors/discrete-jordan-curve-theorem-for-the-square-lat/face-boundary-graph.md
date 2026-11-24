# Face-boundary graph of a set

For a set $S \subseteq \mathbb{Z}^2$, label each unit face of the square lattice by its lower left corner. The face-boundary graph of $S$ is the simple graph on $\mathbb{Z}^2$ in which faces $f$ and $g$ are adjacent when they are nearest neighbours and the primal edge separating them has exactly one endpoint in $S$; that edge is $\{(f_0, m), (f_0 + 1, m)\}$ with $m = \max(f_1, g_1)$ if $f_0 = g_0$, and $\{(m', f_1), (m', f_1 + 1)\}$ with $m' = \max(f_0, g_0)$ otherwise. Its edges are the dual edges crossing the boundary of $S$.
