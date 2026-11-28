# Gap function and tangent residual for monotone variational inequalities

For a monotone operator $F$ on a compact convex set $\mathcal{Z}$ of diameter $D$, the gap function of a point $z \in \mathcal{Z}$ is $\mathrm{Gap}(z) = \max_{z' \in \mathcal{Z}} \langle F(z), z - z' \rangle \ge 0$, which is zero exactly at solutions; for a monotone game the sum of players' unilateral improvements $\sum_i \bigl(f_i(z) - \min_{x_i'} f_i(x_i', z_{-i})\bigr)$ is at most $\mathrm{Gap}(z)$. The tangent residual of $z$ is $r^{\tan}(z) = \min\{ \lVert F(z) + c \rVert : c \in N_{\mathcal{Z}}(z) \}$, where $N_{\mathcal{Z}}(z)$ is the normal cone at $z$; it satisfies $\mathrm{Gap}(z) \le D \cdot r^{\tan}(z)$.

## Depends on

- [Smooth monotone game and monotone variational inequality](smooth-monotone-game-variational-inequality.md)

## Sources

- Y. Cai, A. Oikonomou, W. Zheng, "Finite-Time Last-Iterate Convergence for Learning in Multi-Player Games", NeurIPS 2022; full version "Tight Last-Iterate Convergence of the Extragradient and the Optimistic Gradient Descent-Ascent Algorithm for Constrained Monotone Variational Inequalities", arXiv:2204.09228.
