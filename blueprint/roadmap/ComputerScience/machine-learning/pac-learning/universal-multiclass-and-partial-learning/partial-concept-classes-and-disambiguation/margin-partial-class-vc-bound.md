# Margin and low-dimensional data assumptions as partial classes of bounded VC dimension

Let $V$ be a real Hilbert space and $R, \gamma > 0$. Let $H_{R,\gamma}$ be the partial class of homogeneous halfspace concepts $x \mapsto \mathrm{sign}\langle w, x\rangle$ on $V$ with $\|w\| = 1$, each defined only on the points $x$ with $\|x\| \le R$ and $|\langle w, x\rangle| \ge \gamma$, and undefined elsewhere. Then $\mathrm{VC}(H_{R,\gamma}) \le \lceil R^2/\gamma^2 \rceil$, independently of the dimension of $V$. Thus margin assumptions on the data, which cannot be expressed by restricting a total class of halfspaces, are exactly realizability by a partial class of finite VC dimension.

## Proof sketch

If $d$ points are shattered by $H_{R,\gamma}$, then for every sign vector the corresponding partition of the points is separable with margin $\gamma$ inside the ball of radius $R$. Averaging $\|\sum_i \sigma_i x_i\|^2$ over uniformly random signs gives at most $d R^2$, while margin separation of every partition forces $\|\sum_i \sigma_i x_i\| \ge d\gamma$ for some sign pattern, so $d^2 \gamma^2 \le d R^2$.

## Depends on

- [Partial concept classes and their VC and Littlestone dimensions](partial-concept-class.md)

## Sources

- N. Alon, S. Hanneke, R. Holzman, S. Moran, "A Theory of PAC Learnability of Partial Concept Classes", FOCS (2021), arXiv:2107.08444.
