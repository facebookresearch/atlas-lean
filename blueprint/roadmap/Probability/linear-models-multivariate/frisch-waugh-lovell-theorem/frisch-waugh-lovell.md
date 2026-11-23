# Frisch–Waugh–Lovell theorem

Let $m$ and $\kappa$ be finite index sets, $W$ a symmetric real $m \times m$ matrix, $\langle x, y\rangle_W = x^\top W y$, $A$ a real $m \times \kappa$ matrix and $y, z \in \mathbb{R}^m$. Suppose that $(b, t) \in \mathbb{R}^\kappa \times \mathbb{R}$ solves the weighted normal equations of the regression of $y$ on $[A \mid z]$,

$$A^\top W (y - Ab - tz) = 0, \qquad z^\top W (y - Ab - tz) = 0,$$

and that $z_\perp = z - Au$ is the weighted residual of $z$ on $A$, $A^\top W z_\perp = 0$, for some $u \in \mathbb{R}^\kappa$. Then

$$t\, \langle z_\perp, z_\perp\rangle_W = \langle z_\perp, y\rangle_W.$$

## Sources

- R. Frisch and F. V. Waugh, *Partial time regressions as compared with individual trends*, Econometrica 1 (1933), 387–401.
- M. C. Lovell, *Seasonal adjustment of economic time series and multiple regression analysis*, J. Amer. Statist. Assoc. 58 (1963), 993–1010.
