# Asymptotic covariance of two Aalen–Johansen cumulative incidences

For a competing-risks subject law $\mu$ on a finite grid with causes $c$, write $e_{l,c} = P(X = l, \delta = 1, J = c)$, $d_l = \sum_ce_{l,c}$, $y_l = P(X \ge l)$, $S(l-)$ the product-limit survival before $l$, $S(j)$ the Kaplan–Meier survival and $F_c$ the Aalen–Johansen cumulative incidences of the mean cell vector, and suppose $P(\min(T, C) \ge m) \ne 0$ and $d_l \ne y_l$ for $l \le j \wedge j'$, $j, j' \le m$. Then the influence covariance of $F_c(j)$ and $F_{c'}(j')$ is

$$\sum_{l\le j\wedge j'}\Big[\frac{(F_c(j) - F_c(l))(F_{c'}(j') - F_{c'}(l))d_l}{y_l(y_l - d_l)} - \frac{(F_c(j) - F_c(l))S(l-)e_{l,c'}}{y_l^2} - \frac{(F_{c'}(j') - F_{c'}(l))S(l-)e_{l,c}}{y_l^2} + \frac{S(l-)^2(\mathbf 1\{c = c'\}e_{l,c}y_l - e_{l,c}e_{l,c'})}{y_l^3}\Big].$$
