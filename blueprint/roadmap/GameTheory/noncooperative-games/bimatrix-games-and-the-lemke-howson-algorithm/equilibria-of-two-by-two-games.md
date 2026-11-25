# Classification of Nash equilibria of 2×2 games

Consider a two-player game with actions $T, B$ for player 1 and $L, R$ for player 2. Put $\alpha = u_1(T, L) - u_1(B, L)$, $\beta = u_1(T, R) - u_1(B, R)$, $\gamma = u_2(T, L) - u_2(T, R)$ and $\delta = u_2(B, L) - u_2(B, R)$. With $p = P(T)$ and $q = P(L)$, player 1's advantage from $T$ is $q\alpha + (1-q)\beta$ and player 2's advantage from $L$ is $p\gamma + (1-p)\delta$; $(p, q)$ is a Nash equilibrium exactly when $p = 1$ where the first is positive, $p = 0$ where it is negative, $q = 1$ where the second is positive, and $q = 0$ where it is negative. This characterization involves no division. If $\alpha, \beta, \gamma, \delta$ are all nonzero: when $\alpha\beta > 0$ or $\gamma\delta > 0$ there is a unique equilibrium, and it is pure; when $\alpha\beta < 0$ and $\gamma\delta < 0$ there is a unique completely mixed equilibrium $q = \beta/(\beta - \alpha)$, $p = \delta/(\delta - \gamma)$, together with two pure equilibria if $\alpha\gamma > 0$ and none if $\alpha\gamma < 0$. If some difference is zero the equilibrium set can be infinite; for example, when all payoffs are equal every profile is an equilibrium.

## Proof depends on

- [Mixed Nash equilibrium](../nash-s-theorem/is-mixed-nash.md): mixed equilibria.

## Sources

- The statement is derived on this page from its definitions and the linked results; no external source is followed.
