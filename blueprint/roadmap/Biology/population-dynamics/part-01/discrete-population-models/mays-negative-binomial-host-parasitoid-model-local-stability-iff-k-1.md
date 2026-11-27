# Stability of May's negative-binomial host–parasitoid model

May's model of parasitoids that aggregate in a patchy environment is $H_{t+1} = F H_t (1 + a P_t/k)^{-k}$, $P_{t+1} = H_t - H_{t+1}/F$ (May 1978, eqs. (3)–(4)), with $F > 1$, $a > 0$ and clumping parameter $k > 0$; the negative-binomial factor is the probability that a host escapes parasitism. Its positive equilibrium is $a P^* = k(F^{1/k} - 1)$ (eq. (5)) with $H^* = F P^*/(F - 1)$ (eq. (6), from eq. (4) at equilibrium). May shows that this equilibrium is stable against small disturbances if and only if $k < 1$ (eq. (7), proved in his Appendix 2); for $k > 1$ arbitrarily small disturbances lead to diverging oscillations, and the stability depends only on $k$, independently of $F$ and $a$. As $k \to \infty$ the Nicholson–Bailey result $a P^* = \ln F$ is recovered.

## Expansion

1. The model, with the negative-binomial escape probability $(1 + aP/k)^{-k}$ and the interpretation $k = (1/\mathrm{CV}_p)^2$ of the clumping parameter (eq. (2)), and its equilibrium.
2. The Jacobian at the equilibrium and the stability conditions for a $2 \times 2$ map, as in the source's Appendix 2.
3. The equivalence of these conditions with $k < 1$ for all $F > 1$, $a > 0$, and the boundary case $k = 1$, which the source does not single out.
4. The limit $k \to \infty$ and the comparison with the [Nicholson–Bailey model](../../../not-yet-classified/nicholson-bailey/positive-equilibrium-lyapunov-unstable.md).

## Sources

- R. M. May, Host–parasitoid systems in patchy environments: a phenomenological model, J. Anim. Ecol. 47 (1978), 833–844, eqs. (2)–(7) and Appendix 2. <https://doi.org/10.2307/3674>
