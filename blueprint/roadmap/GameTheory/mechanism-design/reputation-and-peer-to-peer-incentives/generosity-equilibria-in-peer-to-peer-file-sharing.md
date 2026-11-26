# Generosity equilibria in peer-to-peer file sharing

In the minimalist peer-to-peer model where users with generosity types $\theta$ contribute iff $\theta$ exceeds the cost of contributing, which is the reciprocal of the contribution level $x$ of the population, with types uniform on $[0, \theta_m]$: positive equilibrium contribution levels exist iff $\theta_m \ge 4$: for $\theta_m > 4$ there are two, $x_\pm = \tfrac12 \pm \sqrt{\tfrac14 - 1/\theta_m}$, the higher one locally stable and the lower unstable, and for $\theta_m = 4$ the only one is $x = 1/2$; the high equilibrium increases with $\theta_m$ and tends to full contribution, and contribution collapses from $1/2$ to $0$ as $\theta_m$ crosses $4$. Penalizing free riders by reduced service can rescue participation for low generosity, but exclusion can also reduce welfare.

## Proof sketch

Equilibria solve $x = \Pr[\theta > 1/x] = 1 - 1/(x\theta_m)$, i.e. $\theta_m x^2 - \theta_m x + 1 = 0$, whose discriminant $\theta_m(\theta_m - 4)$ gives two roots for $\theta_m > 4$ and the double root $1/2$ for $\theta_m = 4$; for $\theta_m > 4$, stability follows from the slope of the response function at each root.

## Depends on

- [Strategic Game](../../not-yet-classified/part-02/strategic-game/strategic-game.md)

## Sources

- Moshe Babaioff, John Chuang and Michal Feldman, "Incentives in Peer-to-Peer Systems", Algorithmic Game Theory, Cambridge University Press, 2007, Section 23.3 and Claims 23.1 and 23.2.
