# Difference bound for Lipschitz stochastic integrals

Let $B$ have the laws of a real Brownian motion, be adapted to a filtration $(\mathcal F_t)_{t\ge0}$, and have increments $B_t-B_s$ independent of $\mathcal F_s$ whenever $s\le t$. Brownian path continuity and completeness of the filtration are not needed for this fixed-time estimate.

Let $X,Y$ be progressively measurable with finite squared time-and-probability energy on $(0,t]$, and let $f:\mathbb R\to\mathbb R$ be globally $K$-Lipschitz. Then the existing selected Itô integrals satisfy

$$\mathbb E\left|\int_0^t f(X_s)\,dB_s-\int_0^t f(Y_s)\,dB_s\right|^2\le K^2\mathbb E\int_{(0,t]}|X_s-Y_s|^2\,ds.$$

Finite energy of each composed integrand is proved, including its possibly nonzero constant offset. The difference isometry then reduces the assertion to the Lipschitz integrand-distance bound. These are the composition estimates used in the classical globally Lipschitz SDE argument; see Le Gall, [Brownian Motion, Martingales, and Stochastic Calculus](https://link.springer.com/book/10.1007/978-3-319-31089-3), Theorem 8.3. No SDE existence or uniqueness conclusion is claimed by this estimate alone.
