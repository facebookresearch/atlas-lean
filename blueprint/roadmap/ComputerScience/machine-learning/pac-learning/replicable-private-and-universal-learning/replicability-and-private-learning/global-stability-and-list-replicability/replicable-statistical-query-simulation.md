# Replicable simulation of a statistical query by randomized rounding

A randomized algorithm $A(S; r)$ taking an i.i.d. sample $S$ from a distribution $D$ and internal randomness $r$ is **$\rho$-replicable** if $\Pr_{S, S' \sim D^n,\, r}[A(S; r) = A(S'; r)] \ge 1 - \rho$ for every $D$, where $S, S', r$ are independent and the same $r$ is used in both runs. Let $\psi : X \to [0,1]$ be a statistical query, $\tau, \delta, \rho \in (0,1)$ with $\rho > 2\delta$. There is a $\rho$-replicable algorithm which, given

$$
n = \tilde O\!\left(\frac{1}{\tau^2 (\rho - 2\delta)^2}\right)
$$

i.i.d. samples, outputs $v$ with $|v - \mathbb{E}_{x \sim D}[\psi(x)]| \le \tau$ except with probability $\delta$. In other words, $\rho$-replicably answering a query to tolerance $\tau$ costs no more than non-replicably answering it to tolerance $\tau' = \Theta(\tau\rho)$.

## Proof sketch

Estimate $\mathbb{E}[\psi]$ empirically to accuracy $\tau' \approx \tau\rho$, then round to the nearest point of a grid of spacing $\Theta(\tau)$ whose offset is drawn from the shared randomness $r$. Two runs on independent samples produce empirical means within $2\tau'$ of each other, and they round to different grid points only if a grid boundary falls between them, which happens with probability $O(\tau'/\tau) = O(\rho)$ over the random offset.

## Depends on

- [Replicable algorithms with shared randomness](../../../replicable-learning/replicable-algorithms-with-shared-seed.md)
- [Statistical query model with tolerance and the SQ dimension](../../../statistical-query-dimension/statistical-query-dimension.md)

## Proof depends on

- [Randomized-threshold and random-grid rounding lemmas](../../../replicable-learning/randomized-rounding-disagreement.md)
- [Hoeffding's inequality for averages of bounded variables](../../../../../../Probability/concentration-inequalities/hoeffding-s-inequality/measure-real-avg-sub-ge-le.md)

## Sources

- R. Impagliazzo, R. Lei, T. Pitassi, J. Sorrell, "Reproducibility in Learning", STOC (2022), arXiv:2201.08430, Definitions 1.1, 2.1 and 2.2, Theorem 1.2 and Theorem 2.3.
