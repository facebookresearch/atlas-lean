# Wright–Fisher martingale-problem solutions are weak solutions of the equation

Let $X$ be a continuous $[0, 1]$-valued solution of the [martingale problem for the Wright–Fisher diffusion with selection and two-way mutation](two-way-mutation-and-selection-wright-fisher-mar.md). Then, on an enlarged probability space carrying an independent Brownian motion, $X$ is a weak solution of

$$dX_t = b(X_t)\, dt + \sqrt{X_t (1 - X_t)}\, dW_t, \qquad b(x) = \alpha x (1 - x) + \tfrac{1}{2}\bigl(\theta_1 (1 - x) - \theta_2 x\bigr).$$

This is the special case $a(x) = x(1 - x)$, continuous on $[0, 1]$, of [the weak representation of one-dimensional martingale-problem solutions](../../../../Probability/stochastic-calculus/stochastic-differential-equations/weak-sde-representation-of-one-dimensional-marti.md).

## Depends on

- [Weak SDE representation of one-dimensional martingale-problem solutions](../../../../Probability/stochastic-calculus/stochastic-differential-equations/weak-sde-representation-of-one-dimensional-marti.md)
- [Martingale problem for the Wright–Fisher diffusion with selection and two-way mutation](two-way-mutation-and-selection-wright-fisher-mar.md)

## Expansion

The coefficients of [the general representation](../../../../Probability/stochastic-calculus/stochastic-differential-equations/weak-sde-representation-of-one-dimensional-marti.md) instantiate to the Wright–Fisher drift and variance.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986), <https://doi.org/10.1002/9780470316658>, Chapter 5, Section 3 (stochastic equations and martingale problems).
- I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Springer (1991), <https://doi.org/10.1007/978-1-4612-0949-2>, Chapter 5 (weak solutions).
- D. W. Stroock and S. R. S. Varadhan, *Multidimensional Diffusion Processes*, Springer (1979) (martingale problems).
