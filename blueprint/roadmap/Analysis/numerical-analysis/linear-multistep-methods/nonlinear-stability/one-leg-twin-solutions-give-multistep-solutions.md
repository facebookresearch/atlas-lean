# Solutions of the one-leg twin give solutions of the multistep method

If $(y_n)_{n \ge 0}$ satisfies the [one-leg twin](one-leg-twin.md) $\rho(E) y_n = h f(\sigma(E) y_n)$ of a linear multistep method, then $z_n = \sigma(E) y_n = \sum_j \beta_j y_{n+j}$ satisfies the linear multistep method itself, $\rho(E) z_n = h\, \sigma(E) f(z_n)$. The proof uses that $\rho(E)$ and $\sigma(E)$ commute. So results for the one-leg twin transfer to the multistep method.

## Depends on

- [One-leg twin of a linear multistep method](one-leg-twin.md)

## Sources

- E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, Mathematical Institute, University of Oxford, version of 2 March 2022, Section 5, the computation $\rho(E) z_n = \rho(E)\sigma(E) y_n = \sigma(E)\rho(E) y_n = h\sigma(E) f(\sigma(E) y_n) = h\sigma(E) f(z_n)$ after (96). <https://people.maths.ox.ac.uk/suli/nsodes.pdf>
