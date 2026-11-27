# Solutions of the one-leg twin give solutions of the multistep method

Let a linear multistep method have $s = \sigma(1) \ne 0$. If $(y_n)_{n \ge 0}$ satisfies its [one-leg twin](one-leg-twin.md) $\rho(E) y_n = h\, s\, f(\sigma(E) y_n / s)$, then $z_n = \sigma(E) y_n / s = \sum_j \beta_j y_{n+j} / s$ satisfies the linear multistep method itself, $\rho(E) z_n = h\, \sigma(E) f(z_n)$; for $\sigma(1) = 1$ this is $z_n = \sigma(E) y_n$. The proof uses that $\rho(E)$ and $\sigma(E)$ commute. The identity maps solutions to solutions but does not carry over the contractivity of the one-leg method: for the dissipative scalar field $f(y) = -\max(y, 0)$ and $h = 6$, the implicit midpoint rule is G-stable with $G = [1]$, while one step of its twin, the trapezium rule, sends $1$ to $-2$ and $0$ to $0$, doubling their distance.

## Depends on

- [One-leg twin of a linear multistep method](one-leg-twin.md)
- [G-stability](g-stability.md)
- [Dissipative system](dissipative-system.md)

## Sources

- E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, Mathematical Institute, University of Oxford, version of 2 March 2022, Section 5, the computation $\rho(E) z_n = \rho(E)\sigma(E) y_n = \sigma(E)\rho(E) y_n = h\sigma(E) f(\sigma(E) y_n) = h\sigma(E) f(z_n)$ after (96). <https://people.maths.ox.ac.uk/suli/nsodes.pdf>
