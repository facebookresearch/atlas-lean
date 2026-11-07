# Convergents and the Lagrange approximability

Let $\xi$ be an irrational real number,
with complete quotients $\xi_0 = \xi$ and $\xi_{k+1} = 1/\{\xi_k\}$, where $\{x\}$ is the
fractional part of $x$, and digits $a_k = \lfloor \xi_k \rfloor$, so that
$\xi = [a_0; a_1, a_2, \dots]$. For $k \ge 1$ let
$c_k = a_k + [0; a_{k-1}, \dots, a_1] + \{\xi_k\}$, where the middle term is $0$ when $k = 1$.
Then for every $k \ge 1$ the convergent $p/q = [a_0; a_1, \dots, a_{k-1}]$, written in lowest terms
with $q > 0$, satisfies $(-1)^k / (q^2 (p/q - \xi)) = c_k$. Moreover, the $1$-Lagrange
approximability $\lambda_1(\xi)$ equals $\limsup_{k \to \infty} c_k$, taken in the extended reals.

## Sources

- Brandon Dong, Soren Dupont, Evan M. O'Dorney and W. Theo Waitkus, *Raney Transducers and the Lowest Point of the n-Lagrange Spectrum*, INTEGERS 25 (2025), Article A47, Proposition 4 (`integers-2025-A47-prop-4`), parts (a) and (c), quoted from Cusick and Flahive, Appendix 1.
