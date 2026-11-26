# The Riemann hypothesis holds if and only if all zeros of $H_0$ are real

The Riemann hypothesis holds if and only if every zero of the de Bruijn–Newman deformation at time
$0$,

$$
H_0(z) = \int_0^\infty \Phi(u) \cos(z u) \, du,
$$

is real; here $\Phi$ is Newman's kernel. In the notation of this folder, the Riemann hypothesis is
equivalent to the real-rootedness of $H_\lambda$ at $\lambda = 0$.

By the Fourier integral for the Riemann $\xi$ function, $8 H_0(z) = \xi(1/2 + iz/2)$ for every
complex $z$. So $z$ is a zero of $H_0$ exactly when $\rho = 1/2 + iz/2$ is a zero of $\xi$, and
$z = -2i(\rho - 1/2)$ is real exactly when $\operatorname{Re} \rho = 1/2$. The zeros of $\xi$ are
the nontrivial zeros of $\zeta$: the factor $\tfrac12 s(s-1)$ cancels the poles of the completed zeta
function $\pi^{-s/2} \Gamma(s/2) \zeta(s)$ at $s = 0$ and $s = 1$, and the poles of $\Gamma(s/2)$ at
$-2, -4, \dots$ cancel the trivial zeros.

## Depends on

- [Statement of the Riemann hypothesis](../riemann-hypothesis-statement.md)
- [Real-rootedness of the de Bruijn–Newman deformation](zeros-all-real.md)

## Proof depends on

- [Fourier integral for the Riemann ξ function](eight-mul-h-zero-eq-riemann-xi.md)

## Sources

- B. Rodgers and T. Tao, *The de Bruijn–Newman constant is non-negative*, Forum Math. Pi 8 (2020), e6, arXiv:1801.05914v3, §1: with $H_0(z) = \tfrac18 \xi(1/2 + iz/2)$ as in their equation (1), "the Riemann hypothesis is equivalent to the assertion that all the zeroes of $H_0$ are real", and $H_0(z) = \int_0^\infty \Phi(u) \cos(zu)\,du$ with $\Phi$ as in their equation (3).
