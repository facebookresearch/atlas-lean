# Spectrum of a delayed neural field on the sphere

Let $\Omega = S^2$ be the unit sphere with great-circle distance, $f$ a smooth bounded firing-rate function, and $w, \tau : [-1,1] \to \mathbb R$ Hölder continuous with exponent $\alpha \in (1/2, 1]$, with $\tau \ge 0$ not identically zero. The voltage-based neural field with isotropic connectivity $w(r \cdot r')$ and delays $\tau(r \cdot r')$ is

$$\partial_t u(t,r) = -u(t,r) + \int_\Omega w(r \cdot r')\, f\bigl(u(t - \tau(r \cdot r'), r')\bigr)\, dr', \qquad r \in \Omega,$$

posed for initial histories on $[-h, 0]$, $h = \max \tau$, in a space of Lipschitz-in-time, Hölder-in-space functions.

1. **Kernel expansion.** If $g$ is Hölder continuous on $[-1,1]$ with exponent $\alpha \in (1/2,1]$ and $G(r,r') = g(r \cdot r')$, then with $P_n$ the Legendre polynomials and $Y_n^m$ the orthonormal spherical harmonics,

$$G(r,r') = \sum_{n=0}^{\infty} G_n \sum_{m=-n}^{n} Y_n^m(r)\, \overline{Y_n^m(r')}, \qquad G_n = 2\pi \int_{-1}^{1} g(s)\, P_n(s)\, ds, \tag{11}$$

with uniform convergence on $\Omega \times \Omega$.
2. **Spectrum.** Let $\hat u$ be a homogeneous steady state, $\hat u = w_0 f(\hat u)$ with $w_0 = \int_\Omega w(r \cdot r')\,dr'$, and $\kappa = f'(\hat u)$. Let $G_n(\lambda)$ be the coefficients (11) of $g(s) = w(s)\, e^{-\lambda \tau(s)}$. The point spectrum of the linearization is

$$\sigma_p = \{\lambda \in \mathbb C : E_n(\lambda) = 0 \text{ for some } n \ge 0\}, \qquad E_n(\lambda) = \lambda + 1 - \kappa\, G_n(\lambda), \tag{21}$$

each root of $E_n$ having the $2n+1$ eigenfunctions $e^{\lambda t} Y_n^m(r)$, $m = -n, \dots, n$, with equal algebraic and geometric multiplicity. The essential spectrum is $\{-1\}$.
3. **Resolvent.** For $\mu \notin \sigma_p \cup \{-1\}$ and $y \in V$, the equation $(\mu+1)q(r) - \kappa \int_\Omega w(r \cdot r') e^{-\mu \tau(r \cdot r')} q(r')\, dr' = y(r)$ has a unique solution, with spherical-harmonic coefficients

$$q_{nm} = \frac{y_{nm}}{\mu + 1 - \kappa\, G_n(\mu)} .$$

Without delays ($\tau \equiv 0$) the eigenvalues are real, $\lambda_n = -1 + \kappa w_n$ with $w_n$ the coefficients of $w$, so oscillatory (Hopf) instabilities need delays.

## Expansion

Item 1 is the Funk–Hecke formula. A Hölder kernel with exponent above $1/2$ has a uniformly convergent spherical-harmonic expansion, and isotropy of $G$ forces its coefficient matrix to be diagonal and constant in $m$ within each degree $n$. For item 2, substituting $v = e^{\lambda t} q(r)$ into the linearization $\partial_t v = -v + \kappa \int_\Omega w(r \cdot r') v(t - \tau(r \cdot r'), r')\,dr'$ gives $(\lambda+1) q = \kappa \int_\Omega w\, e^{-\lambda\tau} q\, dr'$. Expanding the kernel by item 1 and projecting on $Y_n^m$ decouples degrees: the projection is nonzero only when $E_n(\lambda) = 0$. The same projection gives the resolvent coefficients of item 3. Since $E_n$ depends on $n$ but not $m$, an eigenvalue crossing the imaginary axis at degree $n$ does so with a $(2n+1)$-dimensional eigenspace. The resulting $O(3)$-symmetric Hopf bifurcations select standing or travelling waves on the sphere. For exponential connectivity with axonal delays proportional to great-circle distance, the coefficients $G_n(\lambda)$ follow from a recurrence for $\int_{-1}^1 e^{a \cos^{-1} s} P_n(s)\, ds$.

## Sources

- S. Visser, R. Nicks, O. Faugeras, S. Coombes, "Standing and travelling waves in a spherical brain model: The Nunez model revisited", *Physica D* (2017), Section 2 (Eqs. (1)–(3), Lemmas 1–4, Theorems 1–2, Eq. (11)) and Section 3 (Eqs. (18)–(22), Theorem 3, Theorem 4), <https://doi.org/10.1016/j.physd.2017.02.017> (PMC5421190).
