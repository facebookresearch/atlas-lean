# Composition–multiplier closure of linear-rate ODE hierarchies

**Setting.** Consider an infinite linear hierarchy $\dot p_n = \sum_{m \ge 0}\mathcal{L}_{n,m}p_m$, $p_n(0) = p_n^0$, $n \ge 0$, such as the master equation of a counting process. It is *linear-rate* if there are finitely supported real sequences $(\alpha_r)_{r \ge -1}$ and $(\beta_r)_{r \ge 0}$ (with $\beta_{-1} = 0$) such that

$$\mathcal{L}_{n+r,\,n} = \alpha_r\,n + \beta_r, \qquad n \ge 0,\ n + r \ge 0,$$

i.e. each jump $n \to n + r$ has a rate affine in the source count. For the birth–death–immigration process with per-capita birth $\lambda$, death $\mu$ and immigration $\nu$: $\alpha_1 = \lambda$, $\beta_1 = \nu$, $\alpha_{-1} = \mu$, $\alpha_0 = -(\lambda + \mu)$, $\beta_0 = -\nu$. The generating function $G(z,t) = \sum_n p_n(t)z^n$ satisfies

$$\partial_tG = A(z)\,\partial_zG + B(z)\,G, \qquad A(z) = \sum_{r \ge -1}\alpha_r z^{r+1},\quad B(z) = \sum_{r \ge 0}\beta_r z^r.$$

**Theorem (composition–multiplier representation).** Let $\dot\Phi_t(z) = A(\Phi_t(z))$, $\Phi_0(z) = z$, and $\dot K_t(z) = B(\Phi_t(z))K_t(z)$, $K_0(z) = 1$. On any domain $\Omega$ where $G_0$ is defined and $\Phi_t(\Omega) \subseteq \Omega$ for $t$ in an interval $I \ni 0$, the unique classical solution is

$$G(z,t) = K_t(z)\,G_0\big(\Phi_t(z)\big).$$

This contains the Kendall–Harris formula for branching with immigration and the Jahnke–Huisinga solution of monomolecular chemical master equations.

**Corollary (closed coefficient recursion).** Writing $\Phi_t = \sum_k\phi_k(t)z^k$ and $K_t = \sum_k\kappa_k(t)z^k$,

$$\dot\phi_n = [z^n]A(\Phi_t), \quad \dot\kappa_n = [z^n]\big(B(\Phi_t)K_t\big), \qquad \phi_n(0) = \delta_{n,1},\ \kappa_n(0) = \delta_{n,0},$$

and the right-hand sides at index $n$ involve only $\phi_0,\dots,\phi_n$ and $\kappa_0,\dots,\kappa_n$:

$$[z^n]A(\Phi_t) = \alpha_{-1}\delta_{n,0} + \sum_{r \ge 0}\alpha_r\sum_{k_1 + \cdots + k_{r+1} = n}\ \prod_{i=1}^{r+1}\phi_{k_i}.$$

So the equations up to any index $N$ form a closed finite ODE system, exact on its window $0 \le n \le N$ for as long as the full solution exists, with no boundary value at $N+1$ (unlike finite state projection). Non-linear-rate hierarchies (Schlögl kinetics, predator–prey, telegraph gene expression) are handled by Strang splitting, using this exact closure on the linear-rate part and a capped solver on the remainder.

## Depends on

- [Generating function of the time-inhomogeneous linear birth–death process](../../population-dynamics/inhomogeneous-sevastyanov-branching-processes/generating-function-of-the-time-inhomogeneous-linear-birth-death-process.md)

## Expansion

Along the backward characteristic $\chi(s) = \Phi_{t-s}(z)$, the PDE reduces to the scalar linear ODE $\frac{d}{ds}G(\chi(s),s) = B(\chi(s))G(\chi(s),s)$, whose integration gives the composition–multiplier formula and its uniqueness. Because $A$ has no negative powers beyond $z^0$ ($r \ge -1$ gives $z^{r+1}$ with $r + 1 \ge 0$) and $B$ is a polynomial, extracting the coefficient of $z^n$ from $A(\Phi_t)$ and $B(\Phi_t)K_t$ only uses Cauchy products of lower-index coefficients; triangularity follows by induction on $n$. Recovering $p_n(t)$ from $G_0(\Phi_t)$ requires only the first $N$ coefficients, giving an exact finite closure.

## Sources

- J. C. Chang, "Operator splitting for exploiting linear-rate closure in solving infinite ODE hierarchies", arXiv:2605.17186 (2026), Section 2.1 (definition of linear-rate hierarchies, composition–multiplier theorem, closed coefficient recursion corollary, finite-window exactness proposition), <https://doi.org/10.48550/arXiv.2605.17186>.
