# Global stability of a renewal epidemic model with variable susceptibility

**Model.** Susceptibles carry a static susceptibility label $\sigma$ in a finite measure space $\Sigma$. Let $S(t,\sigma)$ be the density of susceptibles with label $\sigma$ and $F(t)$ the force of infection. With recruitment $\lambda(\sigma)$, per-capita death rate $\mu > 0$, relative susceptibility $\eta(\sigma)$ (both $\lambda, \eta \in L^\infty_+(\Sigma)$) and an infectivity kernel $A(\tau) \ge 0$ of bounded variation, vanishing beyond a finite maximal infection age $\bar\tau$,

$$
\begin{aligned}
\frac{\partial S(t,\sigma)}{\partial t} &= \lambda(\sigma) - \mu S(t,\sigma) - \eta(\sigma) F(t) S(t,\sigma),\\
F(t) &= \int_\Sigma \int_0^{\bar\tau} A(\tau)\,\eta(\sigma)\,F(t - \tau)\,S(t - \tau, \sigma)\,\mathrm{d}\tau\,\mathrm{d}\sigma .
\end{aligned}
$$

The phase space is $\Omega = C^0_+([-\bar\tau, 0], L^\infty_+(\Sigma)) \times L^1_+(-\bar\tau, 0)$ (histories of $S$ and $F$), on which the model generates a continuous semiflow. Let $\partial\Omega$ be the histories with no infection and $\widehat\Omega = \Omega \setminus \partial\Omega$.

**Threshold and equilibria.** The infection-free equilibrium is $S^0(\sigma) = \lambda(\sigma)/\mu$, $F = 0$, and

$$
R_0 = \eta^0 \int_0^{\bar\tau} A(\tau)\,\mathrm{d}\tau, \qquad \eta^0 = \int_\Sigma \eta(\sigma) S^0(\sigma)\,\mathrm{d}\sigma .
$$

An endemic equilibrium $\bar S(\sigma) = \lambda(\sigma)/(\mu + \eta(\sigma)\bar F)$ with $\bar F > 0$ exists, and is then unique, if and only if $R_0 > 1$. Here $\bar F$ is the unique positive root of

$$
\int_\Sigma \frac{\eta(\sigma)\lambda(\sigma)}{\mu + \eta(\sigma)\bar F}\,\mathrm{d}\sigma \int_0^{\bar\tau} A(\tau)\,\mathrm{d}\tau = 1 .
$$

At equilibrium, susceptibles are depleted in proportion to their susceptibility.

**Theorem 1.** If $R_0 \le 1$, the infection-free equilibrium is globally asymptotically stable in $\Omega$. If $R_0 > 1$, solutions starting near it in $\widehat\Omega$ move away, while those starting in $\partial\Omega$ converge to it.

**Theorem 2.** If $R_0 > 1$, the endemic equilibrium is globally asymptotically stable in $\widehat\Omega$.

## Expansion

The left-hand side of the endemic identity is strictly decreasing in $\bar F$ and equals $R_0$ at $\bar F = 0$, which gives existence and uniqueness exactly when $R_0 > 1$. For global stability, restrict to the forward-invariant set reached after time $\bar\tau$, where $S > 0$ and the smoothing of the convolution makes trajectories regular. With $g(x) = x - 1 - \ln x$ and $\xi(\tau) = \eta^0\int_\tau^{\bar\tau} A(\rho)\,\mathrm{d}\rho$ (so $\xi(0) = R_0$, $\xi(\bar\tau) = 0$), the functional

$$
U = \int_\Sigma S^0(\sigma)\, g\Big(\frac{S(t,\sigma)}{S^0(\sigma)}\Big)\,\mathrm{d}\sigma + \int_\Sigma\int_0^{\bar\tau} \xi(\tau)\,\eta(\sigma)\,F(t - \tau)\,S(t - \tau, \sigma)\,\mathrm{d}\tau\,\mathrm{d}\sigma
$$

has a derivative along trajectories that is non-positive when $R_0 \le 1$: the susceptible part contributes a term of the form $-\mu\int_\Sigma (S - S^0)^2/S\,\mathrm{d}\sigma$, and the infection terms combine, using $\mathrm{d}\xi/\mathrm{d}\tau = -\eta^0 A$, into a multiple of $F(t)$ that is controlled by $R_0 - 1$. LaSalle's invariance principle on the compact attractor then gives convergence. For the endemic case, a Volterra-type functional built from $g(S/\bar S)$ and from $g$ applied to the ratio of the delayed incidence $\eta F S$ to its endemic value, weighted by the residual infectivity, has a non-positive derivative by Jensen's inequality, with equality only at the endemic equilibrium. With constant susceptibility, $\eta \equiv 1$, the results reduce to the global stability of the classical Kermack-McKendrick renewal model with demography.

## Sources

- Michael T. Meehan, Daniel G. Cocks and Emma S. McBryde, "Global stability properties of a class of renewal epidemic models with variable susceptibility", arXiv (2020), Section 2 (model, phase space, $R_0$), Section 3 (equilibria), Section 4 (Theorems 1 and 2 and their Lyapunov functionals), <https://doi.org/10.48550/arXiv.2007.11796>.
- W. O. Kermack and A. G. McKendrick, "A contribution to the mathematical theory of epidemics", Proceedings of the Royal Society A 115 (1927), 700–721, <https://doi.org/10.1098/rspa.1927.0118>.
