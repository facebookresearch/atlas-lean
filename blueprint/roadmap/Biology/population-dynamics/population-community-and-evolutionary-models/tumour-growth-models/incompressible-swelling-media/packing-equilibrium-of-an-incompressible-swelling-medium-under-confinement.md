# Packing equilibrium of an incompressible swelling medium under confinement

**Setting.** A swelling medium (a gel, or a growing tumor) is made of $N$ particles that cannot overlap. In the continuum description, $n(x) \ge 0$ is the particle density on $\mathbb{R}^d$ and $\tau(x) > 0$ the local particle volume, so non-overlap reads $n\tau \le 1$ (the density never exceeds the packing density $\tau^{-1}$). Particles feel a confining potential $V(x,\tau) \ge 0$, and the effective potential is $W(x) = V(x,\tau(x))$. The equilibrium minimizes the confinement energy:

$$ \min\Big\{ F[n] = \int_{\mathbb{R}^d} W(x)\,n(x)\,dx \ :\ n \ge 0,\ \ n\tau \le 1,\ \ \int_{\mathbb{R}^d} n\,dx = N \Big\}. $$

**Theorem.** Assume $W$ and $\tau^{-1}$ are smooth, $W \ge 0$, $0 < \tau < \infty$, $|\nabla W| < \infty$; every level set $\mathcal{E}(u) = \{W = u\}$, $u \ge 0$, is compact with positive $(d-1)$-dimensional measure; $x = 0$ is the only critical point of $W$ and $W(0) = 0$; $W(x) \to +\infty$ as $|x| \to \infty$; and $\int_{\mathbb{R}^d}\tau^{-1} > N$. Then the minimizer is unique and is the saturated packing state

$$ n_N(x) = \begin{cases} \tau(x)^{-1}, & x \in \Omega_N,\\ 0, & x \notin \Omega_N, \end{cases} \qquad \Omega_N = \{x : 0 \le W(x) \le U_N\}, $$

where $U_N$ is the unique solution of $P(U_N) = N$ with $P(u) = \int_{\{0 \le W \le u\}}\tau^{-1}\,dx$.

Every minimizer satisfies the bang-bang property: for every $x$, either $n(x)\tau(x) = 1$ or $n(x) = 0$. Within its support the medium is incompressible (packed), and the support is a sublevel set of the effective potential chosen to hold exactly $N$ particles.

## Expansion

The problem is a linear program over a convex set: an optimal $n$ fills the lowest-potential regions first up to the packing bound. If $0 < n\tau < 1$ on a set of positive measure, moving mass from higher to lower values of $W$ (possible because the level sets have positive measure and $W$ has no critical points except the minimum) strictly lowers $F$, which gives the bang-bang property. The mass constraint then fixes the threshold $U_N$; $P$ is continuous and strictly increasing because $\tau^{-1} > 0$ and the level sets carry no mass, so $U_N$ is unique. When $\tau$ and the potential change in time, $n_N(\cdot,t)$ evolves through the moving sublevel sets $\Omega_N(t)$.

## Sources

- Pierre Degond, Marina A. Ferreira, Sara Merino-Aceituno and Mickaël Nahon, "A new continuum theory for incompressible swelling materials", arXiv:1707.02166 (2017), Section 2.3 (mechanical equilibrium); Section 3, Theorem 3.1 and Lemma 3.2, <https://doi.org/10.48550/arXiv.1707.02166>.
