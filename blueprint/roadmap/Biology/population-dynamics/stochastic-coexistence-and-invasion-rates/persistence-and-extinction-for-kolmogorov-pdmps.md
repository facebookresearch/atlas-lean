# Persistence and extinction for Kolmogorov piecewise deterministic Markov processes

**Model.** Species densities $X\in\mathbb R^n_+$ follow, between switches of a finite-state environment $r(t)\in\{1,\dots,n_0\}$,
$$\frac{dX_i}{dt}=X_i\,f_i(X,r(t)),\qquad i=1,\dots,n,$$
where the environment jumps from $k$ to $l$ at the state-dependent rate $q_{kl}(X)$, bounded, continuous and irreducible. This is a Kolmogorov piecewise deterministic Markov process (PDMP): environmental noise acts through random switching between deterministic regimes rather than through white noise. Assume locally Lipschitz $f_i$, a Lyapunov-type function $F(x,k)$ controlling growth with bounded ratios $F(x,k)/F(x,l)\le M_F$, so the process does not explode and returns to compact sets.

**Invasion rates.** For an ergodic invariant probability measure $\mu$ of $(X,r)$ supported on the boundary $\partial\mathbb R^n_+\times\{1,\dots,n_0\}$, the invasion rate (external Lyapunov exponent) of species $i$ is
$$\lambda_i(\mu)=\sum_k\int f_i(x,k)\,\mu(dx,k),$$
the long-run per-capita growth rate of a rare species $i$ when the community is distributed as $\mu$.

**Theorem (persistence).** If for every $\mu$ in the convex hull of boundary ergodic measures $\max_i\lambda_i(\mu)>0$, then the process is stochastically persistent in probability and almost surely: for every $\varepsilon>0$ there is $\delta>0$ with $\liminf_t\mathbb P(X_i(t)\ge\delta\ \forall i)>1-\varepsilon$, and the empirical occupation measures eventually put mass at least $1-\varepsilon$ away from the boundary. The proof gives a Lyapunov inequality $\mathbb E V^\theta(X(n^*T^*),r(n^*T^*))\le\kappa V^\theta(x,k)+\tilde K$ with $\kappa<1$. If moreover a point reachable from everywhere satisfies a Hörmander-type bracket condition, there is a unique invariant probability measure on the interior and convergence to it in total variation is exponentially fast.

**Theorem (extinction).** If for some subset $I$ of species every ergodic measure $\pi$ living on $\mathbb R^I_+$ (species in $I$ present) is a transversal attractor, $\max_{i\notin I}\lambda_i(\pi)<0$, and the species in $I$ can invade sub-communities of $I$, then from nearby initial states, with probability close to one, $\limsup_t\frac1t\ln X_i(t)\le-\beta_I<0$ for every $i\notin I$. If all boundary measures are either such attractors or can be invaded, then almost surely the process converges to one of the attractor faces, $\sum_IP^I_{x,k}=1$, where on face $I$ the excluded species decay at the exact rates $\lambda_i(\mu_I)$ when that face carries a unique measure $\mu_I$. Each attractor accessible from $(x,k)$ is reached with positive probability.

## Expansion

The approach adapts the Hening-Nguyen invasion-rate theory for stochastic differential equations to PDMPs on unbounded state spaces with state-dependent switching. A function $V$ combining $F$ with negative powers of the densities, weighted so that a positive combination of invasion rates is positive for every boundary measure, decreases on average near the boundary, so its fractional power $V^\theta$ is a Lyapunov function. Extinction uses the fact that near an attracting face, $\frac1t\ln X_i$ is close to $\lambda_i$ of the face measure, combined with large-deviation-type control of log-Laplace transforms. Applications classify two-species competitive Lotka-Volterra dynamics under switching: if both invasion rates are negative, each species wins with positive probability (when accessible); if one is negative and the other positive, the first is excluded at the exponential rate; if both are positive, the species coexist. The theory also covers predator-prey models, three-species competition, food chains, and switching between stable and explosive one-species regimes.

## Sources

- A. Hening, S. Sabharwal, "Population dynamics under random switching", arXiv:2507.19615 (2025), Section 2 (Definitions 2.1-2.6, Assumptions 2.1-2.6, Theorems 2.1-2.5) and Section 3 (applications, including 3.1 competitive Lotka-Volterra and Lemma 3.1), <https://doi.org/10.48550/arXiv.2507.19615>.
