# Invasion-rate criterion for convergence to a coexistence stationary distribution

**Setting.** Let $\mathbf X(t)\in\mathbb R^n_+$ be the densities of $n$ interacting species under environmental fluctuations, in one of three forms:

- **SDE:** $dX_i=X_i\big(f_i(\mathbf X)\,dt+g_i(\mathbf X)\,dE_i\big)$, with $E$ a Brownian motion with covariance matrix $(\sigma_{ij})$;
- **PDMP:** $\dot X_i=X_if_i(\mathbf X,r(t))$, with $r(t)$ a finite-state Markov chain of environmental states;
- **switching SDE:** $dX_i=X_i\big(f_i(\mathbf X,r(t))\,dt+g_i(\mathbf X,r(t))\,dE_i\big)$.

Let $\mathcal M$ be the set of ergodic invariant probability measures supported on the extinction boundary $\partial\mathbb R^n_+$ (subcommunities in which some species is absent), and $\mathrm{Conv}(\mathcal M)$ its convex hull. The **invasion rate** of species $i$ into the subcommunity $\mu$ is

$$\lambda_i(\mu)=\sum_{k}\int_{\partial\mathbb R^n_+}\Big(f_i(\mathbf x,k)-\frac{\sigma_{ii}g_i^2(\mathbf x,k)}{2}\Big)\mu(d\mathbf x,k),$$

with $g_i=0$ for PDMPs and a single state for SDEs.

**Theorem.** Suppose that for every $\mu\in\mathrm{Conv}(\mathcal M)$

$$\max_{i=1,\dots,n}\lambda_i(\mu)>0,$$

that is, every boundary invariant measure is repelled by at least one missing species. Then the system is strongly stochastically persistent: for every $\epsilon>0$ there is $\delta>0$ with $\liminf_{t\to\infty}\mathbb P\{X_i(t)\ge\delta\ \forall i\}\ge1-\epsilon$ from any interior initial state. Under the technical (nondegeneracy, irreducibility) assumptions of each setting, there is a unique invariant probability measure $\mu^*$ on the interior, and the law of $\mathbf X(t)$ converges to $\mu^*$ in total variation; for nondegenerate SDEs the convergence is exponentially fast.

**Application (competitive Lotka–Volterra with switching).** For two competitors whose growth rates switch between two environments with stationary weights $\nu_1,\nu_2$, if each survives alone ($\nu_1\ell_i(1)+\nu_2\ell_i(2)>0$) and each can invade the other's stationary state ($\lambda_1(\mu_2)>0$, $\lambda_2(\mu_1)>0$), then both persist and the process converges to a unique stationary distribution on $(0,\infty)^2\times\{1,2\}$, even when one environment alone would lead to competitive exclusion.

## Expansion

Near a boundary measure $\mu$, $\log X_i$ grows at the long-run average rate $\lambda_i(\mu)$ by the ergodic theorem (Itô's correction contributes $-\sigma_{ii}g_i^2/2$). If some convex combination of these rates is positive for every boundary measure, one builds a Lyapunov function $V(\mathbf x)=\prod_iX_i^{-p_i}$ times a function controlling infinity, whose expected value contracts near the boundary; this yields tightness of occupation measures away from the boundary and existence of an interior invariant measure. Uniqueness and total-variation convergence come from irreducibility (Hörmander-type brackets for PDMPs, nondegenerate noise for SDEs). Since $\mu^*$ is rarely explicit, the paper complements the criterion with a numerical scheme for approximating it.

## Sources

- Alexandru Hening, Yao Li, "Stationary distributions of persistent ecological systems", arXiv:2003.04398 (2020), Theorems 2.1, 3.1, 4.1 and 6.1, with invasion rates defined in Sections 2–4, <https://doi.org/10.48550/arXiv.2003.04398>.
