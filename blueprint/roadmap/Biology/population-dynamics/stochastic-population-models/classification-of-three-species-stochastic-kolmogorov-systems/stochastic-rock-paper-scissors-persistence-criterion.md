# Stochastic rock–paper–scissors persistence criterion

Consider three species with densities $\mathbf X(t)=(X_1,X_2,X_3)$ in a stochastic Kolmogorov (generalized Lotka–Volterra) system driven by environmental noise:

$$
dX_i=X_i f_i(\mathbf X)\,dt+X_i g_i(\mathbf X)\,dE_i(t),\qquad i=1,2,3,
$$

where $\mathbf E=\Gamma^\top\mathbf B$ for a standard Brownian motion $\mathbf B$ and $\Gamma^\top\Gamma=\Sigma=(\sigma_{ij})$. Standing assumptions:

- $f_i,g_i$ are locally Lipschitz on $\mathbb{R}^3_+$ and $(g_ig_j\sigma_{ij})$ is positive definite everywhere.
- A dissipativity condition at infinity holds: with $c\in(0,\infty)^3$ and $\gamma_b>0$, the $\limsup$ as $\|x\|\to\infty$ of $\frac{\sum_i c_ix_if_i}{1+\sum_i c_ix_i}-\frac12\frac{\sum_{ij}\sigma_{ij}c_ic_jx_ix_jg_ig_j}{(1+\sum_i c_ix_i)^2}+\gamma_b\bigl(1+\sum_i(|f_i|+g_i^2)\bigr)$ is negative.
- $g_i^2$ grows slightly slower than $|f_i|$.

Then solutions exist, are unique, never leave the faces they start on, and the process is Feller.

For an ergodic invariant probability measure $\mu$ with species support $I_\mu$, the **invasion rates** (external Lyapunov exponents) are

$$
\lambda_i(\mu)=\int\Bigl(f_i(x)-\tfrac{\sigma_{ii}}{2}g_i^2(x)\Bigr)\mu(dx),\qquad i\notin I_\mu,
$$

and $\lambda_i(\mu)=0$ for $i\in I_\mu$. If $\lambda_i(\boldsymbol\delta_0)>0$ for all $i$, each species alone has a unique ergodic measure $\mu_i$ on its axis. $\mathbf X$ is a **rock–paper–scissors system of type (a)** if additionally

$$
\min\{\lambda_1(\mu_2),\lambda_2(\mu_3),\lambda_3(\mu_1)\}>0>\max\{\lambda_1(\mu_3),\lambda_2(\mu_1),\lambda_3(\mu_2)\},
$$

so species $1$ can invade $2$, $2$ can invade $3$, $3$ can invade $1$, and none of the reverse invasions succeeds. This is a stochastic heteroclinic cycle.

**Theorem.** Let $\mathbf X$ be a rock–paper–scissors system of type (a).

1. If $\lambda_1(\mu_2)\lambda_2(\mu_3)\lambda_3(\mu_1)+\lambda_1(\mu_3)\lambda_2(\mu_1)\lambda_3(\mu_2)>0$, then $\mathbf X$ is **strongly stochastically persistent**: there is a unique invariant probability measure $\pi^*$ supported on $(0,\infty)^3$, the occupation measures converge to it almost surely, and $\|\mathbb P_y(\mathbf X(t)\in\cdot)-\pi^*\|_{TV}\to0$ for every $y\in(0,\infty)^3$.
2. If the inequality is reversed, then almost surely the limit points of the occupation measures lie in the convex hull of $\{\mu_1,\mu_2,\mu_3\}$ and $\limsup_{t\to\infty}\frac1t\log\min_iX_i(t)<0$. The trajectory cycles ever closer to the boundary and some species is always exponentially rare.

## Expansion

The key step is a linear-algebra lemma. When the product inequality holds, there are weights $p_1,p_2,p_3>0$ with $\sum_ip_i\lambda_i(\mu_j)>0$ for $j=1,2,3$. When it is reversed, there are weights making all three sums negative. In the first case, positivity at the origin ($\lambda_i(\boldsymbol\delta_0)>0$) extends the inequality to every invariant measure on the boundary. A general persistence theorem then applies: if every boundary invariant measure has a positive invasion rate, the system is strongly stochastically persistent. In the second case, the Lyapunov function $U(x)=(1+c^\top x)\,x_1^{p_1}x_2^{p_2}x_3^{p_3}/(x_1+x_2+x_3)^{p_0}$ contracts in expectation near the boundary away from the origin. This shows that trajectories approach the heteroclinic cycle, where some species is exponentially rare. The criterion is the stochastic form of the average-Lyapunov-function test for heteroclinic cycles, with invasion rates measured against the ergodic measures $\mu_i$ instead of equilibria.

## Sources

- A. Hening, D. H. Nguyen, S. J. Schreiber, "A classification of the dynamics of three-dimensional stochastic ecological systems", arXiv preprint (2020), Section 2 (Assumptions 2.1–2.2), Section 3 (Definition of rock-paper-scissor systems, Theorem 3.1) and Section 6 (Lemma 6.1 and proof), <https://doi.org/10.48550/arXiv.2004.00535>.
