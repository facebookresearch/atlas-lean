# Global dynamics of the discretized autocatalytic HIV model

**Setting.** Uninfected CD4$^+$ T cells $T_4$, infected cells $T_I$ and infectious virions $V_I$ obey

$$\dot T_4 = s + e_1T_4V_I - \gamma_1T_4, \qquad \dot T_I = e_2T_4V_I - e_3T_I, \qquad \dot V_I = e_4T_I - \sigma V_I,$$

where $e_1 = r - \lambda_1$ combines autocatalytic recruitment $rT_4V_I$ with infection loss $\lambda_1T_4V_I$. A first-order semi-implicit (nonstandard) discretization with time step $\ell > 0$, followed by rescaling, gives the difference system

$$x_{n+1} = \frac{1 + x_n}{b + cz_n}, \qquad y_{n+1} = dy_n + ex_{n+1}z_n, \qquad z_{n+1} = fz_n + y_{n+1},$$

with $b = 1 + \ell\gamma_1 > 1$, $c = -\ell e_1 \in \mathbb R$, $d = (1+\ell e_3)^{-1} \in (0,1)$, $f = (1+\ell\sigma)^{-1} \in (0,1)$ and $e = \ell^3se_4e_2\big((1+\ell e_3)(1+\ell\sigma)\big)^{-1} > 0$. Its **discrete reproduction number** is

$$\mathcal R_d = \frac{e}{(b-1)(1-d)(1-f)}.$$

For $c \ne 0$ and $\mathcal R_d \ne 1$ the equilibria are the disease-free point $E_0 = \big((b-1)^{-1}, 0, 0\big)$ and

$$E_1 = \Big(\frac{(1-d)(1-f)}{e},\ \frac{e - (b-1)(1-d)(1-f)}{c(1-d)},\ \frac{e - (b-1)(1-d)(1-f)}{c(1-d)(1-f)}\Big),$$

which is positive exactly when $c > 0$ and $\mathcal R_d > 1$.

**Theorem.** Let $b > 1$, $c > 0$, $0 < d < 1$, $e > 0$, $0 < f < 1$.
1. (Theorems 3.3–3.4) If $\mathcal R_d < 1$, then $E_0$ is globally asymptotically stable on $\mathbb R^3_+$; if $\mathcal R_d > 1$, it is unstable.
2. (Theorems 3.5, 3.7, 3.10 and 3.11) If $\mathcal R_d > 1$, i.e. $e > (b-1)(1-d)(1-f)$, then every solution with $(y_0,z_0) \ne (0,0)$ is bounded away from zero and $E_1$ is globally asymptotically stable.
3. (Theorem 3.9) Every solution with nonnegative initial data converges to $E_0$ or $E_1$; the discrete model has no cycles or chaos, for every step size $\ell$.

For the continuous model with $e_1 < 0$ (Theorem 2.1), the disease-free state is globally asymptotically stable when the continuous reproduction number $\mathcal R_c \le 1$ and the endemic state is globally asymptotically stable when $\mathcal R_c > 1$, so the discretization preserves the threshold dynamics.

## Expansion

The semi-implicit choice (new $T_4$ and $T_I$ in the loss terms, old $V_I$ in the infection term) makes every update a positive rational map, so positivity and equilibria are preserved for all step sizes, which explicit Euler schemes do not achieve. $\mathcal R_d$ is a product of three factors: $1/(b-1)$ is the scaled disease-free T-cell level, and $1/(1-d)$ and $1/(1-f)$ are the expected lifetimes (in steps) of an infected cell and a virion, so $e$ times their product counts secondary infected cells per infected cell. Global convergence uses the monotone structure of the map ($x_{n+1}$ decreasing in $z_n$, $y_{n+1}$ and $z_{n+1}$ increasing in their arguments) through a theorem on convergence of mixed-monotone systems of difference equations (Theorem 3.6), together with explicit $\liminf$ and $\limsup$ bounds (Theorem 3.2).

## Sources

- Majid Jaberi-Douraki, "Continuous and discrete dynamics of a deterministic model of HIV infection", arXiv:1708.09462 (2017), Section 2 (continuous model, Theorem 2.1), Section 3 (discrete model, $\mathcal R_d$, equilibria, Theorems 3.2–3.11), <https://doi.org/10.48550/arXiv.1708.09462>.
