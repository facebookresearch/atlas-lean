# Persistence and extinction thresholds of stochastic Lotka–Volterra food chains

**Setting.** A food chain of $n$ species consists of a prey $X_1$ with logistic self-limitation and predators $X_2,\dots,X_n$, each eating only the species below it:

$$dX_1 = X_1(a_{10} - a_{11}X_1 - a_{12}X_2)\,dt + X_1\,dE_1, \qquad dX_j = X_j(-a_{j0} + a_{j,j-1}X_{j-1} - a_{j,j+1}X_{j+1})\,dt + X_j\,dE_j \quad (2 \le j \le n),$$

with $a_{n,n+1} = 0$, positive coefficients, and environmental noise $E = \Gamma^\top B$ for a standard Brownian motion $B$, covariance $\Sigma = \Gamma^\top\Gamma = (\sigma_{ij})$. Define the stochastic growth rate of the prey $\tilde a_{10} = a_{10} - \sigma_{11}/2$ and stochastic death rates $\tilde a_{j0} = a_{j0} + \sigma_{jj}/2$ for $j \ge 2$. For each $j$ the linear system

$$-a_{11}x_1 - a_{12}x_2 = -\tilde a_{10}, \qquad a_{i,i-1}x_{i-1} - a_{i,i+1}x_{i+1} = \tilde a_{i0}\ (2 \le i < j), \qquad a_{j,j-1}x_{j-1} = \tilde a_{j0}$$

has a unique solution $x^{(j)}$, and the **invasion rate** of predator $j+1$ into the community $(X_1,\dots,X_j)$ is $\mathcal{I}_{j+1} = -\tilde a_{j+1,0} + a_{j+1,j}\,x_j^{(j)}$, with $\mathcal{I}_1 = \tilde a_{10}$. Let $\tilde\kappa(j)$ be the Gard–Hallam quantity $\kappa(j)$ of the deterministic chain with each $a_{i0}$ replaced by $\tilde a_{i0}$; $x_j^{(j)}$, $\mathcal{I}_j$ and $\tilde\kappa(j)$ have the same sign.

**Theorem.** Assume $a_{11} > 0$ and $X(0)$ in the open orthant.
1. (Persistence.) If $\tilde\kappa(n) > 0$, the chain is time-average persistent in probability and

$$\lim_{t\to\infty}\frac1t\int_0^t \mathbb{E}\,X_k(s)\,ds = x_k^{(n)} > 0, \qquad k = 1,\dots,n.$$

If moreover $\Sigma$ is positive definite, the chain is strongly stochastically persistent: it has a unique invariant probability measure $\pi^{(n)}$ on the open orthant and converges to it in total variation, with $\mathbb{E}_{\pi}X_k = x_k^{(n)}$.
2. (Truncation of the chain.) If $\tilde\kappa(j^\ast) > 0$ and $\tilde\kappa(j^\ast + 1) \le 0$ for some $j^\ast < n$, the top predators $X_{j^\ast+1},\dots,X_n$ go extinct weakly in mean, while $X_1,\dots,X_{j^\ast}$ persist in time average with mean abundances $x^{(j^\ast)}$.
3. (Two species.) For $n = 2$: if $\mathcal{I}_1 \le 0$, almost surely $\frac1t\ln X_1 \to \tilde a_{10}$ and $\frac1t\ln X_2 \to -\tilde a_{20}$; if $\mathcal{I}_1 > 0$ and $\mathcal{I}_2 < 0$, the predator goes extinct exponentially fast at rate $\mathcal{I}_2$ and the prey's occupation measures converge to its stationary law.

## Expansion

The deterministic chain persists if and only if $\kappa(n) > 0$ (Gard and Hallam), and the stochastic result shows that noise acts exactly by lowering the prey's growth rate by $\sigma_{11}/2$ and raising each predator's death rate by $\sigma_{jj}/2$; correlations between noises do not matter. The key identity is that, on the support of any ergodic invariant measure, species present have zero Lyapunov exponent, $\lambda_i(\mu) = \int (f_i - \sigma_{ii}/2)\,d\mu = 0$, which, because the per-capita growth rates are linear in abundances, forces the mean abundances to solve the linear system above. Ergodic boundary measures can only live on faces $\{x_{l+1} = \dots = x_n = 0\}$ (a predator cannot survive without its prey), and the invasion rate of the next predator on such a face is $\mathcal{I}_{l+1}$. Since $\mathcal{I}_j$ does not depend on the coefficients of species above $j$, adding a top predator leaves the lower invasion rates unchanged, and each $\mathcal{I}_j$ is strictly decreasing in every noise variance, so environmental fluctuations shorten food chains.

## Sources

- Alexandru Hening, Dang H. Nguyen, "Stochastic Lotka–Volterra food chains", Journal of Mathematical Biology 77 (2018), 135–163, <https://doi.org/10.1007/s00285-017-1192-8>. Published version of arXiv:1703.04809, cited next; locators there refer to the arXiv version.
- Alexandru Hening, Dang H. Nguyen, "Stochastic Lotka-Volterra food chains", arXiv:1703.04809 (2017), Section 1 (models, Theorem 1.1, Definitions 1.1–1.5, Theorem 1.2, Remarks 1.3–1.5), Section 3 (Lemmas 3.2–3.6) and Section 4 (Lemma 4.1, Remark 4.1), <https://doi.org/10.48550/arXiv.1703.04809>.
