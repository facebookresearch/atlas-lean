# Survival-conditioned likelihood inference for composite birth–death processes

**Model.** Let $(X_t)$ be a continuous-time birth–death chain on $\{0,1,\dots,N\}$ with absorbing state $0$, birth rate from $k$ equal to a sum of $K\ge 2$ mechanisms

$$
\lambda_k(\boldsymbol\beta) = \sum_{i=1}^K \beta_i f_i(k),\qquad f_i(0) = f_i(N) = 0,
$$

and death rate $\mu_k = \mu\, r(k)$ with $r(0) = 0<r(k)$ for $k\ge1$; the $f_i,r$ are known and $\boldsymbol\theta = (\beta_1,\dots,\beta_K,\mu)$ lies in an open $\Theta\subset(0,\infty)^{K+1}$. The motivating case is the simplicial SIS epidemic on the complete hypergraph, where every infected $i$-tuple infects each susceptible at rate $\beta_i$: $f_i(k) = \binom{k}{i}(N-k)$, $r(k) = k$. The path $(X_t)_{0\le t\le T}$ is observed continuously, but births are **unmarked**: the mechanism behind each upward jump is latent.

**$Q$-process.** Observed outbreaks are those that survive, so the target law is $\mathbb{P}_{\boldsymbol\theta}(\cdot\mid\tau_0>T)$, which is not time-homogeneous. Assume the generator $Q^+(\boldsymbol\theta)$ killed at $0$ is irreducible on $\{1,\dots,N\}$, with Perron eigenvalue $\gamma(\boldsymbol\theta)<0$, right eigenvector $h_{\boldsymbol\theta}>0$ and left eigenvector $v_{\boldsymbol\theta}>0$, $v^{\mathsf T}h = 1$. The Doob $h$-transform gives a birth–death chain on $\{1,\dots,N\}$ with tilted rates

$$
\widetilde\lambda_k = \lambda_k(\boldsymbol\beta)\,\frac{h_{\boldsymbol\theta}(k+1)}{h_{\boldsymbol\theta}(k)},\qquad
\widetilde\mu_k = \mu\, r(k)\,\frac{h_{\boldsymbol\theta}(k-1)}{h_{\boldsymbol\theta}(k)}\quad(h_{\boldsymbol\theta}(0) = 0),
$$

which is ergodic with stationary law $\widetilde\pi_{\boldsymbol\theta}(k) = v_{\boldsymbol\theta}(k)h_{\boldsymbol\theta}(k)$ (the quasi-stationary-type limit), and whose law agrees asymptotically with the survival-conditioned law on every fixed time window as $T\to\infty$.

**Estimators.** The conditional MLE $\widetilde{\boldsymbol\theta}_T$ solves the full score equation of the $Q$-process likelihood; since the tilts depend on all of $\boldsymbol\theta$, both birth and death martingales enter every score component. The QMLE $\bar{\boldsymbol\theta}_T$ drops the derivatives of the tilt factors, using the working weights $\boldsymbol f(k)/(\boldsymbol\beta^{\mathsf T}\boldsymbol f(k))$ against the birth martingale and $1/\mu$ against the death martingale, with the tilted intensities kept in the compensators.

**Theorem (asymptotics).** Assume the tilted intensities identify $\boldsymbol\theta$. Let

$$
\mathcal I_{ab} = \sum_{k=1}^{N-1}\widetilde\pi(k)\widetilde\lambda_k\,\partial_a\log\widetilde\lambda_k\,\partial_b\log\widetilde\lambda_k + \sum_{k=2}^{N}\widetilde\pi(k)\widetilde\mu_k\,\partial_a\log\widetilde\mu_k\,\partial_b\log\widetilde\mu_k
$$

be the Fisher information and $\mathcal G = \mathcal H^{\mathsf T}\mathcal J^{-1}\mathcal H$ the Godambe information of the working score. If $\mathcal I(\boldsymbol\theta_0)$ is positive definite, then any root of the score equation in a small compact neighbourhood of $\boldsymbol\theta_0$ satisfies, under the $Q$-process law,

$$
\widetilde{\boldsymbol\theta}_T\to\boldsymbol\theta_0 \text{ in probability},\qquad \sqrt T(\widetilde{\boldsymbol\theta}_T - \boldsymbol\theta_0)\Rightarrow\mathcal N\big(0,\mathcal I(\boldsymbol\theta_0)^{-1}\big);
$$

if $\mathcal G(\boldsymbol\theta_0)$ is positive definite, the same holds for $\bar{\boldsymbol\theta}_T$ with covariance $\mathcal G(\boldsymbol\theta_0)^{-1}$. By contrast, the naive MLE computed from surviving trajectories under the unconditional law is biased.

## Expansion

Each score is a stochastic integral against the compensated birth and death counting martingales of the $Q$-process, whose brackets vanish across types. Ergodicity of the finite-state $Q$-process gives $\frac1T\langle U\rangle_T\to\mathcal I$ almost surely and a uniform law of large numbers for the normalized log-likelihood on compacts (consistency); the martingale central limit theorem gives normality. For the QMLE the sensitivity matrix $\mathcal H$ is not block-diagonal, because the tilts couple birth and death parameters, while $\mathcal J$ is, giving the sandwich covariance. Unmarked births make the problem a deconvolution in event space: the one-dimensional state carries information on each $\beta_i$ only through how $\lambda_k$ varies with $k$, which shows up as a strong negative correlation between $\widetilde\beta_1$ and $\widetilde\beta_2$.

## Sources

- M. Lalovic, N. Georgiou, I. Z. Kiss, "Likelihood-based inference for birth-death processes with composite birth mechanisms", arXiv:2604.20422 (2026), Section 2 (model), Section 4 (Doob $h$-transform, Assumption 4.1), Section 5 (scores, Fisher and Godambe information) and Theorems 6.5 and 6.6 with Assumptions 6.1–6.3, <https://doi.org/10.48550/arXiv.2604.20422>.
