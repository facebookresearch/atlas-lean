# Existence and uniqueness of solutions of the random-network mean-field equations

**Statement.** Work on a finite horizon $[t_0, T]$ with the multi-population mean-field equation written as a $kP$-dimensional linear SDE driven by the effective interaction process,

$$d\tilde V(t) = \bigl( -L(t)\, \tilde V(t) + \tilde U^{V}_t + \tilde I(t) \bigr) dt + F(t)\, dW_t,$$

and define the map $\mathcal F_k$ on laws of continuous Gaussian processes by

$$\mathcal F_k(X)_t = \Phi_L(t, t_0)\, Z_0 + \int_{t_0}^{t} \Phi_L(t,s)\bigl(\tilde U^X_s + \tilde I(s)\bigr)\, ds + \int_{t_0}^{t} \Phi_L(t,s)\, F(s)\, dW_s,$$

where $\Phi_L$ is the fundamental matrix of $-L$. Assume the rate functions $S_\beta$ are bounded with bounded derivatives, the inputs are bounded ($\sup_t |I_\alpha(t)| \le I_{\max}$), and the singular values of the noise matrix $F(u)$ are bounded below by $\lambda^{\Gamma}_{\min} > 0$.

**Theorem.** For every nondegenerate $kP$-dimensional Gaussian initial condition $Z_0$, independent of the Brownian motion, and every initial Gaussian process $X$ with $X(t_0) = Z_0$, the map $\mathcal F_k$ has a unique fixed point in the space of laws on $C([t_0, T], \mathbb R^{kP})$, and the iterates $\mathcal F_k^{(n)}(X)$ converge in law to it. The fixed point is the unique solution of the mean-field equations, and the proof is constructive (Picard iteration on mean and covariance functions).

## Depends on

- [Mean-field equations with a Gaussian effective interaction process](mean-field-equations-with-a-gaussian-effective-interaction-process.md)

## Expansion

Every iterate is Gaussian, so it suffices to control means $\mu_n$ and covariances $C_n$. Kolmogorov's moment criterion, together with the bounds $\|\mathbb E[U^X \cdot 1]\|_\infty \le \max_\alpha \sum_\beta |\bar J_{\alpha\beta}| \|S_\beta\|_\infty$ and a uniform bound on the covariance of $U^X$, gives uniform tightness of the sequence. The noise keeps the variances uniformly positive ($C^n_{\alpha\alpha}(t,t) \ge k_0 > 0$) and makes $C^n_{\alpha\alpha}(s,s) C^n_{\alpha\alpha}(t,t) - C^n_{\alpha\alpha}(t,s)^2 \ge c\,|t-s|$, which controls the derivatives of the Gaussian integrals defining $m^X$ and $\Delta^X$. The mean value theorem then bounds $\|C_{n+1} - C_n\|_\infty$ and $\|\mu_{n+1} - \mu_n\|_\infty$ by iterated integrals of earlier differences; these are at most $k^n/(n-1)!$, so both sequences are Cauchy in the uniform norm. Convergence of means and covariances plus tightness gives convergence in law to a Gaussian limit, which is a fixed point; the same estimates applied to two fixed points show they have equal means and covariances. Under a contraction assumption on $L$ the construction extends to $(-\infty, T]$, giving stationary solutions.

## Sources

- O. Faugeras, J. Touboul, B. Cessac, "A constructive mean-field analysis of multi-population neural networks with random synaptic weights and stochastic inputs", Frontiers in Computational Neuroscience (2009), Definition 4 (map $\mathcal F_k$), Lemma 1, Theorems 1–3 (Gaussian convergence criterion, Kolmogorov tightness, uniform tightness), Lemmas 2–5 and Proposition 3, Theorem 4 (existence and uniqueness); Propositions 4–5 (stationary case). <https://doi.org/10.3389/neuro.10.001.2009> (PMC2649202).
