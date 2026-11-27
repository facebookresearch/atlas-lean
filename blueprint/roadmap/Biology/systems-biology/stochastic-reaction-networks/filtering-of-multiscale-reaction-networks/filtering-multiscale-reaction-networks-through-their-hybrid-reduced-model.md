# Filtering multiscale reaction networks through their hybrid reduced model

**Model.** An intracellular network with species $S_1, \dots, S_n$ and reactions $v_{\cdot j} \to v'_{\cdot j}$ ($j = 1, \dots, r$) with rate constants $k_j$ evolves under stochastic mass action,

$$X(t) = X(0) + \sum_{j=1}^r (v'_{\cdot j} - v_{\cdot j})\, R_j\Big(\int_0^t \lambda_j(X(s))\,ds\Big),$$

with independent unit-rate Poisson processes $R_j$. For a scaling parameter $N$, species abundances scale as $N^{\alpha_i}$ and rate constants as $N^{\beta_j}$; set $X^N_i = N^{-\alpha_i}X_i$, $\tilde\rho_j = \beta_j + v_{\cdot j}^\top\alpha$, and let $\gamma_1 = \min_i\big(\alpha_i - \max_{j \in \Gamma_i^+\cup\Gamma_i^-}\tilde\rho_j\big)$ be the fastest time scale, $X^{N,\gamma_1}(t) = X^N(tN^{\gamma_1})$. The **hybrid reduced model** $X^{\gamma_1}$ drops slow reactions ($\gamma_1 + \tilde\rho_j < 0$), replaces fast reactions ($\gamma_1 + \tilde\rho_j > 0$) by their deterministic flux, and keeps reactions with $\gamma_1 + \tilde\rho_j = 0$ as Poisson jumps, a piecewise-deterministic process. Observations at times $t_1 < t_2 < \cdots$ are

$$Y_\ell(t_i) = h_\ell\big(X^{N,\gamma_1}(t_i)\big) + W_\ell(t_i), \qquad \ell = 1, \dots, m,$$

with bounded Lipschitz $h_\ell$ (e.g. saturating fluorescence of a reporter) and i.i.d. standard Gaussian noise. The filter is $\pi^{N,\gamma_1}_{t_i}(\phi) = \mathbb{E}[\phi(X^{N,\gamma_1}(t_i)) \mid Y(t_1), \dots, Y(t_i)]$.

**Theorem.** Assume $\lim_N X^N(0)$ exists and both the full and the reduced processes are non-explosive. Let $\tilde\pi^{N,\gamma_1}_{t_i}(\phi)$ be the filter computed with the reduced model's dynamics but fed the true observations $Y(t_1{:}t_i)$. Then for every $i \ge 1$ and every bounded continuous $\phi$,

$$\pi^{N,\gamma_1}_{t_i}(\phi) - \tilde\pi^{N,\gamma_1}_{t_i}(\phi) \longrightarrow 0 \quad \text{in probability as } N \to \infty.$$

**Corollary (reduced-model particle filter).** Let $\bar\pi^{\gamma_1}_{M,t_i}(\phi)$ be the bootstrap particle filter with $M$ particles that simulates only the reduced model, weights by the Gaussian observation likelihood, and resamples by multinomial branching. Then for every $\delta > 0$,

$$\lim_{N\to\infty}\lim_{M\to\infty}\mathbb{P}\Big(\big|\bar\pi^{\gamma_1}_{M,t_i}(\phi) - \pi^{N,\gamma_1}_{t_i}(\phi)\big| > \delta\Big) = 0.$$

So the latent molecular state of a stiff multiscale network can be tracked from reporter time courses by simulating the much cheaper hybrid model, without loss of accuracy in the large-$N$ limit.

## Expansion

By the Kang–Kurtz separation-of-time-scales theorem, $X^{N,\gamma_1} \Rightarrow X^{\gamma_1}$ in the Skorokhod topology on finite intervals, hence at finitely many observation times. The filter is a ratio of expectations under a reference measure in which observations are independent standard Gaussians, via the Kallianpur–Striebel formula with likelihood weights $\prod_j g(X(t_j), Y(t_j))$; because $h$ is bounded and continuous these weights are bounded continuous functionals of the path at the observation times, so weak convergence of the state transfers to the numerator and denominator, and the denominator stays bounded away from $0$. The particle-filter statement combines this with the classical almost-sure convergence of branching particle filters as $M \to \infty$.

## Sources

- Zhou Fang, Ankit Gupta and Mustafa Khammash, "Stochastic filters based on hybrid approximations of multiscale stochastic reaction networks", 2020 59th IEEE Conference on Decision and Control (CDC) (2020), 4616–4621, <https://doi.org/10.1109/cdc42340.2020.9304194>; numbering as in arXiv:2008.11682: Section on model reduction via time-scale separation (scaled dynamics and reduced model), observation model, Theorem 1, Corollary 1, Proposition 1 and Corollary 2.
