# Mean-field equations with a Gaussian effective interaction process

**Network.** $N$ neurons are split into $P$ populations of sizes $N_1, \dots, N_P$, with $p(i)$ the population of neuron $i$. Neuron $i$ in population $\alpha$ has membrane potential $V_i$ obeying

$$dV_i(t) = \Bigl[ -\frac{V_i(t)}{\tau_\alpha} + \sum_{\beta=1}^{P} \sum_{j=1}^{N_\beta} J_{ij}\, S_\beta(V_j(t)) + I_\alpha(t) \Bigr] dt + f_\alpha\, dW_i(t),$$

where $S_\beta$ is a bounded sigmoidal rate function, $I_\alpha$ a bounded deterministic input, $f_\alpha > 0$ the noise amplitude and the $W_i$ independent Brownian motions. The weights are independent Gaussians with population-dependent scaling,

$$J_{ij} \sim \mathcal N\!\Bigl( \frac{\bar J_{\alpha\beta}}{N_\beta},\ \frac{\sigma_{\alpha\beta}^2}{N_\beta} \Bigr), \qquad i \in \alpha,\ j \in \beta,$$

so that the local field $\sum_{j \in \beta} J_{ij} S_\beta(V_j)$ has mean and variance independent of $N_\beta$.

**Effective interaction process.** For a Gaussian process $X = (X_1, \dots, X_P)$ with mean $\mu(t)$ and covariance $C(t,s)$, define $m_\beta^X(t) = \mathbb E[S_\beta(X_\beta(t))]$ and $\Delta_\beta^X(t,s) = \mathbb E[S_\beta(X_\beta(t)) S_\beta(X_\beta(s))]$, and let $U^X = (U^X_{\alpha\beta})$ be the Gaussian process with

$$\mathbb E[U^X_{\alpha\beta}(t)] = \bar J_{\alpha\beta}\, m_\beta^X(t), \qquad \operatorname{Cov}\bigl(U^X_{\alpha\beta}(t), U^X_{\gamma\delta}(s)\bigr) = \begin{cases} \sigma_{\alpha\beta}^2\, \Delta_\beta^X(t,s) & \alpha = \gamma,\ \beta = \delta, \\ 0 & \text{otherwise.} \end{cases}$$

These moments are explicit Gaussian integrals: with $Dx = (2\pi)^{-1/2} e^{-x^2/2} dx$,

$$m_\beta^X(t) = \int_{\mathbb R} S_\beta\bigl(x \sqrt{C_{\beta\beta}(t,t)} + \mu_\beta(t)\bigr)\, Dx,$$

and $\Delta_\beta^X(t,s)$ is the corresponding two-dimensional Gaussian integral over the bivariate law of $(X_\beta(t), X_\beta(s))$.

**Mean-field equation.** As $N \to \infty$, the law of one representative neuron per population converges to the law of the solution $V = (V_1, \dots, V_P)$ of

$$dV_\alpha(t) = \Bigl( -\frac{V_\alpha(t)}{\tau_\alpha} + \sum_{\beta=1}^{P} U^{V}_{\alpha\beta}(t) + I_\alpha(t) \Bigr) dt + f_\alpha\, dW_\alpha(t), \qquad \alpha = 1, \dots, P,$$

where $U^V$ is independent of the Brownian motions and its law is determined by the law of $V$ itself (a self-consistency, fixed-point equation on laws of processes). Taking expectations, the population means satisfy

$$\frac{d\mu_\alpha}{dt} = -\frac{\mu_\alpha}{\tau_\alpha} + \sum_{\beta} \bar J_{\alpha\beta} \int_{\mathbb R} S_\beta\bigl(x \sqrt{C_{\beta\beta}(t,t)} + \mu_\beta(t)\bigr)\, Dx + I_\alpha(t).$$

Only if $C_{\beta\beta}(t,t) = 0$ for all $t$ does this reduce to the classical neural-mass equation $\dot\mu_\alpha = -\mu_\alpha/\tau_\alpha + \sum_\beta \bar J_{\alpha\beta} S_\beta(\mu_\beta) + I_\alpha$, which therefore rests on the assumption that the average of $S_\beta$ over a population equals $S_\beta$ of the average potential.

## Expansion

Conditional on the potentials, the field $\eta_{i\beta} = \sum_{j \in \beta} J_{ij} S_\beta(V_j)$ is a sum of $N_\beta$ independent terms with mean $\bar J_{\alpha\beta} N_\beta^{-1} \sum_j S_\beta(V_j)$ and covariance $\sigma^2_{\alpha\beta} N_\beta^{-1} \sum_j S_\beta(V_j(t)) S_\beta(V_j(s))$; propagation of chaos replaces the empirical averages by expectations under the limiting law, which yields a Gaussian field with the stated mean and covariance. Because the covariance couples all pairs of times, the field remembers the whole past and the limit is non-Markovian. The general framework allows postsynaptic-potential shapes that are Green's functions of order-$k$ linear differential operators, which turns each population into a $kP$-dimensional linear SDE driven by $U^V$; the first-order leaky case shown here is $k = 1$.

## Sources

- O. Faugeras, J. Touboul, B. Cessac, "A constructive mean-field analysis of multi-population neural networks with random synaptic weights and stochastic inputs", Frontiers in Computational Neuroscience (2009), weight law (Eq. 18), Definition 2 (effective interaction process, Eq. 25), Proposition 1 (Eqs. 26–27), mean-field equation (Eq. 28) and its first-order case (Eqs. 32–33), naive mean-field equation (Eqs. 22–23). <https://doi.org/10.3389/neuro.10.001.2009> (PMC2649202).
