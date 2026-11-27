# Langevin synaptic sampling and its posterior stationary distribution

**Setting.** A network with continuous parameters $\theta = (\theta_1, \dots, \theta_M)$ (synaptic weights, possibly also other plasticity variables) models inputs $\mathbf x = (x_1, \dots, x_N)$ through a generative model $p_{\mathcal N}(\mathbf x \mid \theta)$, and $p_{\mathcal S}(\theta)$ is a prior on the parameters (structural constraints such as sparsity or bounded weights). The posterior is $p(\theta \mid \mathbf x) \propto p_{\mathcal S}(\theta)\, p_{\mathcal N}(\mathbf x \mid \theta)$.

**Dynamics.** Fix a temperature $T > 0$ and a sampling-speed function $b > 0$. Each parameter evolves by the Itô stochastic differential equation

$$d\theta_i = \Bigl( b(\theta_i)\, \frac{\partial}{\partial \theta_i} \log p_{\mathcal S}(\theta) + b(\theta_i)\, \frac{\partial}{\partial \theta_i} \log p_{\mathcal N}(\mathbf x \mid \theta) + T\, b'(\theta_i) \Bigr) dt + \sqrt{2 T\, b(\theta_i)}\; dW_i, \qquad i = 1, \dots, M,$$

with independent standard Wiener processes $W_i$.

**Theorem.** Let $p(\mathbf x, \theta)$ be a strictly positive, continuous probability distribution, twice continuously differentiable in $\theta$, and let $b$ be strictly positive and twice continuously differentiable. Then the dynamics above leaves invariant the tempered posterior

$$p^*(\theta) = \frac{1}{\mathcal Z}\, p(\theta \mid \mathbf x)^{1/T}, \qquad \mathcal Z = \int p(\theta \mid \mathbf x)^{1/T}\, d\theta,$$

and $p^*$ is the unique stationary distribution of the sampling dynamics. For $T = 1$ and constant $b$ the stationary law is exactly the posterior $p(\theta \mid \mathbf x)$; larger $T$ flattens it.

## Expansion

Because the coordinates decouple in the diffusion term, it suffices to check stationarity of the Fokker–Planck equation coordinate by coordinate. With drift $A_i = b(\theta_i)\, \partial_i \log p(\theta \mid \mathbf x) + T b'(\theta_i)$ and diffusion coefficient $D_i = T b(\theta_i)$, the stationary probability current $A_i \pi - \partial_i (D_i \pi)$ vanishes when $b\, \partial_i \log p(\theta \mid \mathbf x)\, \pi = T b\, \partial_i \pi$, that is $\partial_i \log \pi = T^{-1} \partial_i \log p(\theta \mid \mathbf x)$, which gives $\pi \propto p(\theta \mid \mathbf x)^{1/T}$. The correction term $T b'(\theta_i)$ is exactly what allows a parameter-dependent sampling speed (for example slowing very large or very small weights) without moving the stationary distribution. Strict positivity of the target gives uniqueness. In the online version the log-likelihood gradient is replaced by $N$ times the gradient for the currently presented input, which approximates the batch dynamics when the sampling speed is small relative to one sweep through the data.

## Sources

- D. Kappel, S. Habenschuss, R. Legenstein, W. Maass, "Network Plasticity as Bayesian Inference", PLoS Computational Biology (2015), Methods, "Learning a posterior distribution through stochastic synaptic plasticity", Eqs. (12)–(14) and Theorem 1; online approximation Eqs. (15)–(18). <https://doi.org/10.1371/journal.pcbi.1004485> (PMC4636322).
