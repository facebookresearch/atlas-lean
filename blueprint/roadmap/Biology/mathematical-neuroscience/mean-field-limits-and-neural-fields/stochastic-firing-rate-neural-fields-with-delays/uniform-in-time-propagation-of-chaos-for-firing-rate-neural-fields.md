# Uniform-in-time propagation of chaos for firing-rate neural fields

**Setting.** A network of $N$ noisy firing-rate neurons split into $P(N)$ populations at locations $r_\gamma\in\Gamma$, neuron $i$ of population $\alpha$ obeying

$$
dV^{i,N}_t=\Big(-\frac{V^{i,N}_t}{\theta(r_\alpha)}+I(r_\alpha,t)+\sum_{\gamma=1}^{P(N)}J(r_\alpha,r_\gamma)\frac{1}{N_\gamma}\sum_{j=1}^{N_\gamma}S\big(r_\gamma,V^{j,N}_{t-\tau(r_\alpha,r_\gamma)}\big)\Big)dt+\Lambda(r_\alpha,t)\,dW^i_t+\sum_{\gamma=1}^{P(N)}\sigma(r_\alpha,r_\gamma)\frac{1}{N_\gamma}\sum_{j=1}^{N_\gamma}S\big(r_\gamma,V^{j,N}_{t-\tau(r_\alpha,r_\gamma)}\big)dB^i_t ,
$$

in the neural-field regime $\frac{1}{P(N)}\sum_\gamma \frac{1}{N_\gamma(N)}\to 0$, with chaotic (i.i.d. within populations) initial conditions. Let $\bar V^i$ be the coupled process: the solution of the mean-field equation driven by the same Brownian motions $W^i,B^i$ and the same initial condition as $V^i$.

**Theorem (Touboul 2011, Theorem 2; quantitative form in the appendix on uniform propagation of chaos).** Suppose $\theta(r)\in[\theta_m,\theta_M]$ with $0<\theta_m\le\theta_M<\infty$ and the sigmoid $S$ is Lipschitz in its voltage argument with constant $K_S$ satisfying

$$
K_S\le\sqrt{\frac{3\theta_M-2\theta_m}{3\theta_M\theta_m}} .
$$

Then there is a constant $C>0$, depending on the parameters but **not** on the time horizon $T$, such that for every $T>0$ and every neuron $i$ at location $r$,

$$
\sup_{0\le t\le T}\mathbb{E}\big[\,|V^i_t-\bar V^i_t|\,\big]\le\frac{C}{\sqrt N}.
$$

Consequently the long-time regimes of the mean-field equation (stationary or periodic solutions and their bifurcations) faithfully describe the large network, which a finite-horizon propagation-of-chaos result does not guarantee.

## Depends on

- [Gaussian moment equations of the stochastic firing-rate neural field](gaussian-moment-equations-of-the-stochastic-firing-rate-neural-field.md)

## Proof sketch

Subtract the variation-of-constants representations of $V^i$ and $\bar V^i$. The difference splits into four terms: two are Lipschitz differences of sigmoids (controlled by Cauchy–Schwarz and the Burkholder–Davis–Gundy inequality by $K_S^2$ times a delayed supremum of $\mathbb{E}|V^j-\bar V^j|^2$), and two are law-of-large-numbers fluctuations of i.i.d. coupled processes, of order $\frac{1}{P(N)}\sum_\gamma N_\gamma^{-1}+1/N$. The exponential damping $e^{-(t-s)/\theta(r)}$ from the linear leak lets a Gronwall argument on $\Delta_t e^{t/\tilde\theta}$ close uniformly in $t$ when the Lipschitz constant (and delay) is small compared with $1/\theta$.

## Sources

- Jonathan Touboul, "Mean-field equations for stochastic firing-rate neural fields with delays: Derivation and noise-induced transitions", *Physica D: Nonlinear Phenomena* 241 (2012), 1223–1244, <https://doi.org/10.1016/j.physd.2012.03.010>. Preprint version: arXiv:1108.2407 (2011), <https://doi.org/10.48550/arXiv.1108.2407>.
