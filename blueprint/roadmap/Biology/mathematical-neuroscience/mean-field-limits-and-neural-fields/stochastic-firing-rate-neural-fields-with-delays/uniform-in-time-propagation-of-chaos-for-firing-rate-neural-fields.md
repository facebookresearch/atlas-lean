# Uniform-in-time propagation of chaos for firing-rate neural fields

**Setting.** A network of $N$ noisy firing-rate neurons split into $P(N)$ populations at locations $r_\gamma\in\Gamma$, neuron $i$ of population $\alpha$ obeying

$$
dV^{i,N}_t=\Big(-\frac{V^{i,N}_t}{\theta(r_\alpha)}+I(r_\alpha,t)+\sum_{\gamma=1}^{P(N)}J(r_\alpha,r_\gamma)\frac{1}{N_\gamma}\sum_{j=1}^{N_\gamma}S\big(r_\gamma,V^{j,N}_{t-\tau(r_\alpha,r_\gamma)}\big)\Big)dt+\Lambda(r_\alpha,t)\,dW^i_t+\sum_{\gamma=1}^{P(N)}\sigma(r_\alpha,r_\gamma)\frac{1}{N_\gamma}\sum_{j=1}^{N_\gamma}S\big(r_\gamma,V^{j,N}_{t-\tau(r_\alpha,r_\gamma)}\big)dB^i_t ,
$$

in the neural-field regime $\frac{1}{P(N)}\sum_\gamma \frac{1}{N_\gamma(N)}\to 0$, with chaotic (i.i.d. within populations) initial conditions. Let $\bar V^i$ be the coupled process: the solution of the mean-field equation driven by the same Brownian motions $W^i,B^i$ and the same initial condition as $V^i$.

**Theorem (Touboul 2011, Theorem 2; quantitative form in the appendix on uniform propagation of chaos, with the coupling strengths restored).** Suppose $\theta(r)\le\theta_M<\infty$, the sigmoid $S$ is Lipschitz in its voltage argument with constant $K_S$, and, with $\|J\|_\infty=\sup_\alpha\sum_\gamma|J(r_\alpha,r_\gamma)|$ and $\|\sigma\|_\infty=\sup_\alpha\sum_\gamma|\sigma(r_\alpha,r_\gamma)|$ (bounded uniformly in $N$),

$$
\kappa:=4K_S^2\,\theta_M\Big(\theta_M\|J\|_\infty^2+\tfrac12\|\sigma\|_\infty^2\Big)<1 .
$$

Then there is a constant $C>0$, depending on the parameters but **not** on the time horizon $T$, such that for every $T>0$ and every neuron $i$ at location $r$,

$$
\sup_{0\le t\le T}\mathbb{E}\big[\,|V^i_t-\bar V^i_t|\,\big]\le\frac{C}{\sqrt N}.
$$

Consequently the long-time regimes of the mean-field equation (stationary or periodic solutions and their bifurcations) faithfully describe the large network, which a finite-horizon propagation-of-chaos result does not guarantee. A condition on $K_S$ and $\theta$ alone, as printed in the source's Theorem 6, does not suffice: with $\theta\equiv1$, $S=\Phi$ ($K_S\approx0.399$), $J\equiv10$, $\sigma=\tau=0$, $I=-5$ and $\Lambda=0.1$, the mean dynamics have slope about $3.98$ at the symmetric state, which is unstable, and the network leaves it in times of order $\log N$ while the mean-field solution does not.

## Depends on

- [Gaussian moment equations of the stochastic firing-rate neural field](gaussian-moment-equations-of-the-stochastic-firing-rate-neural-field.md)

## Proof depends on

- [Gronwall inequality (integral form)](../../../../Analysis/ordinary-differential-equations/gronwall-inequality/gronwall-inequality-integral-form.md)

## Proof sketch

Subtract the variation-of-constants representations of $V^i$ and $\bar V^i$. The difference splits into four terms: two are Lipschitz differences of sigmoids (controlled by Cauchy–Schwarz and the Burkholder–Davis–Gundy inequality by $K_S^2$ times a delayed supremum of $\mathbb{E}|V^j-\bar V^j|^2$), and two are law-of-large-numbers fluctuations of i.i.d. coupled processes, of order $\frac{1}{P(N)}\sum_\gamma N_\gamma^{-1}+1/N$. With $m_t=\sup_j\sup_{u\le t}\mathbb E|V^j_u-\bar V^j_u|^2$, which is finite for each $t$ by the finite-horizon (Gronwall) estimate and vanishes for $t\le0$ since both processes share the initial segment, the exponential damping $e^{-(t-s)/\theta(r)}$ from the linear leak bounds the two Lipschitz terms by $\theta_M^2\|J\|_\infty^2K_S^2m_t$ and $\tfrac12\theta_M\|\sigma\|_\infty^2K_S^2m_t$, delays included. Hence $m_t\le\kappa m_t+\varepsilon_N$, where $\varepsilon_N$ is the time-uniform size of the fluctuation terms, so $m_t\le\varepsilon_N/(1-\kappa)$ for all $t$. The coupling strengths $\|J\|_\infty$ and $\|\sigma\|_\infty$ multiply $K_S$ in these terms and cannot be dropped from the condition.

## Sources

- Jonathan Touboul, "Mean-field equations for stochastic firing-rate neural fields with delays: Derivation and noise-induced transitions", *Physica D: Nonlinear Phenomena* 241 (2012), 1223–1244, <https://doi.org/10.1016/j.physd.2012.03.010>. Preprint version: arXiv:1108.2407 (2011), <https://doi.org/10.48550/arXiv.1108.2407>.
