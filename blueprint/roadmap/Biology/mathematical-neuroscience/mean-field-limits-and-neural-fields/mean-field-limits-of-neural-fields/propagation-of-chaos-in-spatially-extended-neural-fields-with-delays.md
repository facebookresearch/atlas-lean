# Propagation of chaos in spatially extended neural fields with delays

**Setting.** Neurons are organized in $P(N)$ populations whose locations $r_\gamma$ (cortical position or feature, such as preferred orientation) are drawn i.i.d. from a law $\lambda$ on a compact set $\Gamma$. Population $\gamma$ has $N_\gamma(N)$ neurons. The state $X^{i,N}\in\mathbb R^d$ of neuron $i$ in population $\alpha$, for example a Hodgkin–Huxley or FitzHugh–Nagumo state, solves

$$dX^{i,N}_t=\Big(f(r_\alpha,t,X^{i,N}_t)+\frac1{P(N)}\sum_{\gamma=1}^{P(N)}\sum_{p(j)=\gamma}\frac1{N_\gamma}\,b\big(r_\alpha,r_\gamma,X^{i,N}_t,X^{j,N}_{t-\tau(r_\alpha,r_\gamma)}\big)\Big)dt+\sigma(r_\alpha)\,dW^i_t,$$

with space-dependent propagation delays $\tau(r,r')\le\tau$. Assume (H1)–(H5): $f$ and $b$ are uniformly Lipschitz in the state variables, $|b(r,r',x,z)|^2\le\tilde K(1+|x|^2)$, $|f(r,t,x)|^2\le C(1+|x|^2)$, and all coefficients are regular in the space variables. Assume also the *neural field limit*

$$\epsilon(N):=\frac1{P(N)}\sum_{\gamma=1}^{P(N)}\frac1{N_\gamma(N)}\to0 ,$$

which holds, for instance, when populations have comparable sizes and $P(N)=o(N)$.

**Theorem.**

1. For any square-integrable initial process, the network has a unique global strong solution. The *stochastic neural field mean-field equation*

$$d\bar X_t(r)=f(r,t,\bar X_t(r))\,dt+\sigma(r)\,dW_t(r)+\int_\Gamma\mathbb E_{\bar Z}\big[b\big(r,r',\bar X_t(r),\bar Z_{t-\tau(r,r')}(r')\big)\big]\,d\lambda(r')\,dt,$$

driven by a spatially chaotic Brownian field $W_t(r)$, with $\bar Z$ an independent copy of $\bar X$, has a unique solution on $[-\tau,T]$, measurable in $r$.
2. For almost every realization of the locations, each neuron $i$ of population $\alpha$ satisfies

$$\mathcal E\Big(\mathbb E\Big[\sup_{-\tau\le s\le T}\big|X^{i,N}_s-\bar X^i_s(r_\alpha)\big|^2\Big]\Big)=O\Big(\epsilon(N)+\frac1{P(N)}\Big).$$

For any fixed distinct neurons $i_1,\dots,i_l$, their joint law converges to $m(r_{p(i_1)})\otimes\cdots\otimes m(r_{p(i_l)})$ (propagation of chaos).

## Proof sketch

The proof is a coupling argument in the style of Sznitman. Each neuron is coupled with an independent copy of the mean-field process at its location, driven by the same Brownian motion. The error splits into a within-population averaging term of order $1/N_\gamma$, giving $\epsilon(N)$, and a Monte Carlo error from replacing $\int_\Gamma\cdot\,d\lambda$ by the empirical average over population locations, of order $1/P(N)$. Delays only add a history segment to the state. Neurons at different locations become independent, yet their laws vary in space. The noise in the limit is white in space, so the macroscopic dynamics is not a deterministic Wilson–Cowan/Amari equation unless the noise vanishes. For firing-rate neurons with Gaussian initial data, the mean-field solutions are Gaussian processes, so the law is described by deterministic integro-differential equations for their mean and covariance.

## Sources

- Jonathan Touboul, "Propagation of chaos in neural fields", *The Annals of Applied Probability* 24 (2014), 1298–1328, <https://doi.org/10.1214/13-aap950>. Preprint version: arXiv:1108.2414 (2011), Section 1 (network equations, neural field assumption, (H1)–(H5)), Proposition 1 (well-posedness of the network), Theorem 2 (well-posedness of the mean-field equation), Theorem 3 and Corollary 4 (convergence rate and propagation of chaos), Section 4 (reduction to neural field equations), <https://doi.org/10.48550/arXiv.1108.2414>.
