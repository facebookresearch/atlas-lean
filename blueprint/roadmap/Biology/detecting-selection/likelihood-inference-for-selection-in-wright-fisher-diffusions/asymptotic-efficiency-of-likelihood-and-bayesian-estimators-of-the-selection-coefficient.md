# Asymptotic efficiency of likelihood and Bayesian estimators of the selection coefficient

**Setting.** Observe continuously on $[0,T]$ a Wright–Fisher diffusion with selection and mutation,

$$dX_t=\tfrac12\bigl(sX_t(1-X_t)-\theta_2X_t+\theta_1(1-X_t)\bigr)\,dt+\sqrt{X_t(1-X_t)}\,dW_t,$$

where the mutation parameters $\theta_1,\theta_2>0$ are known and the selection coefficient $s$ lies in an open bounded set $\mathcal S\subset\mathbb R$. Both the neutral case $s=0$ and the non-neutral case are covered. The likelihood ratio is

$$\frac{d\mathbb P^{(s')}_\nu}{d\mathbb P^{(s)}_\nu}(X^T)=\frac{\nu(s',X_0)}{\nu(s,X_0)}\exp\Bigl\{(s'-s)\int_0^T\tfrac12\sqrt{X_t(1-X_t)}\,dW_t-\tfrac18(s'-s)^2\int_0^TX_t(1-X_t)\,dt\Bigr\}.$$

The maximum likelihood estimator is $\hat s_T=\arg\sup_{s\in\mathcal S}d\mathbb P^{(s)}_\nu/d\mathbb P^{(s_0)}_\nu$. The Bayesian estimator $\tilde s_T$ minimizes the integrated risk $\int_{\mathcal S}\mathbb E^{(s)}_\nu[\ell(\sqrt T(\bar s_T-s))]\,p(s)\,ds$. Here $p$ is a continuous prior with a polynomial majorant, and $\ell$ is an even, nonnegative loss with convex sublevel sets, continuous at $0$, $\ell(0)=0$, and with a polynomial majorant.

**Theorem.** Assume the initial densities $\nu(s,\cdot)$ are continuous in $s$ and satisfy mild tail and Hellinger-continuity conditions (all hold when $\nu=f_s$, the stationary density). Let $\bar s_T$ be either $\hat s_T$ or $\tilde s_T$, and set

$$I(s)=\tfrac14\,\mathbb E^{(s)}[\xi(1-\xi)],\qquad \xi\sim f_s(x)\propto e^{sx}x^{\theta_1-1}(1-x)^{\theta_2-1}.$$

Then, uniformly in $s$ on every compact $\mathcal K\subset\mathcal S$:

1. (Consistency.) $\lim_{T\to\infty}\sup_{s\in\mathcal K}\mathbb P^{(s)}_\nu[|\bar s_T-s|>\varepsilon]=0$ for every $\varepsilon>0$.
2. (Asymptotic normality.) $\sqrt T(\bar s_T-s)\to N(0,I(s)^{-1})$ in distribution.
3. (Moment convergence.) For every $p>0$, $\mathbb E^{(s)}_\nu|\sqrt T(\bar s_T-s)|^p\to\mathbb E|I(s)^{-1/2}\zeta|^p$ with $\zeta\sim N(0,1)$.
4. (Asymptotic efficiency.) For every admissible loss $\ell$ and every $s_0\in\mathcal S$,

$$\lim_{\delta\to0}\lim_{T\to\infty}\sup_{|s-s_0|<\delta}\mathbb E^{(s)}_\nu\bigl[\ell(\sqrt T(\bar s_T-s))\bigr]=\mathbb E\bigl[\ell(I(s_0)^{-1/2}\zeta)\bigr].$$

So the continuously observed path attains the Hájek–Le Cam minimax bound for selection inference. This is a benchmark that no estimator from discretely sampled frequencies can beat.

## Depends on

- [Uniform local asymptotic normality of the Wright–Fisher diffusion with selection and mutation](uniform-local-asymptotic-normality-of-the-wright-fisher-diffusion-with-selection-and-mutation.md)

## Expansion

The proof checks the Ibragimov–Has'minskii conditions for the normalized likelihood ratio $Z_{T,s}(u)$. Uniform LAN gives convergence of its marginals to $\exp\{u\Delta(s)-u^2I(s)/2\}$ with $\Delta(s)\sim N(0,I(s))$. The limit has a unique maximizer and a unique Bayes point. The remaining conditions are a Hölder bound on $\mathbb E|Z_{T,s}(u)^{1/m}-Z_{T,s}(v)^{1/m}|^m$ and an exponential bound on $\mathbb E\,Z_{T,s}(u)^{1/2}$. The standard route through a polynomial majorant of $1/\sigma^2$ fails here, because $\sigma^2(x)=x(1-x)$ vanishes at the boundaries. Instead these bounds are proved directly from the explicit drift, using uniform ergodicity of the additive functional $\int_0^TX_t(1-X_t)\,dt$.

## Sources

- Jaromir Sant, Paul A. Jenkins, Jere Koskela, Dario Spanò, "Convergence of Likelihood Ratios and Estimators for Selection in non-neutral Wright-Fisher Diffusions", arXiv:2001.03527 (2020), Section 3, Theorem 3.2 (main result) with Theorem 3.3, Corollary 3.4 and Propositions 3.5–3.7, <https://doi.org/10.48550/arXiv.2001.03527>.
