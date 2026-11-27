# Crow-Kimura replicator-mutator limit of the Zakai filtering equation

**Setting.** A hidden signal and its observation solve

$$dX_t=g(X_t)\,dt+\Sigma^{1/2}dW_t,\qquad dZ_t=h(X_t)\,dt+\Xi^{1/2}dB_t,$$

with $g:\mathbb{R}^m\to\mathbb{R}^m$, $h:\mathbb{R}^m\to\mathbb{R}^n$ of class $C^2$, globally Lipschitz with linear growth, and $\Sigma,\Xi$ positive definite. Let $\mathcal{L}^*$ be the Fokker-Planck operator of the signal, playing the role of mutation. Replace the observation path by its piecewise linear interpolation $Z^d$ on a grid of mesh $\delta_d=T/d$. Interpreting a type $x$ as a hypothesis, the unnormalized *Crow-Kimura replicator-mutator equation with time-varying fitness* is, for constants $r>0$, $s<r$,

$$\partial_t\mu^d_t(x)=\mathcal{L}^*\mu^d_t(x)-\frac r2\Big\|h(x)-\frac{dZ^d_t}{dt}\Big\|^2_{\Xi}\mu^d_t(x)+s\Big\langle h(x)-\frac{dZ^d_t}{dt},\,h(z)-\frac{dZ^d_t}{dt}\Big\rangle_{\Xi}\mu^d_t(x)\ \text{averaged over }z\sim\mu^d_t ,$$

where $\|v\|^2_\Xi=v^\top\Xi^{-1}v$: fitness is a Gaussian log-likelihood of the current observation increment ($s=0$), plus a frequency-dependent term ($s\neq0$).

**Statement.** Let $q_t$ solve the modified Zakai equation (Itô form)

$$dq_t=\mathcal{L}^*q_t\,dt-\frac s2h^\top\Xi^{-1}h\,q_t\,dt+(r-s)\,q_t\,h^\top\Xi^{-1}dZ_t,$$

with $q_0=\mu^d_0=f$ a bounded smooth probability density. Then for every $T>0$ and $p\ge1$,

$$\lim_{d\to\infty}\mathbb{E}\Big[\sup_{0\le t\le T}|\mu^d_t(x)-q_t(x)|^p\Big]=0\qquad\text{for all }x,$$

provided $r-s$ is below an explicit bound depending on $T$, $p$, the growth constant of $h$ and $\Xi$. For $r=1$, $s=0$ the limit is the standard Zakai equation, whose normalization is the Kushner-Stratonovich equation for the posterior density of $X_t$ given $(Z_u)_{u\le t}$: the normalized replicator-mutator dynamics converge to exact Bayesian filtering. With $s\ne0$ in the linear-Gaussian case the limit corresponds to an ensemble Kalman-Bucy filter with covariance inflation, which helps under model misspecification.

## Expansion

With a smooth observation path, the replicator-mutator PDE is a parabolic equation with a potential that contains $dZ^d/dt$, and the Wong-Zakai principle says that smooth approximations of the driving noise converge to the Stratonovich integral. Expanding $-\tfrac r2\|h-\dot Z^d\|^2_\Xi$ gives $r\,h^\top\Xi^{-1}\dot Z^d$ minus terms quadratic in $h$, and the $\|\dot Z^d\|^2$ part is independent of $x$ and disappears on normalization; the Stratonovich-to-Itô correction of the $h\,dZ$ term cancels part of the quadratic term, yielding the Zakai form. The proof uses Kunita's forward Feynman-Kac representation of stochastic PDEs and moment bounds that require the condition on $r-s$.

## Sources

- Sahani Pathiraja and Philipp Wacker, "Connections between sequential Bayesian inference and evolutionary dynamics", Philos. Trans. R. Soc. A 383 (2025), 20240241, <https://doi.org/10.1098/rsta.2024.0241>. Numbering follows the arXiv version, arXiv:2411.16366 (2024): Section 3 (Theorem 3.1) and Theorem A.1 (forward representation formula, quoted there from earlier work), <https://doi.org/10.48550/arXiv.2411.16366>.
