# Crow-Kimura replicator-mutator limit of the Zakai filtering equation

**Setting.** A hidden signal and its observation solve

$$dX_t=g(X_t)\,dt+\Sigma^{1/2}dW_t,\qquad dZ_t=h(X_t)\,dt+\Xi^{1/2}dB_t,$$

with $g:\mathbb{R}^m\to\mathbb{R}^m$, $h:\mathbb{R}^m\to\mathbb{R}^n$ of class $C^2$, globally Lipschitz with linear growth, and $\Sigma,\Xi$ positive definite. Let $\mathcal{L}^*$ be the Fokker-Planck operator of the signal, playing the role of mutation, and let $x^*_t$ be the reference (true) hidden trajectory that generates the observations, $dZ_t=h(x^*_t)\,dt+\Xi^{1/2}dB_t$. On the grid $t_i=i\delta_d$ of mesh $\delta_d=T/d$, smooth only the observation *noise*: replace $B$ by its piecewise linear interpolation at the grid points and keep the drift frozen at the grid points, that is, ((3.3) of the source)

$$\frac{dZ^d_t}{dt}=h(x^*_{t_i})+\Xi^{1/2}\,\frac{B_{t_{i+1}}-B_{t_i}}{\delta_d},\qquad t\in[t_i,t_{i+1}).$$

This is not the piecewise linear interpolation of the observation path $Z$ itself (which would use $\delta_d^{-1}\int_{t_i}^{t_{i+1}}h(x^*_u)\,du$ as drift). Interpreting a type $x$ as a hypothesis, the *Crow-Kimura replicator-mutator equation with time-varying fitness* is, for constants $r>0$, $s<r$,

$$\partial_t\rho_t(x)=\mathcal{L}^*\rho_t(x)+\rho_t(x)\Big(\mathbb{E}_{z\sim\rho_t}[f_t(x,z)]-\mathbb{E}_{x'\sim\rho_t,\,z\sim\rho_t}[f_t(x',z)]\Big),$$

$$f_t(x,z)=-\frac r2\Big\|h(x)-\frac{dZ^d_t}{dt}\Big\|^2_{\Xi}+s\Big\langle h(x)-\frac{dZ^d_t}{dt},\,h(z)-\frac{dZ^d_t}{dt}\Big\rangle_{\Xi},$$

where $\|v\|^2_\Xi=v^\top\Xi^{-1}v$ and $\langle v,w\rangle_\Xi=v^\top\Xi^{-1}w$: fitness is a Gaussian log-likelihood of the current observation increment ($s=0$), plus a frequency-dependent term ($s\neq0$). The theorem concerns the *linear* equation ((3.7) of the source, restated as (5.3) at the start of the proof)

$$\partial_t\mu^d_t(x)=\mathcal{L}^*\mu^d_t(x)+\Big(-\frac r2\,h(x)^\top\Xi^{-1}h(x)+(r-s)\,h(x)^\top\Xi^{-1}\frac{dZ^d_t}{dt}\Big)\mu^d_t(x).$$

*Relation to the Crow-Kimura equation.* For $s=0$ the fitness depends on $x$ alone, and $-\frac r2\|h(x)-\frac{dZ^d_t}{dt}\|^2_\Xi$ differs from the coefficient of $\mu^d_t$ above only by the $x$-independent term $-\frac r2\|\frac{dZ^d_t}{dt}\|^2_\Xi$; hence $\rho_t=\mu^d_t/\int\mu^d_t$ solves the Crow-Kimura equation, i.e. $\mu^d$ is an unnormalized Crow-Kimura solution. For $s\neq0$ this identification is not available: the $x$-dependent part of the fitness in the normalized Crow-Kimura equation ((3.6) of the source) is $-\frac r2h^\top\Xi^{-1}h+(r-s)h^\top\Xi^{-1}\frac{dZ^d_t}{dt}+s\,h(x)^\top\Xi^{-1}\mathbb{E}_{\rho_t}[h]$, so it carries the extra term $s\,h(x)^\top\Xi^{-1}\mathbb{E}_{\rho_t}[h]$ that normalizing the linear equation does not produce (for $h(x)=x$, $\Xi=1$ the two differ by $s\,\mathbb{E}_{\rho_t}[x]\,x$). The source's Lemma 3.1 asserts that the linear equation is the unnormalized form of (3.6), but its proof derives only (3.6). For $s\neq0$ the theorem below is therefore a statement about the linear equation, not about the Crow-Kimura dynamics. The unnormalized equation displayed in the statement of the source's Theorem 3.1, (3.12), is also not the equation used in the proof: it contains the additional $x$-independent term $-(\frac r2-s)\|\frac{dZ^d_t}{dt}\|^2_\Xi\,\mu^d_t$, whose time integral is of order $nT/\delta_d\to\infty$ (for $r=1$, $s=0$, $h\equiv0$ its solution tends to $0$ while $q_t=e^{t\mathcal{L}^*}f>0$).

**Statement.** Let $q_t$ solve the modified Zakai equation, in Stratonovich form ((5.4) of the source)

$$dq_t=\mathcal{L}^*q_t\,dt-\frac r2h^\top\Xi^{-1}h\,q_t\,dt+(r-s)\,q_t\,h^\top\Xi^{-1}\circ dZ_t,$$

equivalently, since $d\langle Z\rangle_t=\Xi\,dt$, in Itô form

$$dq_t=\mathcal{L}^*q_t\,dt-\tfrac12\big[r-(r-s)^2\big]h^\top\Xi^{-1}h\,q_t\,dt+(r-s)\,q_t\,h^\top\Xi^{-1}dZ_t,$$

with $q_0=\mu^d_0=f$ a bounded smooth probability density, and let $\mu^d$ solve the linear equation above. Fix a realised reference signal path $x^*_t$ on $[0,T]$, and let $\mathbb{E}_B$ denote expectation with respect to the observation noise $B$ alone (with $x^*$ held fixed). Then for every $T>0$ and $p\ge1$ such that $\int |x|^{\max(2,p)} f(x)\,dx < \infty$ (finite second moment for (5.9) and finite $p$-th moment when $p>2$),

$$\lim_{d\to\infty}\mathbb{E}_B\Big[\sup_{0\le t\le T}|\mu^d_t(x)-q_t(x)|^p\Big]=0\qquad\text{for all }x,$$

provided there exist conjugate exponents $r_1, r_2 > 1$ ($1/r_1 + 1/r_2 = 1$) such that $\tfrac12 r_1 r_2 (r-s) p \lambda_{\Xi}^2 < 1/K(T)$, where $K(T)$ is the explicit horizon-dependent constant of (5.9) in the source depending on $T$, $p$, the coefficients of $g$ and $h$, $\Sigma$, $\Xi$, and the finite second moment of the initial density $f$. The Itô form printed in the source's statement of Theorem 3.1, (3.13), has drift $-\frac s2h^\top\Xi^{-1}h\,q_t$; it agrees with the Stratonovich form (5.4) used in the proof only when $(r-s)(r-s-1)=0$, so it is a misprint in general; (5.4) is the Wong-Zakai limit of the linear equation. For $s=0$, by the relation above, the normalized Crow-Kimura dynamics $\rho_t=\mu^d_t/\int\mu^d_t$ converge to the normalization of $q_t$. For $r=1$, $s=0$, if $X_0$ has density $f$ and the signal and observation noises $W, B$ are independent Brownian motions independent of $X_0$, the limit is the standard Zakai equation, whose normalization is the Kushner-Stratonovich equation for the posterior density of $X_t$ given $(Z_u)_{u\le t}$: the normalized replicator-mutator dynamics converge to exact Bayesian filtering. For $s=0$ and general $r$, in the linear-Gaussian case the normalized dynamics are the density evolution of a multiplicatively covariance-inflated ensemble Kalman-Bucy filter, which helps under model misspecification.

## Expansion

With a smooth observation path, the replicator-mutator PDE is a parabolic equation with a potential that contains $dZ^d/dt$, and the Wong-Zakai principle says that smooth approximations of the driving noise converge to the Stratonovich integral. For $s=0$, expanding $-\tfrac r2\|h-\dot Z^d\|^2_\Xi$ gives $r\,h^\top\Xi^{-1}\dot Z^d$ minus terms quadratic in $h$, and the $\|\dot Z^d\|^2$ part is independent of $x$ and disappears on normalization, leaving the linear equation above; the Stratonovich-to-Itô correction of the $h\,dZ$ term cancels part of the quadratic term, yielding the Zakai form. The proof uses Kunita's forward Feynman-Kac representation of stochastic PDEs and moment bounds that require the condition on $r-s$.

## Sources

- Sahani Pathiraja and Philipp Wacker, "Connections between sequential Bayesian inference and evolutionary dynamics", Philos. Trans. R. Soc. A 383 (2025), 20240241, <https://doi.org/10.1098/rsta.2024.0241>. Numbering follows the arXiv version, arXiv:2411.16366 (2024): Section 3 (Theorem 3.1) and Theorem A.1 (forward representation formula, quoted there from earlier work), <https://doi.org/10.48550/arXiv.2411.16366>.
