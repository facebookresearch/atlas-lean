# Half-normal fluctuations at the critical fitness threshold

**Setting.** In the fitness-threshold ecosystem (i.i.d. increments $I_n$, uniform fitnesses, least fit removed first), let $\hat F_n$ be the empirical fitness distribution, $F$ the $U[f_c,1]$ distribution function with $f_c=\mathbb{E}I_-/\mathbb{E}I_+$, and $\hat\Delta_n=\hat F_n-F$. Assume

$$\mathbb{E}I_-<\mathbb{E}I_+,\qquad \mathbb{E}(I^2)<\infty .$$

Let $W_1,W_2$ be independent standard Brownian motions and $\mathrm{Br}_1(f)=W_1(f)-fW_1(1)$ the Brownian bridge of $W_1$. Put $\sigma_2=\sigma(f_cI_+-I_-)$, $\tilde\sigma_1=\sqrt{f_c(1-f_c)\mathbb{E}I_+}$, and let $Y_\infty=\tilde\sigma_1\tilde W_1+\sigma_2W_2$, where $\tilde W_1$ is a standard Brownian motion built from $W_1$ on $[0,f_c]$ and a randomly rotated portion of its increments on $[f_c,1]$ (with $\tilde W_1\equiv0$ if $f_c=0$). Let $\Psi(x)=x(1)-\inf_{0\le t\le1}x(t)$.

**Theorem (functional CLT).** For every $f_0\in(f_c,1]$,

$$\sqrt n\,\Big(\hat\Delta_n\big|_{[f_0,1]},\ \hat F_n(f_c)\Big)\ \Rightarrow\ \frac{1}{(1-f_c)\,\mathbb{E}I_+}\Big(\sqrt{\mathbb{E}I_+}\,\mathrm{Br}_1+(1-F)\,\sigma_2\,W_2(1),\ \Psi(Y_\infty)\Big)\quad\text{in } D([f_0,1])\times\mathbb{R}.$$

**One-dimensional marginals.** With $Z$ standard normal and

$$g(f)=\frac{1}{(1-f_c)\,\mathbb{E}I_+}\sqrt{f(1-f)\,\mathbb{E}I_+ +\Big(\frac{1-f}{1-f_c}\Big)^2\sigma_2^2},\qquad \sigma_2^2=f_c^2\,\mathbb{E}(I_+^2)+\mathbb{E}(I_-^2),$$

where $\sigma_2^2$ is the variance of the mean-zero variable $f_cI_+-I_-$ (no cross term, since $I_+I_-=0$). (The source's Theorem 2 has the prefactor $1/\mathbb{E}I_+$ and a cross term $2f_c\,\mathbb{E}I_+\,\mathbb{E}I_-$; but the population has size about $n(1-f_c)\mathbb{E}I_+$, and a simulation of the $\pm1$ walk with $\mathbb P(I=1)=0.7$ gives standard deviations $1.000$ at $f=0.8$ and $1.514$ at $f=0.6$, matching $1.014$ and $1.537$ from the formula above.)

$$\sqrt n\,\hat\Delta_n(f)\Rightarrow\begin{cases} g(f)\,Z, & f>f_c,\\ g(f_c)\,|Z|, & f=f_c,\end{cases}$$

while $\sqrt n\,\hat\Delta_n\to0$ uniformly on compacts of $[0,f_c)$ in probability. The limit is thus zero below the threshold, half-normal at it, and a continuous Gaussian process above it with a nondegenerate right limit at $f_c$; in particular $(\sqrt n\,\hat\Delta_n)$ is not tight in $D([0,1])$ or $D([f_c,1])$. This differs from the Brownian bridge limit of classical empirical processes, including those with random sample sizes.

## Expansion

Write $L_n(f)=S_n(f)-M_n(f)$ with $S_n(f)$ a sum of i.i.d. terms. Above $f_c$ the running minimum $M_n(f)$ is eventually constant, so $\hat F_n(f)$ is a smooth function of the partial sums $S_n(f)$ and $X_n$. Donsker's theorem for the counts of uniform fitnesses (a Brownian bridge in $f$) and for the birth–death increments (the $W_2$ term) gives the Gaussian part; the factor $(1-F)$ comes from normalizing by $X_n$. At $f=f_c$ the walk $S(f_c)$ has zero drift, so $L_n(f_c)/\sqrt n$ converges to the reflected functional $\Psi$ of its Brownian limit $Y_\infty$, and Lévy's identity $\Psi(W)\overset{d}{=}|W(1)|$ gives the half-normal marginal. The proof establishes tightness and convergence of finite-dimensional distributions, computing the covariances of the limit explicitly.

## Depends on

- [Glivenko–Cantelli theorem for the fitness-threshold ecosystem](glivenko-cantelli-theorem-for-the-fitness-threshold-ecosystem.md)

## Sources

- Iddo Ben-Ari, "An Empirical Process Interpretation of a Model of Species Survival", arXiv:1210.1112 (2012): Theorem 2 (functional CLT), Lemma 2 ($\tilde W_1$ is Brownian motion), marginal formula following Theorem 2, Lemma 4 (tightness), Lemma 6 (covariances), Lemma 7 (finite-dimensional convergence), Sections 1–2. <https://doi.org/10.48550/arXiv.1210.1112>. Published version: Stochastic Processes and their Applications 123(2) (2013), 475–489, <https://doi.org/10.1016/j.spa.2012.09.009>; locators above refer to the arXiv version.
