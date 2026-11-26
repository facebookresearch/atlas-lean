# Exponential ergodicity of Λ-Wright–Fisher processes with mutation

**$\Lambda$-Wright–Fisher process.** The frequency $X_t\in[0,1]$ of type $a$ solves

$$
\begin{aligned}
dX_t={}&\big(\sigma(X_t)X_t(1-X_t)+\theta_a(1-X_t)-\theta_AX_t\big)dt+\sqrt{\Lambda(\{0\})X_t(1-X_t)}\,dW_t\\
&+\int_{(0,1]\times[0,1]}r\big(\mathbf 1_{\{u\le X_{t-}\}}(1-X_{t-})-\mathbf 1_{\{u>X_{t-}\}}X_{t-}\big)\tilde N(dt,dr,du)\\
&+\int_{(-1,1)}rX_{t-}(1-X_{t-})\,S(dt,dr)+\int_{(-1,1)}|r|\big(\mathbf 1_{\{r\ge0\}}(1-X_{t-})-\mathbf 1_{\{r<0\}}X_{t-}\big)M(dt,dr),
\end{aligned}
$$

with $W$ a Brownian motion, $\tilde N$ a compensated Poisson measure of intensity $dt\,r^{-2}\Lambda(dr)\,du$ (multiple-merger neutral reproduction with finite measure $\Lambda$ on $[0,1]$), and $S,M$ Poisson measures of intensities $dt\,|r|^{-1}\mu(dr)$ and $dt\,|r|^{-1}\nu(dr)$ (random environmental selection and environmental mutation), all independent; $\theta_a,\theta_A\ge0$ are mutation rates and $\sigma$ a frequency-dependent selection function.

Assume $\sigma=\sigma_s$ is a polynomial written in the form

$$
\sigma(x)x(1-x)=\sum_{\ell=2}^{\kappa}\beta_\ell\sum_{i=0}^{\ell}\binom{\ell}{i}x^i(1-x)^{\ell-i}\Big(p^{(\ell)}_i-\frac{i}{\ell}\Big),\qquad \beta_\ell\ge0,\ p^{(\ell)}_i\in[0,1],\ p^{(\ell)}_0=0,\ p^{(\ell)}_\ell=1,
$$

which yields a Bernstein dual built from the ancestral structure (branching at rate $\beta_\ell$ into $\ell$ lines, coalescence from $\Lambda$, absorption of lines by mutation).

**Theorem (Cordero–Véchambre, Theorem 2.15).** If

$$
C:=\nu(-1,1)+\theta_a+\theta_A-\mu(-1,1)-\sum_{\ell=2}^{\kappa}\beta_\ell(\ell-1)>0,
$$

then $X$ is $W_1$-uniformly ergodic on $[0,1]$ and, with stationary law $\rho^X_\infty$,

$$
\sup_{x\in[0,1]}W_1(\rho^X_{x,t},\rho^X_\infty)\le 3e^{-Ct/3}\qquad(t\ge0).
$$

If moreover $\sup_n\mathbb{E}_n[L_1]<\infty$ for the dual line-counting process, there is $K>0$ with $\sup_xd_{\mathrm{Rad}}(\rho^X_{x,t},\rho^X_\infty)\le 2Ke^{-Ct}$ for $t\ge1$. If in addition $\Lambda([0,1/2+\epsilon])>0$ for every $\epsilon>0$, then $X$ is **open set recurrent**: from any start in $(0,1)$, every open subset of $[0,1]$ is visited at arbitrarily large times almost surely.

**Sufficient condition (Proposition 2.16).** $\sup_n\mathbb{E}_n[L_1]<\infty$ holds whenever $\limsup_{x\to0}\log\Lambda([0,x))/\log x<1$; e.g. if $\Lambda(\{0\})>0$, or for $\Lambda(dr)=c\,r^{a-1}(1-r)^{b-1}dr$ with $a\in(0,1)$. This forces the no-dust condition $\int r^{-1}\Lambda(dr)=\infty$ (fast coming down of the dual).

**Open set recurrence criterion (Theorem 2.13).** If $\Lambda([0,1/2+\epsilon])>0$ for all $\epsilon>0$ and $X$ has at least one topologically recurrent point in $(0,1)$, then every point of $[0,1]$ is topologically recurrent. The threshold $1/2$ is sharp: for any other $\Lambda$ the remaining parameters can be chosen so that $1/2$ is not recurrent.

**Without mutation (Theorems 2.19–2.20).** When $\int r^{-1}\Lambda(dr)\in(0,\infty)$, $\Lambda(\{1\})=0$ and there is no mutation ($\nu=0$, $\theta_a=\theta_A=0$), but selection repels the boundaries strongly enough for a Siegmund dual to be absorbed regularly and uniformly, $X$ is locally $W_p$-uniformly ergodic on $(0,1)$ with exponential (under a strong integrability condition on $\Lambda,\mu$ near the endpoints) or polynomial (under a weaker one) rate, and is open set recurrent under the same condition on $\Lambda$.

## Depends on

- [Distance to stationarity from Bernstein and Siegmund duals](distance-to-stationarity-from-bernstein-and-siegmund-duals.md)

## Expansion

The constant $C$ is a net drift of the dual line count: mutation (rates $\theta_a+\theta_A$ and environmental mutation $\nu$) removes lines, while selective branching adds $\ell-1$ lines at rate $\beta_\ell$ and environmental selection $\mu$ duplicates lines. When $C>0$ the number of lines is absorbed at $0$ exponentially fast uniformly in its starting value, and the abstract Bernstein-dual bound gives the rate. Recurrence of the whole interval then follows from recurrence of the support of the stationary law, which the multiple-merger jumps spread over $[0,1]$ when $\Lambda$ charges $[0,1/2+\epsilon]$.

## Sources

- F. Cordero, G. Véchambre, "Distance to stationarity and open set recurrence for ergodic processes on the unit interval with a Bernstein or a Siegmund dual", arXiv:2507.07587 (2025). <https://doi.org/10.48550/arXiv.2507.07587>
