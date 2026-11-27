# Nonlinear feedback release laws for sterile insect control

**Setting.** Use the sex-structured sterile insect model with residual fertility $\epsilon$, competitiveness $\gamma$, competition parameter $\beta$ and female basic offspring number $\mathcal N_F>1$ (see the depends-on entry), with the sterile population $M_S(t)$ now chosen from measurements of the wild population.

**Continuous nonlinear feedback.** Let $0\le\epsilon<\mathcal N_F^{-1}$ and pick $\theta>0$ with $\theta+\epsilon<\mathcal N_F^{-1}$. Define

$$
\kappa(x)=\frac1\gamma\,\frac{e^{-\beta x}-(\mathcal N_F^{-1}-\theta)}{(\mathcal N_F^{-1}-\theta)-\epsilon e^{-\beta x}},\qquad x\ge0 .
$$

If the releases maintain $M_S(t)\ge\kappa\big(M(t)+F(t)\big)\,M(t)$ for all $t$, then every solution converges exponentially to $\mathbf 0$; in fact $F(t)\le F(0)e^{-(1-r)\rho\theta t}$, and $M$ decays exponentially as well. Replacing $\kappa(M+F)$ by its maximum $\kappa(0)=\frac1\gamma\frac{1-k}{k-\epsilon}$, $k=\mathcal N_F^{-1}-\theta$, recovers the linear feedback law $M_S=\kappa(0)M$. The nonlinear gain is smaller when the wild population is large, because competition $e^{-\beta(M+F)}$ already suppresses recruitment. Larger $\theta$ raises both the gain and the decay rate.

**Impulsive feedback.** Suppose releases of size $\tau\Lambda_n$ are made at times $n\tau$, right after measuring $M(n\tau)$ and $F(n\tau)$, and assume $\theta+\epsilon<\min(1,\mu_S/\mu_F)\,\mathcal N_F^{-1}$. There is an explicit nonnegative row vector

$$
K_{\epsilon,n}=\kappa\big(M_{n+1}+F_{n+1}\big)\,e^{(\mu_S-\mu_M)\tau}\,\big(1,\ c_{\theta,\tau}\big),\qquad M_{n+1}=M(n\tau)e^{-\mu_M\tau},\ F_{n+1}=F(n\tau)e^{-\mu_F\tau},
$$

with a constant $c_{\theta,\tau}>0$ depending only on $r,\rho,\theta,\mathcal N_F,\mu_M,\tau$, such that if

$$
\tau\Lambda_n\ge\Big|K_{\epsilon,n}\begin{pmatrix}M(n\tau)\\F(n\tau)\end{pmatrix}-M_S(n\tau)\Big|_+\quad\text{for all }n,
$$

then every solution converges exponentially to $\mathbf 0$ with a rate bounded below independently of the initial condition. If moreover $\tau\Lambda_n\le K_{\epsilon,n}(M(n\tau),F(n\tau))^{\mathsf T}$, the total amount released $\sum_n\Lambda_n$ is finite. An analogous statement holds when measurements are taken only every $p\tau$ days, with the release at the $m$-th step after a measurement corrected for the sterile males still alive from the previous $m$ releases.

## Expansion

With $M_S=\boldsymbol\kappa(t)M$, the female equation reads $\dot F=(1-r)\rho\big(\frac{1+\epsilon\gamma\boldsymbol\kappa}{1+\gamma\boldsymbol\kappa}e^{-\beta(M+F)}-\mathcal N_F^{-1}\big)F$. Requiring the bracket to be at most $-\theta$ and solving for $\boldsymbol\kappa$ gives exactly $\boldsymbol\kappa\ge\kappa(M+F)$; the condition $\epsilon+\theta<\mathcal N_F^{-1}$ keeps the denominator positive. Exponential decay of $F$ then feeds a linear inequality for $M$, and Gronwall's lemma gives exponential decay of $M$. In the impulsive version, between releases $M$ and $F$ decay at most at rates $\mu_M$ and $\mu_F$ and are bounded above by the Gronwall estimates, while $\kappa$ is decreasing; so a release that covers the worst case over the next period, using the lower bounds $M_{n+1},F_{n+1}$ inside $\kappa$ and the upper bounds outside, keeps the continuous feedback inequality valid on the whole interval. The condition involving $\mu_S/\mu_F$ makes all exponents in this worst-case bound nonnegative.

## Depends on

- [Critical release rate and residual-fertility threshold in the sex-structured SIT model](critical-release-rate-and-residual-fertility-threshold-in-the-sex-structured-sit-model.md)

## Proof depends on

- [Gronwall inequality in integral form](../../../../../Analysis/ordinary-differential-equations/gronwall-inequality/gronwall-inequality-integral-form.md)

## Sources

- M. S. Aronna, Y. Dumont, "On nonlinear pest/vector control via the Sterile Insect Technique: impact of residual fertility", arXiv:2005.05595 (2020), Section 4 (closed-loop control: Proposition 3 on continuous nonlinear feedback, Theorem 2 on impulsive feedback with synchronized measurements, Theorem 3 on sparse measurements), <https://doi.org/10.48550/arXiv.2005.05595>.
