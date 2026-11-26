# Weighted quantile Mendelian randomization with asymmetric-Laplace quantile selection

**Setting.** In two-sample summary-data Mendelian randomization with $p$ genetic instruments, let $\hat r_i=\hat\beta_{Yi}/\hat\beta_{Xi}$ be the ratio estimate of the causal effect $\theta_0$ of exposure $X$ on outcome $Y$ from instrument $i$, and $w_i>0$ precision weights (by the delta method, $\operatorname{Var}\hat r_i\approx\sigma_{Yi}^2/\hat\beta_{Xi}^2+\hat\beta_{Yi}^2\sigma_{Xi}^2/\hat\beta_{Xi}^4$ for independent samples). Invalid instruments have pleiotropic effects that shift $\hat r_i$ away from $\theta_0$. With the check loss $\rho_\tau(u)=\tau u$ for $u\ge0$ and $(\tau-1)u$ for $u<0$, the weighted $\tau$-quantile

$$\hat Q(\tau)=\arg\min_\theta\sum_{i=1}^pw_i\,\rho_\tau(\hat r_i-\theta)$$

generalizes the weighted median estimator ($\tau=1/2$).

**Consistency condition.** $\hat Q(\tau)$ is consistent for $\theta_0$ whenever $q_-\le\tau\le1-q_+$, where $q_-$ and $q_+$ are the weighted proportions of invalid instruments with negative and positive pleiotropic effects. This holds for some $\tau$ exactly under the zero modal pleiotropy assumption (the weighted mode of the pleiotropic effects is $0$); the weighted median additionally needs a valid weighted majority.

**Model for selecting $\tau$.** Assume $\hat r_i$ follows an asymmetric Laplace distribution with location $\theta$, skewness $\tau\in(0,1)$ and inverse scale $\lambda w_i$:

$$f(\hat r_i)=\lambda w_i\,\tau(1-\tau)\exp\big(-\lambda w_i\,\rho_\tau(\hat r_i-\theta)\big),$$

so $\theta$ is the $\tau$-quantile of each $\hat r_i$. Coordinate-wise maximization of the likelihood gives

$$\hat\theta=\arg\min_\theta\sum_iw_i\rho_{\hat\tau}(\hat r_i-\theta),\qquad \hat\lambda=\frac{p}{\sum_iw_i\rho_{\hat\tau}(\hat r_i-\hat\theta)},\qquad \hat\tau=\frac12-\frac{\hat a}{2\big(2p+\sqrt{\hat a^2+4p^2}\big)},$$

with $\hat a=\hat\lambda\sum_iw_i(\hat r_i-\hat\theta)$, iterated to convergence; $\hat\theta$ is then the weighted $\hat\tau$-quantile of the ratio estimates.

**Proposition (valid root).** For $a\neq0$ and $p>0$, the $\tau$-score equation $p(1-2\tau)=a\,\tau(1-\tau)$ has exactly one root in $(0,1)$, namely the one displayed above (the negative-sign root of the quadratic).

**Proposition (direction of the selected quantile).** Let $\bar r_w=\sum_iw_i\hat r_i/\sum_iw_i$ be the weighted mean of the ratios. Then $\hat\tau<1/2$ if $\bar r_w>\theta$, $\hat\tau=1/2$ if $\bar r_w=\theta$, and $\hat\tau>1/2$ if $\bar r_w<\theta$. Thus when pleiotropy pushes the bulk of ratios upward, the estimator moves to a lower quantile, and conversely.

## Expansion

Differentiating the log-likelihood in $\tau$ uses $\partial_\tau\rho_\tau(u)=u$, giving $p\frac{1-2\tau}{\tau(1-\tau)}=\lambda\sum_iw_i(\hat r_i-\theta)=a$, a quadratic $a\tau^2-(a+2p)\tau+p=0$ whose roots are $\frac{a+2p\pm\sqrt{a^2+4p^2}}{2a}$; only the minus root lies in $(0,1)$, and rationalizing gives the stated form. Its sign is that of $-a$, which yields the direction result. Directional pleiotropy skews the empirical distribution of ratios, and the asymmetric Laplace fit reads that skew to choose a quantile inside the consistency window $[q_-,1-q_+]$ without knowing the proportion of invalid instruments, which matters most when many instruments carry small pleiotropic effects.

## Sources

- Julien St-Pierre, Archer Y. Yang, Mireille E. Schnitzer, Marc-André Legault, "Robust Mendelian Randomization Estimation using Weighted Quantile Regression", arXiv:2604.07566 (2026): Sections 2.2–2.3 (weighted quantile regression and asymmetric Laplace model), Appendix A.1 (consistency condition), Appendix A.2 with Propositions 1–2. <https://doi.org/10.48550/arXiv.2604.07566>
