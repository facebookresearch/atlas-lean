# Unbiased incidence recovery and optimal classification from antibody measurements

**Model.** On day $T$ a sample yields an antibody measurement $\mathbf r\in\Omega$. Negatives have density $N(\mathbf r)$; an individual infected $t$ days earlier has density $R(\mathbf r,t)$, with $R(\cdot,0)=N$ (no detectable response on the day of infection). Let $f(t)$ be the fraction of the population infected on day $t$ and $q(T)=\sum_{t\le T}f(t)$ the prevalence. Positives on day $T$ have density $P(\mathbf r,T)=\sum_{t=0}^TR(\mathbf r,t)f(T-t)/q(T)$, and the measurement density is

$$Q(\mathbf r,T)=q(T)P(\mathbf r,T)+(1-q(T))N(\mathbf r)=N(\mathbf r)+\sum_{t=0}^{T-1}f(t)\big(R(\mathbf r,T-t)-N(\mathbf r)\big).$$

**Estimator.** Fix a measurable $D_P\subseteq\Omega$, the same on every day, and set $N_P=\int_{D_P}N$, $R_P(k)=\int_{D_P}R(\cdot,k)$; require $R_P(1)\ne N_P$, i.e. $D_P$ separates day-1 positives from negatives (otherwise the normalization below divides by zero; for example $D_P=\Omega$ gives $R_P(1)=N_P=1$). Let $\widehat Q_P(T)=\frac1S\sum_{i\le S}\mathbf 1_{D_P}(\mathbf r_i)$ from the $S$ samples of day $T$. With $\beta_P(T)=\frac{\widehat Q_P(T)-N_P}{R_P(1)-N_P}$ and $\alpha_P(k)=\frac{R_P(k)-N_P}{R_P(1)-N_P}$, the daily incidences solve the lower-triangular Toeplitz system

$$\widehat f(T-1)=\beta_P(T)-\sum_{t=0}^{T-2}\widehat f(t)\,\alpha_P(T-t),\qquad \widehat f(0)=\beta_P(1),$$

and $\widehat q(T)=\sum_{t\le T}\widehat f(t)$. Every $\widehat Q_P(T)$, $\widehat f(t)$ and $\widehat q(T)$ is unbiased, for any such $D_P$ with $R_P(1)\ne N_P$; the choice affects only the variance.

**Optimal classification.** For pairs $(D_P(T),D_N(T))$ that partition $\Omega$ up to null sets, i.e. $D_P(T)\cup D_N(T)$ has full mass and $D_P(T)\cap D_N(T)$ has zero mass under both $N$ and $P(\cdot,T)$, the prevalence-weighted misclassification

$$\mathcal L(D_P,D_N)=(1-q(T))\int_{D_P}N+q(T)\int_{D_N}P(\cdot,T)$$

is minimized on each day (and hence summed over days) by any such pair with $D_P(T)\supseteq D_P^*(T)$ and $D_N(T)\supseteq D_N^*(T)$ up to null sets, where

$$D_P^*(T)=\{\mathbf r:q(T)P(\mathbf r,T)>(1-q(T))N(\mathbf r)\},\qquad D_N^*(T)=\{\mathbf r:(1-q(T))N(\mathbf r)>q(T)P(\mathbf r,T)\}.$$

These two sets miss the boundary $B(T)=\{\mathbf r:q(T)P(\mathbf r,T)=(1-q(T))N(\mathbf r)\}$, so $(D_P^*(T),D_N^*(T))$ is itself an admissible partition, and the minimizer is unique up to null sets, when $B(T)$ has zero mass under $N$ and $P(\cdot,T)$, as the source assumes; otherwise $B(T)$ may be split between the two classes arbitrarily without changing $\mathcal L$. Plugging $\widehat q(T)$ gives classification domains that move as antibody levels of the infected population rise and wane.

## Depends on

- [Positive predictive value of diagnostic parameters](../../sensitivity-specificity-and-predictive-values/ppv.md)

## Expansion

Integrating $Q$ over $D_P$ gives $Q_P(T)-N_P=\sum_{t<T}f(t)(R_P(T-t)-N_P)$, a discrete convolution of incidence with a known kernel; since $\alpha_P(1)=1$ the system is unit lower-triangular and solved by forward substitution. Each $\beta_P(T)$ is affine in an unbiased Monte Carlo estimate, and the recursion is linear, so unbiasedness propagates. The classification rule is the pointwise Bayes rule: assigning $\mathbf r$ to the class with larger prevalence-weighted density minimizes the integrand of $\mathcal L$ at every point.

## Sources

- P. Bedekar, A. J. Kearsley, P. N. Patrone, "Prevalence Estimation and Optimal Classification Methods to Account for Time Dependence in Antibody Levels", *Journal of Theoretical Biology* 559 (2023), 111375, Section 2 (probability models, Eqs. (PrT), (totprob), (QP), (festimate0), (qestimate), optimal classification scheme), Appendix A (Lemma A.1, Theorem A.2), <https://doi.org/10.1016/j.jtbi.2022.111375> (preprint arXiv:2208.02127).
