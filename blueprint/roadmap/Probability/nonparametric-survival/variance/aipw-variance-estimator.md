# Aipw Variance Estimator

Let $O_i : \Omega \to \Omega_1$ ($i \in \mathbb N$) be random units, $T \subseteq \Omega_1$ a treatment event, $X : \Omega_1 \to \mathcal X$ a covariate and $Y : \Omega_1 \to \mathbb R$ an outcome, and let $e_n^i(\omega), m_{0,n}^i(\omega), m_{1,n}^i(\omega) : \mathcal X \to \mathbb R$ be nuisance functions that may depend on the sample size $n$, the unit $i$ and the sample point $\omega$. Write $\hat\psi_{n,i}(\omega)$ for the fitted AIPW score of unit $i$ at sample size $n$ and $\hat\tau_n(\omega) = n^{-1}\sum_{i<n}\hat\psi_{n,i}(\omega)$ for the AIPW estimator.

The plug-in variance estimator is the $1/n$ sample variance of the fitted scores of units $0, \dots, n-1$, that is, of the estimated influence-function values $\hat\psi_{n,i} - \hat\tau_n$:

$$\hat\sigma_n^2(\omega) = \frac1n \sum_{i<n} \bigl(\hat\psi_{n,i}(\omega) - \hat\tau_n(\omega)\bigr)^2,$$

with $\hat\sigma_0^2 = 0$.
