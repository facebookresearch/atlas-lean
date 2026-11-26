# Aipw Estimator

Let $O_i : \Omega \to \Omega_1$ ($i \in \mathbb N$) be random units, $T \subseteq \Omega_1$ a treatment event, $X : \Omega_1 \to \mathcal X$ a covariate and $Y : \Omega_1 \to \mathbb R$ an outcome, and let $e_n^i(\omega), m_{0,n}^i(\omega), m_{1,n}^i(\omega) : \mathcal X \to \mathbb R$ be nuisance functions that may depend on the sample size $n$, the unit $i$ and the sample point $\omega$. Write $\hat\psi_{n,i}(\omega)$ for the fitted AIPW score of unit $i$ at sample size $n$.

The AIPW estimator of the average treatment effect at sample size $n$ is the sample mean of the fitted scores of units $0, \dots, n-1$:

$$\hat\tau_n(\omega) = \frac1n \sum_{i < n} \hat\psi_{n,i}(\omega),$$

with $\hat\tau_0 = 0$ (since $0^{-1} = 0$).
