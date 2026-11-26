# Asymptotic normality of a cross-fitted estimator

Let $(\Omega, P)$ be a probability space, $\mathcal{W}$ a measurable space with a probability measure $\nu$, and $W_0, W_1, \dots : \Omega \to \mathcal{W}$ measurable, mutually independent and identically distributed with law $\nu$. Let $\psi : \mathcal{W} \to \mathbb{R}$ be measurable with $\psi \in L^2(\nu)$ (the score at the true nuisances). Let $K \in \mathbb{N}$ and let $\mathrm{fold} : \mathbb{N} \to \mathbb{N} \to \{0, \dots, K-1\}$ be a fold assignment, $\mathrm{fold}(n, i)$ being the fold of unit $i$ at sample size $n$. Write $U_{n,k}(\omega) = (W_i(\omega))_{i < n,\ \mathrm{fold}(n,i) \ne k}$ for the training data of fold $k$. Let $G_{n,k} : \mathcal{W}^{\mathrm{trainFold}(n,k)} \times \mathcal{W} \to \mathbb{R}$ be measurable with $G_{n,k}(u, \cdot) \in L^2(\nu)$ for every $u$, and let $\hat\theta_n = n^{-1} \sum_{i < n} G_{n, \mathrm{fold}(n,i)}(U_{n,\mathrm{fold}(n,i)}, W_i)$ be the cross-fitted estimator. Assume for every fold $k$, as $n \to \infty$:

- $L^2$ consistency: $\int \bigl(G_{n,k}(U_{n,k}, w) - \psi(w)\bigr)^2 d\nu(w) \xrightarrow{P} 0$;
- negligible bias: $\sqrt{n}\,\Bigl(\int G_{n,k}(U_{n,k}, w)\, d\nu(w) - \int \psi \, d\nu\Bigr) \xrightarrow{P} 0$.

Then, with $\theta = \int \psi \, d\nu$,

$$\sqrt{n}\,\bigl(\hat\theta_n - \theta\bigr) \xrightarrow{d} \mathcal{N}\bigl(0, \operatorname{Var}_\nu(\psi)\bigr),$$

that is, it converges in distribution to any random variable $Z$ on a probability space with $Z \sim \mathcal{N}(0, \operatorname{Var}_\nu(\psi))$. No Donsker or entropy condition is assumed.
