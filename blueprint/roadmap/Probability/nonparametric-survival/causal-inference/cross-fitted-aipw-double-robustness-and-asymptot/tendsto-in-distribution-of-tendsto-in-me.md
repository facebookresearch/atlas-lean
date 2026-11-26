# From the oracle gap to asymptotic normality

Let $(\Omega, P)$ be a probability space, $\mathcal{W}$ a measurable space with a probability measure $\nu$, and $W_0, W_1, \dots : \Omega \to \mathcal{W}$ measurable, mutually independent and identically distributed with law $\nu$. Let $\psi : \mathcal{W} \to \mathbb{R}$ be measurable with $\psi \in L^2(\nu)$, and let $\hat\theta_n : \Omega \to \mathbb{R}$ be almost everywhere measurable estimators with

$$\sqrt{n}\,\Bigl(\hat\theta_n - n^{-1} \sum_{i < n} \psi(W_i)\Bigr) \xrightarrow{P} 0.$$

Then

$$\sqrt{n}\,\Bigl(\hat\theta_n - \int \psi \, d\nu\Bigr) \xrightarrow{d} \mathcal{N}\bigl(0, \operatorname{Var}_\nu(\psi)\bigr),$$

that is, it converges in distribution to any random variable $Z$ on a probability space with $Z \sim \mathcal{N}(0, \operatorname{Var}_\nu(\psi))$. This is the central limit theorem for the oracle estimator combined with Slutsky's lemma.
