# Cond Exp indicator comap ae eq

Let $\mu$ be a finite measure on a measurable space $\Omega$, $X : \Omega \to \mathcal X$ measurable with $\mathcal X$ countable with measurable singletons, and $E \subseteq \Omega$ measurable. Then the conditional probability of $E$ given $\sigma(X)$ is the propensity of $E$ at the observed covariate value:

$$\mu(E \mid \sigma(X))(\omega) = \frac{\mu(E \cap \{X = X(\omega)\})}{\mu(X = X(\omega))} \quad \text{for } \mu\text{-a.e. } \omega,$$

where the quotient is taken to be $0$ when its denominator is $0$.
