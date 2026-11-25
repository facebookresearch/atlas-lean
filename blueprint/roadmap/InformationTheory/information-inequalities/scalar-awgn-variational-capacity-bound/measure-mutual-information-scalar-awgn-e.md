# Measure Mutual Information scalar AWGN eq zero of power zero

Let $(\Omega, \mu)$ be a probability space and let $X, Z : \Omega \to \mathbb{R}$ be measurable and independent, with $Z \sim \mathcal{N}(0, N)$ for some $N > 0$. Suppose the input has zero power: $\int_\Omega X^2 \, d\mu \le 0$ (the integral of a nonnegative function). Then

$$I(X; X + Z) = 0.$$

Here $I(X; X + Z)$ is the mutual information, in bits, of the joint law of $(X, X + Z)$: the Kullback–Leibler divergence of that law from the product of its marginals, divided by $\ln 2$, with values in $[0, \infty]$.
