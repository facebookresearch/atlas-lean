# Measure Mutual Information scalar AWGN const

Let $(\Omega, \mu)$ be a probability space and $Z : \Omega \to \mathbb{R}$ measurable with $Z \sim \mathcal{N}(0, N)$ for some $N > 0$, and let $c \in \mathbb{R}$. The constant input $X \equiv c$ satisfies the power bound at budget $c^2$, that is $c^2 \ge 0$ and $\int_\Omega c^2 \, d\mu \le c^2$, and

$$I(c; c + Z) = 0,$$

although the budget $c^2$ is positive when $c \neq 0$. Here $I(c; c + Z)$ is the mutual information, in bits, of the joint law of $(c, c + Z)$: the Kullback–Leibler divergence of that law from the product of its marginals, divided by $\ln 2$, with values in $[0, \infty]$.
