# Scalar AWGN converse, variance form

Let $(\Omega, \mu)$ be a probability space and let $X, Z : \Omega \to \mathbb{R}$ be measurable and independent, with $Z \sim \mathcal{N}(0, N)$ for some $N > 0$. The input satisfies the power bound at budget $P$, meaning $P \ge 0$ and $\int_\Omega X^2 \, d\mu \le P$, the integral being the integral of a nonnegative function (no integrability of $X$ is assumed). Then $\operatorname{Var}(X) \le P$ and

$$I(X; X + Z) \le \frac{\ln\left(1 + \operatorname{Var}(X)/N\right)}{2 \ln 2}.$$

Here $I(X; X + Z)$ is the mutual information, in bits, of the joint law of $(X, X + Z)$: the Kullback–Leibler divergence of that law from the product of its marginals, divided by $\ln 2$, with values in $[0, \infty]$. The mean of $X$ does not enter the bound.
