# Berry–Esseen theorem with constant 42

Let $X_0, X_1, X_2, \dots$ be measurable, mutually
independent real random variables on a probability space, each with the same distribution as
$X_0$, where $X_0$ has a finite third moment, mean $\mathbb{E}[X_0] = 0$ and variance
$\sigma^2 = \operatorname{Var}(X_0) > 0$ with $\sigma > 0$. Write $\rho = \mathbb{E}|X_0|^3$,
$S_n = X_0 + \dots + X_{n-1}$, and $\Phi$ for the distribution function of the standard normal
distribution. Then for every $n \ge 1$ and every real $x$,

$$\left|\mathbb{P}\left(\frac{S_n}{\sqrt{n\sigma^2}} \le x\right) - \Phi(x)\right| \le
\frac{42\rho}{\sigma^3\sqrt{n}}.$$

Integrability of $X_0$ is not assumed separately, since on a probability space it follows from
the finite third moment.
