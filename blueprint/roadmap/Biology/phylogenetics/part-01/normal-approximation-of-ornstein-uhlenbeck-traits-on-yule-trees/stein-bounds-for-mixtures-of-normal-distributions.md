# Stein bounds for mixtures of normal distributions

**Statement.** Let $X$ be a real random variable with $\mathbb E(X^2)<\infty$, and let $\mathscr G$ be a $\sigma$-algebra such that the regular conditional distribution of $X$ given $\mathscr G$ is normal, with random mean $\mathbb E(X\mid\mathscr G)$ and random variance $\mathbb V(X\mid\mathscr G)$. Put $\mu=\mathbb E X$ and $\sigma^2=\mathbb E\,\mathbb V(X\mid\mathscr G)>0$. Write $V_E=\mathbb V\big(\mathbb E(X\mid\mathscr G)\big)$ and $V_V=\mathbb V\big(\mathbb V(X\mid\mathscr G)\big)$. Then the Kolmogorov distance satisfies

$$d_K\big(\mathscr L(X),N(\mu,\sigma^2)\big)\le\frac{\sqrt{V_V}}{\sigma^2}+\frac{V_E}{\sigma^2}+\sqrt{\frac2\pi}\,\frac{\sqrt{V_E}\,V_V^{1/4}}{\sigma^2},$$

and the Wasserstein distance between the standardized variable and $N(0,1)$ satisfies

$$d_W\Big(\mathscr L\big(\tfrac{X-\mu}{\sigma}\big),N(0,1)\Big)\le\sqrt{\frac2\pi}\,\frac{V_V^{3/4}}{\sigma^3}+\frac{\sqrt{V_E}\sqrt{V_V}}{\sigma^3}+\frac{V_E}{\sigma^2}+\sqrt{\frac2\pi}\,\frac{\sqrt{V_E}\,V_V^{1/4}}{\sigma^2}.$$

The bounds depend only on the first two moments of the first two conditional moments. In the degenerate case of two normals, $d_K\big(N(m,\tau^2),N(\mu,\sigma^2)\big)\le\sigma^{-2}|\sigma^2-\tau^2|+\frac{\sqrt{2\pi}}{4\sigma}|\mu-m|$.

## Expansion

Stein's method for $N(\mu,\sigma^2)$ uses the characterizing equation $\mathbb E[\sigma^2f'(Z)-(Z-\mu)f(Z)]=0$. Conditionally on $\mathscr G$, $X$ is exactly normal with parameters $(M,S^2)=(\mathbb E(X\mid\mathscr G),\mathbb V(X\mid\mathscr G))$, so $\mathbb E[S^2f'(X)-(X-M)f(X)\mid\mathscr G]=0$. Plug in the solution $f_h$ of the Stein equation for a test function $h$, either an indicator for $d_K$ or a 1-Lipschitz function for $d_W$. The error then becomes

$$\mathbb E\big[(\sigma^2-S^2)f_h'(X)\big]+\mathbb E\big[(M-\mu)f_h(X)\big].$$

The standard bounds on $\|f_h\|_\infty$, $\|f_h'\|_\infty$ and the Lipschitz constant of $f_h'$, combined with Cauchy–Schwarz, give the stated combinations of $V_V$ and $V_E$. This route avoids computing the third moment that a classical Berry–Esseen argument would need for sums of dependent tip values.

These are the two main theorems and two remarks of Section 2 of the source.

## Sources

- K. Bartoszek, T. Erhardsson, "Normal approximation for mixtures of normal distributions and the evolution of phenotypic traits", arXiv:1912.03561 (2019). <https://doi.org/10.48550/arXiv.1912.03561>
- Published version: K. Bartoszek, T. Erhardsson, "Normal approximation for mixtures of normal distributions and the evolution of phenotypic traits", Advances in Applied Probability 53 (2021), 162–188, <https://doi.org/10.1017/apr.2020.53>.
