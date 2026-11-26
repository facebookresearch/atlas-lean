# Isotropic normal conditioned on a cone and its normalizing constant

**Setting.** In constrained size-and-shape analysis of low-resolution RNA backbones, fixed bond lengths and angles leave each free landmark on a product of spheres and half-cylinders (polypolar coordinates); a landmark whose bond angle is fixed moves on a cone. Parametrize the cone of half-angle $c \in [0,\pi]$ about the $z$-axis by

$$\mathbf{x} = r\,(\sin c\cos\theta,\ \sin c\sin\theta,\ \cos c)^T, \qquad r > 0,\ \theta \in [0, 2\pi),$$

and let $\mathbf{x} \sim \mathcal{N}(\boldsymbol\mu, \sigma^2 I_3)$ be trivariate isotropic normal.

**Theorem.** Conditioned on lying on the cone, $(r, \theta)$ has density

$$p(r,\theta) = \frac{1}{c(\kappa_1,\kappa_2,\kappa_3)}\; r\, \exp\big\{-\kappa_1 r^2 + \kappa_2 r + \kappa_3 r\cos(\theta - \mu)\big\}, \qquad r > 0,\ 0 \le \theta < 2\pi,$$

with parameters $\kappa_1 > 0$, $\kappa_2, \kappa_3 \in \mathbb{R}$ and $0 \le \mu < 2\pi$ determined by $\boldsymbol\mu$, $\sigma^2$ and $c$.

**Lemma (normalizing constant).** For $\kappa_1 > 0$,

$$c(\kappa_1,\kappa_2,\kappa_3) = \pi \sum_{m=0}^\infty \frac{\kappa_2^m}{\kappa_1^{m/2 + 1}}\, \frac{\Gamma(\frac m2 + 1)}{m!}\; {}_1F_1\Big(\frac m2 + 1;\ 1;\ \frac{\kappa_3^2}{4\kappa_1}\Big),$$

where ${}_1F_1(a;b;z) = \sum_{j \ge 0} \frac{(a)_j}{(b)_j}\frac{z^j}{j!}$ is Kummer's confluent hypergeometric function and $(a)_j = a(a+1)\cdots(a+j-1)$.

The family is an exponential family with natural parameters $\kappa_1$, $\kappa_2$, $\kappa_3\cos\mu$, $\kappa_3\sin\mu$; for $\kappa_2 = 0$ it is a bivariate normal in the Cartesian coordinates $(r\cos\theta, r\sin\theta)$, and given $r$ the angle $\theta$ is von Mises with mean $\mu$ and concentration $\kappa_3 r$.

## Expansion

Writing $\|\mathbf{x} - \boldsymbol\mu\|^2 = r^2 - 2r\,\boldsymbol\mu\cdot\mathbf{e}(\theta) + \|\boldsymbol\mu\|^2$ with $\mathbf{e}(\theta)$ the unit generator of the cone, the term $\boldsymbol\mu\cdot\mathbf{e}(\theta) = \mu_z\cos c + \sin c\,(\mu_x\cos\theta + \mu_y\sin\theta)$ splits into a part linear in $r$ (giving $\kappa_2$) and a part in $\cos(\theta - \mu)$ (giving $\kappa_3$), and the surface element on the cone contributes the factor $r$. For the constant, integrate $\theta$ to get $2\pi I_0(\kappa_3 r)$, expand $e^{\kappa_2 r}$ in powers of $r$, and use $\int_0^\infty r^{m+1} e^{-\kappa_1 r^2} I_0(\kappa_3 r)\,dr = \frac12 \Gamma(\frac m2 + 1)\,\kappa_1^{-(m/2+1)}\, {}_1F_1(\frac m2 + 1; 1; \kappa_3^2/(4\kappa_1))$.

## Sources

- K. V. Mardia, B. Eltzner and S. F. Huckemann, "Constrained Shape Analysis with Applications to RNA Structure", arXiv:2502.16270 (2025), Section 2 (polypolar coordinates), Section 4 (distributions on polypolar coordinates, Theorem 4.1 and Lemma 4.2), <https://doi.org/10.48550/arXiv.2502.16270>.
