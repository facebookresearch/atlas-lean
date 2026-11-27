# Plasmid loss threshold and evolutionarily stable segregation

**Model.** Let $u_z(t)$ be the density of cells carrying $z \in \{0, 1, \dots, \hat z\}$ plasmids. Plasmids replicate at logistic rate $b z (1 - z/\hat z)$, cells with $z_0$ plasmids divide at rate $\beta(z_0, \alpha)$ in environment $\alpha$ (antibiotic absent or present), and each plasmid goes to a chosen daughter independently with probability $p_{z_0} \in [0, \tfrac12]$, so a daughter receives $z$ plasmids with probability $g(z; z_0) = \binom{z_0}{z} p_{z_0}^z (1 - p_{z_0})^{z_0 - z}$; the **segregation kernel** is $k(z; z_0) = g(z; z_0) + g(z_0 - z; z_0)$. Only plasmid-free cells die, at rate $\mu(0, \alpha)$ ($\mu_0 > 0$ with antibiotic, $0$ without). The model (Equation 4)

$$\dot u_z = -b z\Big(1 - \tfrac{z}{\hat z}\Big) u_z + b (z-1)\Big(1 - \tfrac{z-1}{\hat z}\Big) u_{z-1} - \beta(z, \alpha) u_z + \sum_{z_0 = z}^{\hat z} k(z; z_0)\, \beta(z_0, \alpha)\, u_{z_0} - \mu(z, \alpha) u_z$$

is linear and splits as $x_0' = (\beta(0,\alpha) - \mu(0,\alpha)) x_0 + B^\top y$, $y' = A y$ with $x_0 = u_0$ and $y = (u_1, \dots, u_{\hat z})$. The matrix $A$ is irreducible, so its spectral bound $\lambda_1 = \lambda_1(p)$ is a real eigenvalue with positive eigenvector $\hat y$, and depends on the segregation strategy $p = (p_z)$.

**Theorem 1.** Let $N(t) = x_0(t) + \sum_{z \ge 1} y_z(t)$ and suppose the long-run plasmid-free growth rate $\hat\lambda_0 = \lim_{t \to \infty} \frac1t \int_0^t (\beta(0, \alpha(\tau)) - \mu(0, \alpha(\tau)))\, d\tau$ exists. If $\hat\lambda_0 > \lambda_1$, then $\sum_{z \ge 1} y_z / N \to 0$ and the plasmid is lost. If $\hat\lambda_0 < \lambda_1$, then $y(t)/N(t) \to c\, \hat y$ for some $c > 0$, a stable plasmid-bearing subpopulation.

**Definition 2 (ESSS).** A segregation strategy $p^* \in [0, 0.5]^{\hat z}$ maximizing $\lambda_1(p)$ is the evolutionarily stable segregation strategy; when $\hat\lambda_0 < \lambda_1(p^*)$ a resident population using $p^*$ cannot be invaded by any other segregation strategy.

## Proof depends on

- [Perron–Frobenius theorem for irreducible nonnegative matrices](../../../../../LinearAlgebra/special-matrices/perron-frobenius-theorem/perron-frobenius.md)

## Expansion

Plasmid-free cells never acquire plasmids, so the system is block triangular: the plasmid-free class grows at its own rate and is fed by segregation losses, while the plasmid-bearing block evolves autonomously under $A$. By Perron–Frobenius theory for the irreducible quasi-positive matrix $A$, $y(t) \sim c e^{\lambda_1 t} \hat y$, and variation of constants shows $x_0$ grows like $e^{\max(\hat\lambda_0, \lambda_1) t}$, giving the dichotomy. Between two strategies competing in the same environment, the one with the larger $\lambda_1$ outgrows the other, which makes maximizing $\lambda_1$ the evolutionary criterion. The maximizer is not available in closed form; gradient ascent on $\lambda_1(p)$ shows that for low and medium copy numbers the optimum is $p_z = \tfrac12$ (fair segregation), while for high copy numbers it becomes systematically unequal.

## Sources

- K. Münch, R. Münch, R. Biedendieck, D. Jahn, J. Müller, "Evolutionary model for the unequal segregation of high copy plasmids", PLoS Computational Biology 15 (2019) e1006724, Equations (2)–(8), Definitions 1–2, Theorem 1, <https://doi.org/10.1371/journal.pcbi.1006724> (PMC6420036).
