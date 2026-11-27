# Shadow of gene-level selection on modal protocell composition

**Setting.** In the fast–slow protocell model with protocell reproduction $G_{FS}(x) = x - \eta x^2$ ($x$ = fraction of slow genes, $\eta \in (0,1]$), gene-level advantage $s$ for fast genes and relative between-protocell selection strength $\lambda$, the long-time state for $\lambda(1-\eta) > s\theta$ is the density $p^\lambda_\theta(x) \propto x^{(\lambda/s)(1-\eta)-\theta-1}(1-x)^{\theta-1} e^{-\lambda\eta x/s}$ (see [Long-time behavior of the fast–slow protocell PDE](long-time-behavior-of-the-fast-slow-protocell-pde.md)).

**Proposition.** Suppose $\lambda(1-\eta) > s(\theta+1)$ and $\theta \ge 1$. For $\eta \in (0,1]$ the modal composition $\hat x^\lambda_{FS} = \arg\max_{x\in[0,1]} p^\lambda_\theta(x)$ is

$$\hat x^\lambda_{FS} = \frac{\lambda - 2s - \sqrt{(\lambda - 2s)^2 - 4\lambda\eta\,[\lambda(1-\eta) - s(\theta+1)]}}{2\lambda\eta},$$

and $\hat x^\lambda_{FS} = 1$ for $\eta = 0$. As between-protocell selection becomes infinitely strong,

$$\hat x^\infty_{FS} = \lim_{\lambda\to\infty} \hat x^\lambda_{FS} = \begin{cases} 1, & \eta < \tfrac12,\\[2pt] \dfrac1\eta - 1, & \eta \ge \tfrac12 .\end{cases}$$

For $\eta > 1/2$ the collective optimum is $x^* = 1/(2\eta)$, and $\hat x^\infty_{FS} = 1/\eta - 1 < 1/(2\eta)$: even with arbitrarily strong protocell-level competition the most abundant protocell carries fewer slow genes than the protocell-level optimum.

## Depends on

- [Long-time behavior of the fast–slow protocell PDE](long-time-behavior-of-the-fast-slow-protocell-pde.md)

## Proof sketch

Setting the logarithmic derivative of $p^\lambda_\theta$ to zero gives the quadratic $\lambda\eta x^2 - (\lambda - 2s)x + [\lambda(1-\eta) - s(\theta+1)] = 0$ after clearing denominators; its smaller root lies in $[0,1]$. Dividing by $\lambda$ and letting $\lambda\to\infty$ gives $\eta x^2 - x + (1-\eta) = 0$, with roots $1$ and $1/\eta - 1$. The gap from $x^*$ persists because the PDE's steady state balances protocell fitness against the within-cell drift, which vanishes only at the boundary: the steady state maximizes not $G$ itself but a $G$-weighted quantity whose maximum is displaced toward the all-fast boundary.

## Sources

- Daniel B. Cooney, Fernando W. Rossine, Dylan H. Morris and Simon A. Levin, "A PDE Model for Protocell Evolution and the Origin of Chromosomes via Multilevel Selection", *Bulletin of Mathematical Biology* 84 (2022), 109, <https://doi.org/10.1007/s11538-022-01062-y>. Preprint version: arXiv:2109.09357 (2021), proposition on the most abundant protocell composition at steady state for the fast–slow model, <https://doi.org/10.48550/arXiv.2109.09357>.
