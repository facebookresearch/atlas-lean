# Mean-field simplicial contagion and bistability

In the simplicial SIS contagion model on a simplicial complex, a susceptible node is infected at rate $\beta$ through each link to an infectious neighbour and at rate $\beta_\Delta$ through each 2-simplex (triangle) whose other two vertices are both infectious, and infectious nodes recover at rate $\mu > 0$. Let $\langle k \rangle$ and $\langle k_\Delta \rangle$ be the mean numbers of links and of 2-simplices per node. The homogeneous mean-field equation for the infectious density $\rho(t) \in [0, 1]$ is

$$\frac{d\rho}{dt} = -\mu\rho + \beta\langle k \rangle \rho(1 - \rho) + \beta_\Delta \langle k_\Delta \rangle \rho^2 (1 - \rho).$$

With $\lambda = \beta\langle k \rangle / \mu > 0$ and $\lambda_\Delta = \beta_\Delta \langle k_\Delta \rangle / \mu > 0$, the equilibria are $\rho = 0$ and the roots in $(0, 1)$ of

$$\lambda_\Delta \rho^2 - (\lambda_\Delta - \lambda)\rho + (1 - \lambda) = 0, \qquad \rho_\pm = \frac{(\lambda_\Delta - \lambda) \pm \sqrt{(\lambda + \lambda_\Delta)^2 - 4\lambda_\Delta}}{2\lambda_\Delta}.$$

1. If $\lambda > 1$, $\rho = 0$ is unstable and there is exactly one equilibrium in $(0, 1)$, namely $\rho_+$, which is stable.
2. If $\lambda < 1$ and $\lambda_\Delta \le 1$, $\rho = 0$ is the only equilibrium in $[0, 1]$ and it is stable.
3. If $\lambda_\Delta > 1$ and $2\sqrt{\lambda_\Delta} - \lambda_\Delta < \lambda < 1$, then $0 < \rho_- < \rho_+ < 1$: the disease-free state and the endemic state $\rho_+$ are both stable, separated by the unstable threshold $\rho_-$ (bistability). For $\lambda < 2\sqrt{\lambda_\Delta} - \lambda_\Delta$ only $\rho = 0$ remains.

At $\lambda = 2\sqrt{\lambda_\Delta} - \lambda_\Delta$ the two roots merge, so as $\lambda$ increases the endemic branch appears with the positive density $\rho = (\sqrt{\lambda_\Delta} - 1)/\sqrt{\lambda_\Delta}$: the transition is discontinuous.

## Expansion

Dividing by $\mu\rho$ gives $-1 + \lambda(1 - \rho) + \lambda_\Delta \rho(1 - \rho) = 0$, which is the quadratic above; its discriminant simplifies to $(\lambda + \lambda_\Delta)^2 - 4\lambda_\Delta$. The product of the roots is $(1 - \lambda)/\lambda_\Delta$ and their sum is $(\lambda_\Delta - \lambda)/\lambda_\Delta < 1$. For $\lambda > 1$ the product is negative, so exactly one root is positive. For $\lambda < 1$, two positive roots need $\lambda_\Delta > \lambda$ and a non-negative discriminant, i.e. $\lambda \ge 2\sqrt{\lambda_\Delta} - \lambda_\Delta$; if $\lambda_\Delta \le 1$ this second condition cannot hold together with $\lambda_\Delta > \lambda$, because $2\sqrt{\lambda_\Delta} - \lambda_\Delta \ge \lambda_\Delta$ when $\lambda_\Delta \le 1$. The quadratic is positive at $\rho = 1$ and its vertex lies below $1/2$, so both roots lie below $1$. Stability follows from the sign of the right-hand side, which is negative between $0$ and $\rho_-$, positive between the roots, and negative above $\rho_+$; at $\rho = 0$ the linearization is $\mu(\lambda - 1)$. Higher-order transmission ($\lambda_\Delta$) is invisible at small $\rho$, which is why the epidemic threshold for invading from a few infectious nodes stays at $\lambda = 1$ while large initial seeds can persist below it. The same discontinuous transitions, bistability and hysteresis appear on hypergraphs and temporal higher-order networks.

## Sources

- S. Majhi, M. Perc, D. Ghosh, "Dynamics on higher-order networks: a review", Journal of the Royal Society Interface 19 (2022) 20220043, section 2 (basic concepts) and section 4.1 (contagion processes), <https://doi.org/10.1098/rsif.2022.0043> (PMC8941407).
- I. Iacopini, G. Petri, A. Barrat, V. Latora, "Simplicial models of social contagion", Nature Communications 10 (2019) 2485, the model reviewed in section 4.1 above.
