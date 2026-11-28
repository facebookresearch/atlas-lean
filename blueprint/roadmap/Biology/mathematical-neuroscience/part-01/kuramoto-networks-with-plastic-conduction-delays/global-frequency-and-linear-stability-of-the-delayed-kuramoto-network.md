# Global frequency and linear stability of the delayed Kuramoto network

Let $N \ge 2$ phase oscillators with common natural frequency $\omega_0 \in \mathbb{R}$, coupling gain $g > 0$, adjacency coefficients $a_{ij} \in \{0,1\}$ with no self-coupling ($a_{ii} = 0$ for every $i$) and fixed conduction delays $\tau^0_{ij} \ge 0$ evolve by

$$\frac{d\theta_i}{dt}(t) = \omega_0 + \frac{g}{N}\sum_{j=1}^N a_{ij}\,\sin\bigl(\theta_j(t-\tau^0_{ij}) - \theta_i(t)\bigr), \qquad 1 \le i \le N.$$

An in-phase synchronized solution $\theta_i(t) = \Omega t$ (for every $i$) exists exactly when $\Omega$ solves the scalar fixed-point equation

$$\Omega = \omega_0 + \frac{g}{N}\sum_{j=1}^N a_{ij}\sin(-\Omega\tau^0_{ij})$$

for every $i$ (automatic when every row of $(a_{ij})$ has the same delay profile), and then $\Omega \in [\omega_0 - g, \omega_0 + g]$. Writing $\theta_i = \Omega t + \epsilon_i$, the perturbations obey the linear delay system

$$\frac{d\epsilon_i}{dt}(t) = \frac{g}{N}\sum_{j=1}^N a_{ij}\cos(\Omega\tau^0_{ij})\bigl(\epsilon_j(t-\tau^0_{ij}) - \epsilon_i(t)\bigr),$$

and $\lambda \in \mathbb{C}$ is a characteristic root iff $\det M_\lambda = 0$ for the $N \times N$ matrix

$$(M_\lambda)_{ii} = \lambda + \frac{g}{N}\sum_{j} a_{ij}\cos(\Omega\tau^0_{ij}), \qquad (M_\lambda)_{ij} = -\frac{g}{N}\,a_{ij}\cos(\Omega\tau^0_{ij})\,e^{-\lambda\tau^0_{ij}} \quad (i \ne j).$$

The synchronized state is linearly stable if every root other than the neutral root $\lambda = 0$ (common phase shift) has $\operatorname{Re}\lambda < 0$; a Lyapunov-functional sufficient condition is $\cos(\Omega\tau^0_{ij}) > 0$ for all connected pairs. The source's model, Eq. (1), sums over all $j$ and does not exclude $a_{ii} = 1$, but the diagonal of its matrix, Eq. (17), printed as $\lambda + \frac{g}{N}\sum_j a_{ij}\cos(\Omega\tau^0_{ij})$, omits the $j = i$ term $-\frac{g}{N}a_{ii}\cos(\Omega\tau^0_{ii})e^{-\lambda\tau^0_{ii}}$ of the linear delay system; the page therefore assumes no self-coupling, under which Eq. (17) holds as printed.

## Expansion

Substituting $\theta_i = \Omega t$ into the equation gives the frequency condition. Linearizing $\sin(-\Omega\tau^0_{ij} + \epsilon_j(t-\tau^0_{ij}) - \epsilon_i(t))$ about the phase-locked solution and using the frequency condition to cancel the constant terms gives the linear delay system; the ansatz $\epsilon_i = v_i e^{\lambda t}$ turns it into $M_\lambda v = 0$. The vector $v = (1,\dots,1)$ always gives $\lambda = 0$, reflecting the rotational invariance $\theta_i \mapsto \theta_i + c$.

## Sources

- S. H. Park and J. Lefebvre, "Synchronization and resilience in the Kuramoto white matter network model with adaptive state-dependent delays", Journal of Mathematical Neuroscience 10 (2020) 16, <https://doi.org/10.1186/s13408-020-00091-y>, PMCID PMC7494726. Section "Synchronized state and stability with plastic delays", Eqs. (15)–(17) (the non-plastic case $\kappa = 0$).
