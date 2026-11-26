# N-strain SIS model with co-colonization

Hosts are susceptible ($S$), singly colonized by strain $i$ ($I_i$), or co-colonized by strains $i$ then $j$ ($I_{ij}$, including $I_{ii}$), as proportions of a constant population. With transmission rate $\beta$, clearance rate $\gamma$, birth and death rate $r = d$, and co-colonization factors $K_{ij} > 0$,

$$\begin{aligned} \dot S &= r - S\sum_{j} F_j - dS + \gamma(1 - S), \\ \dot I_i &= F_i S - I_i \sum_j K_{ij} F_j - (d + \gamma) I_i, \\ \dot I_{ij} &= I_i K_{ij} F_j - (d + \gamma) I_{ij}, \end{aligned} \qquad F_i = \beta\Bigl(I_i + \frac12\sum_{j}(I_{ij} + I_{ji})\Bigr).$$

Let $D_i = \frac12\sum_j (I_{ij} + I_{ji})$ (the strain-$i$ share of co-colonization), $J_i = I_i + D_i$ (hosts transmitting strain $i$), $I = \sum_i I_i$, $D = \sum_{i,j} I_{ij} = \sum_i D_i$, $T = I + D = \sum_i J_i$, $m = \gamma + d$ and $R_0 = \beta/m$.

1. **Aggregate dynamics.** $\dot S = m(1 - S) - \beta S T$ and $\dot T = \beta S T - m T$, independent of the $K_{ij}$. If $R_0 > 1$, the endemic state is $(S^*, T^*) = (1/R_0,\ 1 - 1/R_0)$, and at equilibrium $I_{ij} = \frac{\beta}{m} I_i^* K_{ij} J_j^*$.

2. **Neutral case.** If $K_{ij} \equiv k$, then on $(S, T) = (S^*, T^*)$,

$$I(t) = I^* + e^{-(m + \beta k T^*)t}\bigl(I(0) - I^*\bigr), \qquad I^* = \frac{m T^*}{m + \beta k T^*}, \qquad D^* = T^* - I^*.$$

On the invariant manifold $(S, T, I) = (S^*, T^*, I^*)$, each pair $(I_i, J_i)$ solves a linear system with eigenvalues $0$ and $-\xi < 0$; the combination $H_i \propto I_i/I^* - J_i/T^*$ decays exponentially while

$$z_i = \frac{I_i}{I^*} + \frac{2(T^*)^2}{2(T^*)^2 - D^* I^*}\Bigl(\frac{J_i}{T^*} - \frac{I_i}{I^*}\Bigr)$$

is conserved (with $\sum_i z_i = 1$). For general initial $I(0)$ on $(S, T) = (S^*, T^*)$, $I(t) \to I^*$ exponentially and $(J_i/T^*, I_i/I^*, D_i/D^*)$ converges to a common constant strain frequency $z_i^\infty$ with $\sum_i z_i^\infty = 1$ (neutral coexistence).

## Expansion

Summing the $I_i$ and $I_{ij}$ equations and using $\sum_i F_i = \beta T$ gives the $(S, T)$ block, a standard SIS system. With $K_{ij} \equiv k$ and $T = T^*$, the $I$ equation is linear with rate $m + \beta k T^*$. From $\dot I_i = m(J_i - I_i) - \beta k T^* I_i$ and $\dot J_i = \frac{\beta k}{2}(I^* J_i - T^* I_i)$, the $(I_i, J_i)$ system has matrix $\begin{pmatrix} -(m + \beta k T^*) & m \\ -\beta k T^*/2 & \beta k I^*/2 \end{pmatrix}$, whose determinant vanishes because $(m + \beta k T^*) I^* = m T^*$; $z_i$ is the coordinate along the kernel direction and $H_i$ along the decaying one, with $-\xi$ the trace.

## Sources

- S. Madec and E. Gjini, *Predicting N-strain coexistence from co-colonization interactions: epidemiology meets ecology and the replicator equation*, Bull. Math. Biol. (2020), <https://doi.org/10.1007/s11538-020-00816-w>, PMCID PMC7595998 (Section 2, model (1); Section 3.1, equations (2)–(9)).
