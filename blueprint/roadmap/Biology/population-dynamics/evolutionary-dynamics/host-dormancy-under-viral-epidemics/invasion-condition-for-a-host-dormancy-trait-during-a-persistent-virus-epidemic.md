# Invasion condition for a host dormancy trait during a persistent lytic virus epidemic

**Model.** Two host types compete in a logistic chemostat-like population with virions (type 3). Type 1 hosts are active ($1a$) or infected ($1i$); type 2 hosts are active ($2a$), dormant ($2d$) or infected ($2i$). Active hosts of type $j$ reproduce at rate $\lambda_j$ and die at rate $\mu_1 + C(n_1 + n_2)$, with $0 < \mu_1 < \lambda_2 < \lambda_1$ (dormancy carries a reproductive cost). A virion contacts an active host at rate $D$; for type 1 this always gives infection, while for type 2 a fraction $q$ of contacts instead triggers dormancy (the virion being lost only in the infecting contacts). Infected cells recover at rate $r$ or lyse at rate $v$, releasing $m$ virions; dormant cells resuscitate at rate $\sigma$ and die at rate $\kappa\mu_1$; virions decay at rate $\mu_3$. The individual-based Markov chain $\mathbf{N}^K$, rescaled by the carrying capacity $K$, converges to

$$\begin{aligned}
\dot n_{1a} &= n_{1a}(\lambda_1 - \mu_1 - C(n_1+n_2) - Dn_3) + r n_{1i}, & \dot n_{1i} &= D n_3 n_{1a} - (r+v)n_{1i},\\
\dot n_{2a} &= n_{2a}(\lambda_2 - \mu_1 - C(n_1+n_2) - Dn_3) + r n_{2i} + \sigma n_{2d}, & \dot n_{2d} &= qDn_3 n_{2a} - (\kappa\mu_1 + \sigma)n_{2d},\\
\dot n_{2i} &= (1-q)Dn_3 n_{2a} - (r+v)n_{2i}, & \dot n_3 &= -Dn_3 n_{1a} - (1-q)Dn_3 n_{2a} + mv(n_{1i}+n_{2i}) - \mu_3 n_3.
\end{aligned}$$

**Persistent epidemic.** Without type 2, a coordinatewise positive equilibrium $(n_{1a}^*, n_{1i}^*, n_3^*)$ (persistent virus epidemic) exists iff $mv > r + v$ and $\bar n_{1a} = (\lambda_1 - \mu_1)/C > n_{1a}^* = \mu_3(r+v)/\big(D(mv - (r+v))\big)$.

**Theorem.** Assume $r\kappa\mu_1 \ne v\sigma$ and that the persistent-epidemic equilibrium is asymptotically stable for the type-1–virus subsystem.
1. *Linear stability.* The equilibrium $(n_{1a}^*, n_{1i}^*, 0, 0, 0, n_3^*)$ of the full system is unstable if

$$\lambda_1 - \lambda_2 < \frac{qDn_3^*(v\sigma - r\kappa\mu_1)}{(r+v)(\kappa\mu_1 + \sigma)}$$

and asymptotically stable if the reverse strict inequality holds.
2. *Stochastic invasion.* Start $\mathbf{N}^K$ from the resident equilibrium with a single active type-2 individual. For all sufficiently small $\beta > 0$, the probability that type 2 reaches total size $\beta K$ before dying out converges as $K \to \infty$ to $1 - s_{2a}$, where $s_{2a}$ is the first coordinate of the smallest positive solution of the extinction-probability equations of the three-type branching process (active, dormant, infected) that linearises type 2 at the resident equilibrium. $s_{2a} < 1$ exactly under the instability condition of item 1; then, on invasion, the time to reach $\beta K$ is $(1/\lambda^* + o(1))\log K$, with $\lambda^* > 0$ the leading eigenvalue of the linearised mean matrix, while on extinction the invader dies out in time $o(\log K)$.

Hence when $v\sigma > r\kappa\mu_1$ (dormant cells survive the epidemic better than infected cells recover) a dormancy trait invades despite its reproductive cost, as long as that cost is below the right-hand side.

## Proof sketch

Near the resident equilibrium, rare type-2 individuals evolve as a three-type branching process with virion density frozen at $n_3^*$. An active type-2 cell has net growth $\lambda_2 - \mu_1 - C(n_{1a}^* + n_{1i}^*) - Dn_3^*$ and is diverted at rate $qDn_3^*$ into dormancy, from which it returns with probability $\sigma/(\kappa\mu_1 + \sigma)$, instead of into infection, from which it returns with probability $r/(r+v)$. Using the resident equilibrium relation $\lambda_1 - \mu_1 - C n_1^* - Dn_3^* + rDn_3^*/(r+v) = 0$, the sign of the Perron root reduces to the stated inequality. The three-phase invasion argument (branching approximation, deterministic transit, and the coupled extinction time) gives the $\log K$ asymptotics.

## Sources

- Jochen Blath and András Tóbiás, "Emergence of microbial host dormancy during a persistent virus epidemic", *Journal of Mathematical Biology* 92 (2026), 60, <https://doi.org/10.1007/s00285-026-02372-8>. Preprint version: arXiv:2504.04943 (2025), Section 2 (Propositions 2.1, 2.3, 2.5) and Section 3 (Theorems 3.1 and 3.5), <https://doi.org/10.48550/arXiv.2504.04943>.
