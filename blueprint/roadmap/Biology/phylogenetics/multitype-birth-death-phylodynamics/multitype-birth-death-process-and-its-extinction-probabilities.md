# Multitype birth–death process and its extinction probabilities

**Process.** Fix $d$ types and a partition $0 = t_0 < t_1 < \dots < t_n = T$ of the time axis (time runs forward from the origin $0$ to the present $T$). In interval $k$, an infected individual of type $i$

- transmits to type $j$ (a "birth", $j = i$ allowed) at rate $\lambda_{ij,k} \ge 0$, creating a new type-$j$ individual and remaining type $i$;
- becomes non-infectious (a "death") at rate $\mu_{i,k} \ge 0$;
- is sampled at rate $\psi_{i,k} \ge 0$, and upon sampling is removed with probability $r \in [0,1]$;
- changes to type $j \ne i$ at rate $m_{ij} \ge 0$ (with $m_{ii} = 0$).

At the present, each extant type-$i$ individual is sampled with probability $\rho_i$. The process starts from one individual and stops when no infected individuals remain. Epidemiological summaries are the within- and between-type effective reproduction numbers, the becoming-non-infectious rate, and the sampling proportion,

$$R_{ij,k} = \frac{\lambda_{ij,k}}{\mu_{i,k} + r\,\psi_{i,k}}, \qquad \delta_{i,k} = \mu_{i,k} + r\,\psi_{i,k}, \qquad s_{i,k} = \frac{\psi_{i,k}}{\mu_{i,k} + \psi_{i,k}} .$$

**No-sample probabilities.** Let $p_{i,k}(t)$ be the probability that an individual of type $i$ alive at time $t \in [t_{k-1}, t_k)$ has no sampled descendants by time $T$. Then $p_{i,k}$ solves the backward master equation

$$-\frac{d}{dt}\,p_{i,k}(t) = -\Big(\sum_{j=1}^{d}(\lambda_{ij,k} + m_{ij}) + \mu_{i,k} + \psi_{i,k}\Big) p_{i,k}(t) + \sum_{j=1}^{d}\lambda_{ij,k}\, p_{i,k}(t)\, p_{j,k}(t) + \sum_{j=1}^{d} m_{ij}\, p_{j,k}(t) + \mu_{i,k},$$

a Riccati-type system coupled across types, integrated from the present backward. With no sampling at the present the terminal value is $p_{i,n}(T) = 1$ (the condition written in the source); with contemporaneous sampling probability $\rho_i$ it is $p_{i,n}(T) = 1 - \rho_i$, and across interval boundaries $p$ is continuous. When some $m_{ij} > 0$ there is in general no closed form and the system is solved numerically (Runge–Kutta).

## Expansion

The equation follows from a first-step analysis over a short interval $\Delta t$ going backward: nothing happens with probability $1 - (\sum_j(\lambda_{ij} + m_{ij}) + \mu_i + \psi_i)\Delta t$; a transmission to type $j$ leaves two independent lineages of types $i$ and $j$, both of which must leave no samples (product $p_i p_j$); a type change to $j$ leaves one type-$j$ lineage; a death leaves nothing and contributes $\mu_i \Delta t$; a sampling event contributes nothing, since it produces a sample. Letting $\Delta t \to 0$ gives the ODE. With $d = 1$ the system reduces to the birth–death skyline model, and with constant rates and $r = 1$ to the classical constant-rate birth–death–sampling process. The ratio $R_{ij,k}$ is the expected number of type-$j$ infections caused by a type-$i$ individual during an infectious period of mean $1/\delta_{i,k}$ when rates stay constant and type changes are ignored.

## Sources

- D. Kühnert, T. Stadler, T. G. Vaughan, A. J. Drummond, "Phylodynamics with migration: a computational framework to quantify population structure from genomic data", Molecular Biology and Evolution (2016), New Approaches ("The Multitype Birth–Death Process", "The Probability p of Having No Sampled Descendants", Eq. (2), "Parameterization of the Multitype Birth Death Model"), <https://doi.org/10.1093/molbev/msw064> (PMC4948704).
