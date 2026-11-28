# Basic reproduction number of the multi-host multi-stage multi-vector model

**Model.** A pathogen is shared by $m$ host species and transmitted by $p$ arthropod vector species. Host species $i$ follows an $SEI^nR$ structure: recruitment $\Lambda_i$, natural death $\mu_i$, incubation rate $\nu_i$, and $n$ infectious stages $I_{1,i},\dots,I_{n,i}$, with recovery rate $\eta_{l,i}$ and progression rate $\gamma_{l,i}$ out of stage $l$ ($\gamma_{n,i}=0$). Vector species $j$ follows an $SI$ structure with recruitment $\Lambda_{v,j}$ and death rate $\mu_{v,j}+\delta_{v,j}$ (natural plus control-induced). Let $a_{i,j}$ be the biting rate of vector $j$ on host $i$, $\beta^\diamond_{i,j}$ the infectiousness of vector $j$ to host $i$, and $\beta^i_{l,j}$ the infectiousness of stage-$l$ host $i$ to vector $j$. Collect these into the $m\times p$ matrices $A=(a_{i,j})$, $B^\diamond=(\beta^\diamond_{i,j})$ and $B_l=(\beta^i_{l,j})$, and write $\circ$ for the Hadamard product. On the limiting system with host totals $N_i=\Lambda_i/\mu_i$ and vector totals $N_{v,j}=\Lambda_{v,j}/(\mu_{v,j}+\delta_{v,j})$, the infected compartments evolve as

$$
\begin{aligned}
\dot{\mathbf E} &= \operatorname{diag}^{-1}(\mathbf N_h)\operatorname{diag}(\mathbf S)\,(A\circ B^\diamond)\,\mathbf I_v - \operatorname{diag}(\mu_h+\nu_h)\,\mathbf E, \\
\dot{\mathbf I}_1 &= \operatorname{diag}(\nu)\,\mathbf E - \operatorname{diag}(\alpha_1)\,\mathbf I_1, \qquad
\dot{\mathbf I}_l = \operatorname{diag}(\gamma_{l-1})\,\mathbf I_{l-1} - \operatorname{diag}(\alpha_l)\,\mathbf I_l \quad (2\le l\le n), \\
\dot{\mathbf I}_v &= \operatorname{diag}(\mathbf S_v)\sum_{l=1}^n (A\circ B_l)^{T}\operatorname{diag}^{-1}(\mathbf N_h)\,\mathbf I_l - \operatorname{diag}(\mu_v+\delta_v)\,\mathbf I_v,
\end{aligned}
$$

where $\alpha_{l,i} = \mu_i + \eta_{l,i} + \gamma_{l,i}$. The disease-free equilibrium has $\bar{\mathbf S} = \mathbf N_h$ and $\bar{\mathbf S}_v = \mathbf N_v$, and the region where host and vector totals are bounded by these values is compact, positively invariant and attracting.

**Lemma.** The next-generation basic reproduction number is $\mathcal R_0(m,n,p)$, where

$$
\mathcal R_0^2(m,n,p) = \rho\Bigl(\operatorname{diag}(\mathbf N_v)\Bigl(\sum_{l=1}^n (A\circ B_l)^{T}\operatorname{diag}(\gamma_1\circ\cdots\circ\gamma_{l-1}\circ\nu)\,\operatorname{diag}^{-1}\bigl((\mu+\nu)\circ\alpha_1\circ\cdots\circ\alpha_l\bigr)\Bigr)\operatorname{diag}^{-1}(\mathbf N_h)\,(A\circ B^\diamond)\,\operatorname{diag}^{-1}(\mu_v+\delta_v)\Bigr)
$$

and $\rho$ denotes the spectral radius. The $l$-th summand weights stage-$l$ infectiousness by the probability $\prod_{k<l}\gamma_{k}/\alpha_{k}\cdot\nu/(\mu+\nu)$ of reaching stage $l$ and by the mean stage duration $1/\alpha_l$.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

Split the infected subsystem into new infections $\mathcal F$ and transitions $\mathcal V$ and linearise at the disease-free equilibrium. Then $F$ has the host-from-vector block $A\circ B^\diamond$ and the vector-from-host block $\operatorname{diag}(\mathbf N_v)\bigl[(A\circ B_1)^T,\dots,(A\circ B_n)^T\bigr]\operatorname{diag}^{-1}(\mathbf N_h)$, and $V$ is block lower-bidiagonal (latent to stage 1 to stage 2, and so on). Because $F$ is block anti-diagonal, $FV^{-1}$ squares to a block-diagonal matrix, and $\rho(FV^{-1})^2$ equals the spectral radius of the vector-to-vector product above. That is why the formula is stated for $\mathcal R_0^2$: one host-vector-host cycle takes two generations.

## Sources

- Derdei Mahamat Bichara, "Global analysis of multi-host and multi-vector epidemic models", Journal of Mathematical Analysis and Applications 475 (2019), 1532–1553, <https://doi.org/10.1016/j.jmaa.2019.03.030>. Published version of arXiv:1807.02918, cited next; locators there refer to the arXiv version.
- Derdei Bichara, "Global Analysis of Multi-Host and Multi-Vector Epidemic Models", arXiv 2018: Section 1 (model), Section 2, Lemma 2.1. <https://doi.org/10.48550/arXiv.1807.02918>
