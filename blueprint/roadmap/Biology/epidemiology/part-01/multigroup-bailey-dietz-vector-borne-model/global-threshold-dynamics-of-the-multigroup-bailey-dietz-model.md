# Global threshold dynamics of the multigroup Bailey–Dietz model

**Model.** For groups $i = 1, \dots, n$ let host group $i$ have $S_{h,i}, I_{h,i}, R_{h,i}$ with recruitment $\Lambda_{h,i}$, death $\mu_{h,i}$ and recovery $\gamma_{h,i}$, and let vector group $i$ have $S_{v,i}, I_{v,i}$ with recruitment $\Lambda_{v,i}$ and death $\mu_{v,i}$:

$$
\begin{aligned}
\dot S_{h,i} &= \Lambda_{h,i} - S_{h,i}\sum_{j=1}^nL_{ij}(N_h,N_v)I_{v,j} - \mu_{h,i}S_{h,i}, \\
\dot I_{h,i} &= S_{h,i}\sum_{j=1}^nL_{ij}(N_h,N_v)I_{v,j} - (\gamma_{h,i}+\mu_{h,i})I_{h,i}, \\
\dot R_{h,i} &= \gamma_{h,i}I_{h,i} - \mu_{h,i}R_{h,i}, \\
\dot S_{v,i} &= \Lambda_{v,i} - S_{v,i}\sum_{j=1}^nM_{ij}(N_h,N_v)I_{h,j} - \mu_{v,i}S_{v,i}, \\
\dot I_{v,i} &= S_{v,i}\sum_{j=1}^nM_{ij}(N_h,N_v)I_{h,j} - \mu_{v,i}I_{v,i}.
\end{aligned}
$$

The contact functions $L_{ij}, M_{ij}$ are smooth and positive for positive population vectors, so many force-of-infection forms are covered (mass action, frequency dependence, residence-time mixing). Total populations converge to $\bar N_{h,i} = \Lambda_{h,i}/\mu_{h,i}$ and $\bar N_{v,i} = \Lambda_{v,i}/\mu_{v,i}$. On this limit set the dynamics reduce to

$$
\dot S_h = \Lambda_h - \mathrm{diag}(S_h)LI_v - \mathrm{diag}(\mu_h)S_h, \quad \dot I_h = \mathrm{diag}(S_h)LI_v - \mathrm{diag}(\mu_h+\gamma_h)I_h, \quad \dot I_v = \mathrm{diag}(\bar N_v - I_v)MI_h - \mathrm{diag}(\mu_v)I_v,
$$

with $L = L(\bar N_h, \bar N_v)$ and $M = M(\bar N_h, \bar N_v)$ constant.

**Basic reproduction number.**

$$
\mathcal{R}_0 = \rho\begin{pmatrix} 0 & \mathrm{diag}(\mu_h+\gamma_h)^{-1}\mathrm{diag}(\bar N_h)L \\ \mathrm{diag}(\mu_v)^{-1}\mathrm{diag}(\bar N_v)M & 0\end{pmatrix},
$$

and, when the contact network is strongly connected,
$\mathcal{R}_0^2 = \rho\left(\mathrm{diag}(\mu_h+\gamma_h)^{-1}\mathrm{diag}(\bar N_h)L\,\mathrm{diag}(\mu_v)^{-1}\mathrm{diag}(\bar N_v)M\right)$, the host-to-host reproduction number over two transmission steps.

**Theorem.** Assume the host–vector contact network $\begin{pmatrix}0 & L\\ M & 0\end{pmatrix}$ is irreducible. For the reduced system:
1. There is a unique endemic equilibrium, with all components positive, if and only if $\mathcal{R}_0 > 1$; when it exists it is locally asymptotically stable.
2. If $\mathcal{R}_0 \le 1$, the disease-free equilibrium is globally asymptotically stable; if $\mathcal{R}_0 > 1$, it is unstable.
3. If $\mathcal{R}_0 > 1$, the endemic equilibrium is globally asymptotically stable.

Equilibria are therefore exactly the disease-free state and, above threshold, one endemic state, for any contact functions and any strongly connected bipartite contact structure.

## Depends on

- [Irreducibility of the bipartite host–vector contact network](irreducibility-of-the-bipartite-host-vector-contact-network.md)
- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

Existence and uniqueness of the endemic equilibrium follow from writing the equilibrium condition as a fixed point of a monotone, strictly sublinear, bounded map on $\mathbb{R}^n_{\ge 0}$ with irreducible derivative at $0$. Such a map has a positive fixed point exactly when the spectral radius of its derivative exceeds $1$, and then only one (Hethcote–Thieme fixed-point lemma). For the disease-free equilibrium, the linear Lyapunov function $\langle \xi, I_h\rangle + \langle \eta, I_v\rangle$ built from the positive left Perron vector $(\xi, \eta)$ of the next-generation matrix has nonpositive derivative when $\mathcal{R}_0 \le 1$, and LaSalle's principle finishes the proof. For the endemic equilibrium a Volterra-type function $\sum_i c_i(x_i - \bar x_i\log x_i)$ is used, with weights that make the cross terms cancel: they are the spanning-tree sums of the transitive contact multigraph with edges $L_{ik}M_{kj} \neq 0$, i.e. the kernel of its graph Laplacian (Kirchhoff's matrix-tree theorem). For the full model, which is triangular with the total populations converging, the standard result on triangular systems (a globally stable equilibrium of the limiting subsystem, together with forward-bounded trajectories, gives global stability of the full system) is the tool for lifting these conclusions.

## Sources

- Abderrahman Iggidr, Gauthier Sallet and Max O. Souza, "On the dynamics of a class of multi-group models for vector-borne diseases", arXiv:1409.1470 (2014), Section 2 (model, Theorem 2.1 on triangular systems), Section 3 (definition of $\mathcal{R}_0$, Theorem 3.1, Lemma 3.1), Section 4 (Theorem 4.1, Lemma 4.2, Proposition 4.1, Theorem 4.2), <https://doi.org/10.48550/arXiv.1409.1470>. Published version: Journal of Mathematical Analysis and Applications 441(2) (2016), 723–743, <https://doi.org/10.1016/j.jmaa.2016.04.003>; locators above refer to the arXiv version.
