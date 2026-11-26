# Global stability of HIV dynamics with latently infected cells

**Model.** Let $T$ be uninfected CD4$^+$ T cells, $I$ productively infected cells, $L$ latently infected cells and $V$ free virus:

$$
\begin{aligned}
T'&=\lambda-d_TT-kTV, & I'&=(1-p)kTV+\alpha L-d_II,\\
L'&=pkTV-\alpha L-d_LL, & V'&=Nd_II-d_VV,
\end{aligned}
$$

where a fraction $p\in(0,1)$ of infections are latent, latent cells activate at rate $\alpha$ and are cleared at rate $d_L$, and each productively infected cell releases $N$ virions over its lifetime.

**Reproduction number and equilibria.**

$$
R_L=\frac{kN\lambda}{d_Td_V}\cdot\frac{(1-p)d_L+\alpha}{d_L+\alpha}.
$$

The non-infective equilibrium is $E_{NI}=(\lambda/d_T,0,0,0)$; for $R_L>1$ the infective equilibrium is

$$
E_I=\Big(\frac{\lambda}{d_TR_L},\ \frac{d_Td_V}{kNd_I}(R_L-1),\ \frac{p\lambda}{R_L(d_L+\alpha)}(R_L-1),\ \frac{d_T}{k}(R_L-1)\Big).
$$

**Theorem.** For nonnegative parameters and positive initial data, solutions exist, are unique, remain positive and bounded. If $R_L\le1$, $E_{NI}$ is globally asymptotically stable; if $R_L>1$, $E_{NI}$ is an unstable saddle and $E_I$ is globally asymptotically stable.

## Expansion

$R_L$ is the basic reproduction number of the standard target-cell model, $kN\lambda/(d_Td_V)$, multiplied by the probability that an infection eventually becomes productive: immediately with probability $1-p$, or after latency with probability $p\,\alpha/(\alpha+d_L)$. Latency therefore lowers $R_L$ but cannot by itself eliminate infection once $R_L>1$; it does create a long-lived reservoir that persists under therapy. Global stability follows from Korobeinikov-type Lyapunov functions $\sum_ic_i(x_i-x_i^*\ln x_i)$, with weights chosen so that the latent and productive pathways combine, plus LaSalle's invariance principle.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Proof depends on

- [LaSalle's invariance principle](../../../../Dynamics/smooth-dynamics/lasalle-s-invariance-principle/lasalle.md)

## Sources

- Stephen Pankavich, "The Effects of Latent Infection on the Dynamics of HIV", arXiv:1312.3670: Section 3 (model with latently infected cells, reproduction number and equilibria): Theorems 3.1–3.3; proofs in Section 5. <https://doi.org/10.48550/arXiv.1312.3670>
