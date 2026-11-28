# Next-generation numbers and bistability in a stage-structured Wolbachia model

**Model.** Uninfected ($u$) and Wolbachia-infected ($w$) mosquitoes are tracked as eggs $E$, larvae/pupae $L$, adult males $M$ and adult females $F$:

$$\begin{aligned}
\dot M_j&=b_m\psi L_j-\mu_{mj}M_j, &\dot F_j&=b_f\psi L_j-\mu_{fj}F_j\quad(j=u,w),\\
\dot E_u&=\phi_u\,\mathcal M_u\,F_u+\phi_w v_u F_w-(\delta+\mu_{eu})E_u, &\dot E_w&=v_w\phi_w F_w-(\delta+\mu_{ew})E_w,\\
\dot L_j&=\delta\,\mathcal K\,E_j-(\psi+\mu_l)L_j, &\mathcal K&=1-\frac{L_u+L_w}{K_l},
\end{aligned}$$

where $\mathcal M_u=M_u/(M_u+M_w)$ is the probability that an uninfected female mates with an uninfected male (complete cytoplasmic incompatibility: uninfected females mated to infected males lay no viable eggs), $v_w\in(0,1]$ is the maternal transmission fraction, $v_u=1-v_w$, $b_f+b_m=1$, $\psi$ is the emergence rate, $\delta$ the hatching rate, $\phi_j$ egg-laying rates and $\mu$ death rates.

**Next-generation numbers.**

$$G_0^u=\frac{b_f\psi}{\psi+\mu_l}\cdot\frac{\delta}{\delta+\mu_{eu}}\cdot\frac{\phi_u}{\mu_{fu}},\qquad G_0^w=v_w\,\frac{b_f\psi}{\psi+\mu_l}\cdot\frac{\delta}{\delta+\mu_{ew}}\cdot\frac{\phi_w}{\mu_{fw}},$$

the expected number of same-type female offspring per female per generation in a near-empty habitat.

**Equilibria.** The infection-free equilibrium has $L_u^0=K_l(1-1/G_0^u)$ (exists iff $G_0^u>1$); with perfect maternal transmission $v_w=1$ (so $v_u=0$), the complete-infection equilibrium has $L_w^c=K_l(1-1/G_0^w)$ (exists iff $G_0^w>1$), while for $v_w<1$ there is no complete-infection equilibrium, since $E_u=L_u=F_u=M_u=0$ and $F_w>0$ give $\dot E_u=\phi_wv_uF_w>0$ (the source: "During imperfect maternal transmission, $v_w<1$, ... the CIE cannot be achieved"); the other compartments are proportional to $L$ (e.g. $F=b_f\psi L/\mu_f$).

**Invasion number.** The next-generation matrix of the infected compartments at the infection-free equilibrium gives

$$\mathcal R_0=\frac{G_0^w}{G_0^u}=\frac{v_w\,\mu_{fu}\,\phi_w\,(\delta+\mu_{eu})}{\mu_{fw}\,\phi_u\,(\delta+\mu_{ew})}.$$

**Theorem.**

1. The infection-free equilibrium is locally asymptotically stable if $G_0^u>1$ and $\mathcal R_0<1$.
2. With perfect maternal transmission $v_w=1$ (so $v_u=0$), the complete-infection equilibrium is locally asymptotically stable if $G_0^w>1$.

Hence, with perfect maternal transmission $v_w=1$ (so $v_u=0$), for $\mathcal R_0<1<G_0^w$ (which forces $G_0^u>G_0^w>1$) both boundary equilibria are locally asymptotically stable, so the system is bistable: a small Wolbachia introduction dies out, while a large enough release goes to complete infection.

**Numerical observation (not part of the statement).** The source also reports, as a conjecture it checks only numerically (its Theorem 3), that with perfect maternal transmission ($v_w=1$) an endemic (coexistence) equilibrium exists for $\mathcal R_0<1<G_0^w$ and is unstable, so that it separates the two basins (a backward bifurcation in $\mathcal R_0$).

## Depends on

- [Basic reproduction number of the next-generation matrix](../../../../epidemiology/next-generation-matrix-and-the-basic-reproductio/r0.md)

## Proof depends on

- [$R_0$ as a threshold for the linearized infected subsystem](../../../../epidemiology/next-generation-matrix-and-the-basic-reproductio/is-hurwitz-sub-iff-r0-lt-one.md)

## Expansion

At the infection-free state the larval density satisfies $\mathcal K=1/G_0^u$, so the infected cohort's effective reproduction is $G_0^w\mathcal K=G_0^w/G_0^u$, which is why $\mathcal R_0$ is a ratio: infected mosquitoes compete for the same larval resource that uninfected mosquitoes have already saturated. Stability is proved by block-triangular Jacobians of Metzler type: a Metzler block $\begin{pmatrix}A&B\\C&D\end{pmatrix}$ is stable iff $A$ and the Schur complement $D-CA^{-1}B$ are, and the relevant Schur complements reduce to $\mu_f(1/G_0-1)$, negative iff $G_0>1$. Cytoplasmic incompatibility creates positive frequency dependence: the more infected males, the lower uninfected fitness, which is why the numerically observed endemic equilibrium sits at the frequency where the two cohorts' fitnesses balance. For wAlbB in Anopheles albimanus at baseline parameters $\mathcal R_0\approx0.68$, and the source's simulations place the threshold at an infected fraction of about $0.34$ among females.

## Sources

- Florez D, Young AJ, Bernabé KJ, Hyman JM, Qu Z, "Modeling Sustained Transmission of *Wolbachia* among *Anopheles* Mosquitoes: Implications for Malaria Control in Haiti", *Tropical Medicine and Infectious Disease* 8 (2023) 162, model (1)-(3), next-generation numbers (4)-(5), equilibria (6)-(9), $\mathcal R_0$ (Section 2.2.2), Theorems 1-2 with Appendices A-B (proved), Theorem 3 (verified numerically, Section 2.2.3), <https://doi.org/10.3390/tropicalmed8030162>, PMCID PMC10056903.
