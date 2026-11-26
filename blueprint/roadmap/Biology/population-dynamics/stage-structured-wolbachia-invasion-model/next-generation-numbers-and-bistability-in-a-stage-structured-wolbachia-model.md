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

**Equilibria.** The infection-free equilibrium has $L_u^0=K_l(1-1/G_0^u)$ (exists iff $G_0^u>1$); the complete-infection equilibrium has $L_w^c=K_l(1-1/G_0^w)$ (exists iff $G_0^w>1$); the other compartments are proportional to $L$ (e.g. $F=b_f\psi L/\mu_f$).

**Invasion number.** The next-generation matrix of the infected compartments at the infection-free equilibrium gives
$$\mathcal R_0=\frac{G_0^w}{G_0^u}=\frac{v_w\,\mu_{fu}\,\phi_w\,(\delta+\mu_{eu})}{\mu_{fw}\,\phi_u\,(\delta+\mu_{ew})}.$$

**Theorem.**
1. The infection-free equilibrium is locally asymptotically stable if $G_0^u>1$ and $\mathcal R_0<1$.
2. The complete-infection equilibrium is locally asymptotically stable if $G_0^w>1$.
3. With perfect maternal transmission ($v_w=1$), the biologically relevant endemic (coexistence) equilibrium exists for $\mathcal R_0<1$, $G_0^w>1$ and is unstable.

Hence for $\mathcal R_0<1<G_0^w$ the system is bistable (a backward bifurcation in $\mathcal R_0$): a small Wolbachia introduction dies out, while releases pushing the infected fraction above the unstable endemic level go to complete infection.

## Expansion

At the infection-free state the larval density satisfies $\mathcal K=1/G_0^u$, so the infected cohort's effective reproduction is $G_0^w\mathcal K=G_0^w/G_0^u$, which is why $\mathcal R_0$ is a ratio: infected mosquitoes compete for the same larval resource that uninfected mosquitoes have already saturated. Stability is proved by block-triangular Jacobians of Metzler type: a Metzler block $\begin{pmatrix}A&B\\C&D\end{pmatrix}$ is stable iff $A$ and the Schur complement $D-CA^{-1}B$ are, and the relevant Schur complements reduce to $\mu_f(1/G_0-1)$, negative iff $G_0>1$. Cytoplasmic incompatibility creates positive frequency dependence: the more infected males, the lower uninfected fitness, so the unstable endemic equilibrium is the frequency at which the two cohorts' fitnesses balance. For wAlbB in Anopheles albimanus at baseline parameters $\mathcal R_0\approx0.68$ and the threshold is an infected fraction of about $0.34$ among females.

## Sources

- Florez D, Young AJ, Bernabé KJ, Hyman JM, Hyman JM, Qu Z, "Modeling Sustained Transmission of <i>Wolbachia</i> among <i>Anopheles</i> Mosquitoes: Implications for Malaria Control in Haiti" (2023), model (1)-(3), next-generation numbers (4)-(5), equilibria (6)-(9), $\mathcal R_0$ (Section 2.2.2), Theorems 1-3 and Appendices A-B, <https://doi.org/10.3390/tropicalmed8030162>, PMCID PMC10056903.
