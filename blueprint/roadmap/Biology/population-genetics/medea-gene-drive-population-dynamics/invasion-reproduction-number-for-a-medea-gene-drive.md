# Invasion reproduction number for a Medea gene drive

**Model.** *Medea* is a maternal-effect gene drive: offspring of a *Medea*-carrying mother die as embryos unless they inherit the *Medea* allele. A continuous-time compartmental model tracks eggs $E_i$, females $F_i$ and males $M_i$ of genotypes $i=0$ (wild type), $1$ (heterozygote $M+$) and $2$ (homozygote $MM$), with density-dependent egg survival (carrying capacity $K$), maturation rate $\psi$, egg mortalities $\mu_{e i}$, adult mortalities $\mu_{f i}$, $\mu_{m i}$ and fecundities $\phi_{ij}$ of a genotype-$i$ female mated with a genotype-$j$ male. Define the population reproduction numbers
$$\mathcal{G}_{00} = \frac12\,\frac{\psi}{\psi+\mu_{e0}}\,\frac{\phi_{00}}{\mu_{f0}}, \qquad \mathcal{G}_{011} = \frac14\,\frac{\psi}{\psi+\mu_{e1}}\,\frac{\phi_{01}}{\mu_{f0}}, \qquad \mathcal{G}_{101} = \frac14\,\frac{\psi}{\psi+\mu_{e1}}\,\frac{\phi_{10}}{\mu_{f1}},$$
the expected numbers of female offspring of the tracked genotype from the crosses $F_0\times M_0\to F_0$, $F_0\times M_1\to F_1$ and $F_1\times M_0\to F_1$.

**Proposition.** At the *Medea*-free equilibrium (which exists when $\mathcal{G}_{00}>1$), the next-generation matrix of the *Medea*-carrying compartments gives
$$\mathcal{R}_0 = \frac{(\mu_{f1}\mu_{m0}\phi_{01} + \mu_{f0}\mu_{m1}\phi_{10})(\mu_{e0}+\psi)}{2\,\mu_{f1}\mu_{m1}\phi_{00}(\mu_{e1}+\psi)} = \frac{\mathcal{G}_{011}/\mu_{m1} + \mathcal{G}_{101}/\mu_{m0}}{\mathcal{G}_{00}/\mu_{m0}}.$$
If $\mathcal{R}_0>1$, *Medea* invades from arbitrarily low frequency; if $\mathcal{R}_0<1$ (any fitness cost), the *Medea*-free equilibrium is locally stable and establishment requires a release above a threshold. The *Medea*-complete equilibrium has $E_2 = (1-1/\mathcal{G}_{22})K$, $F_2 = \frac{\psi}{2\mu_{f2}}E_2$, $M_2 = \frac{\psi}{2\mu_{m2}}E_2$ with $\mathcal{G}_{22} = \frac12\frac{\psi}{\psi+\mu_{e2}}\frac{\phi_{22}}{\mu_{f2}}$, and all other compartments zero.

## Expansion

Near the *Medea*-free state, new $M+$ individuals arise only from the two heterozygous crosses with wild-type partners, each producing half $M+$ offspring, and wild-type partners are at their equilibrium abundance, which is why $\mathcal{G}_{00}$ appears as the normalisation. The linearised matrix of the *Medea*-carrying compartments is Metzler, and a block criterion for Metzler stability links local stability of the *Medea*-free equilibrium to the next-generation threshold $\mathcal{R}_0=1$. Without fitness costs $\mathcal{R}_0=1$; any cost makes *Medea* a threshold-dependent drive, so replacement is bistable and depends on release size.

## Sources

- Z. Qu, "Modeling Medea gene-drive population replacement: thresholds and release strategies", arXiv:2609.06687, Section 3 (population reproduction numbers, basic reproduction number and Medea-complete equilibrium). <https://doi.org/10.48550/arXiv.2609.06687>
