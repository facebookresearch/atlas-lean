# Continent–island equilibria under dominance

**Model.** An island receives one-way migration at rate $\mu$ from a continent fixed for haplotype $A_2B_2$, while $A_1$ and $B_1$ are favoured on the island with selection rates $\alpha,\beta>0$ and dominance coefficients $\vartheta,\sigma\in[-1,1]$ (genotype fitness $1+\alpha,1+\vartheta\alpha,1-\alpha$ at locus $\mathsf A$, analogously at $\mathsf B$, additive across loci). With all forces weak and recombination rate $\rho$, the island allele frequencies $p,q$ of $A_1,B_1$ and linkage disequilibrium $D$ satisfy

$$\dot p=\alpha p(1-p)\big(1+\vartheta(1-2p)\big)+\beta D\big(1+\sigma(1-2q)\big)-\mu p,$$

$$\dot q=\beta q(1-q)\big(1+\sigma(1-2q)\big)+\alpha D\big(1+\vartheta(1-2p)\big)-\mu q,$$

$$\dot D=D\big[\alpha(1-2p)(1+\vartheta(1-2p))+\beta(1-2q)(1+\sigma(1-2q))\big]-\rho D+\mu(pq-D).$$

**Single-locus polymorphisms.** With $q=D=0$ the internal equilibria of locus $\mathsf A$ solve $\alpha(1-p)(1+\vartheta(1-2p))=\mu$, i.e.

$$p_\pm=\frac{1+3\vartheta\pm\sqrt{(1-\vartheta)^2+8\mu\vartheta/\alpha}}{4\vartheta}\qquad(\vartheta\ne0),$$

and analogously $q_\pm$; within the one-locus system the equilibrium at $p_-$ is asymptotically stable whenever admissible and the one at $p_+$ is always unstable. The continental fixation $p=0$ loses stability exactly when $\mu<\alpha(1+\vartheta)$, the invasion rate of a rare island-favoured allele, which appears in heterozygotes.

**Theorem.**

1. Under weak migration and strictly intermediate dominance ($|\vartheta|,|\sigma|<1$) there is a unique, globally asymptotically stable full polymorphism $F_\mu$.
2. Under linkage equilibrium (strong recombination, $\rho\gg\max\{\alpha,\beta,\mu\}$, $D=0$) the dynamics decouple into the two one-locus dynamics, and the possible full polymorphisms are the four products of $p_\pm$ and $q_\pm$; only $F_1=(p_-,q_-)$ can be stable, and it is stable whenever admissible. If moreover $-1<\vartheta<1$ and $-1<\sigma<1$, then, with $\mu$ as the bifurcation parameter, exactly seven bifurcation patterns occur for open sets of parameters $(\alpha,\beta,\vartheta,\sigma,\rho)$, and which one applies is determined by $\vartheta,\sigma$ and the ratio $\alpha/\beta$ (source Theorem 4.1, stated for $0<\alpha<\zeta_1\beta$, $\zeta_1=(1+\sigma)/(1+\vartheta)$; the case $\alpha>\zeta_1\beta$ follows by exchanging the loci). The count does not cover the boundary $\vartheta=-1$ or $\sigma=-1$ (a completely recessive island allele) or non-generic parameter values. For example, at $\vartheta=-1$ the invasion rate $\alpha(1+\vartheta)$ vanishes, so $p=0$ is asymptotically stable for every $\mu>0$. That gives a pattern outside the seven, all of which start, for small $\mu$, with $p=0$ unstable.
3. For completely linked loci ($\rho=0$) only two bifurcation patterns occur, those of a single diallelic locus.
4. For sufficiently strong migration the continental haplotype swamps the island and no polymorphism is maintained.

## Expansion

The quadratic for $p$ comes from $2\vartheta p^2-(1+3\vartheta)p+(1+\vartheta-\mu/\alpha)=0$, whose discriminant is $(1-\vartheta)^2+8\mu\vartheta/\alpha$; for $\vartheta\to0$ the root $p_-$ tends to the no-dominance value $1-\mu/\alpha$. Dominance of the island-favoured allele ($\vartheta>0$) raises the swamping threshold to $\alpha(1+\vartheta)$ because rare alleles are seen in heterozygotes; recessivity ($\vartheta<0$) lowers it; when both $p_\pm$ are admissible, the unstable $p_+$ separates the stable polymorphism $p_-$ from another attractor. Without epistasis and with $D=0$ each locus is a one-locus migration–selection (equivalently mutation–selection) gradient system, so the two-locus phase portrait is a Cartesian product. With $\rho=0$ the two loci behave as one locus with haplotypes $A_1B_1$ and $A_2B_2$.

## Depends on

- [Weak- and strong-migration limits with intermediate dominance](weak-and-strong-migration-limits-with-intermediate-dominance.md)
- [Gametic linkage disequilibrium](../../../../quantitative-genetics/dominance-linkage-disequilibrium/ld-d.md)

## Sources

- A. Akerman, R. Bürger, "The consequences of dominance and gene flow for local adaptation and differentiation at two linked loci", *Theoretical Population Biology* 94:42–62 (2014), Section 4: equations (4.2), (4.7), (4.8), (4.11)–(4.13), Theorems 4.1 and 4.2, <https://doi.org/10.1016/j.tpb.2014.04.001>, PMCID: PMC4045392.
