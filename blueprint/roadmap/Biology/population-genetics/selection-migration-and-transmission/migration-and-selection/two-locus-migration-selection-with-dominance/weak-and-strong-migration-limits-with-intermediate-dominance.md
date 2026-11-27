# Weak- and strong-migration limits with intermediate dominance

**Model.** Two diallelic loci $\mathsf A$ (alleles $A_1,A_2$) and $\mathsf B$ ($B_1,B_2$) with recombination probability $r\in[0,\tfrac12]$ in a population of two demes $k=1,2$. In deme $k$ the one-locus fitnesses at $\mathsf A$ are $A_1A_1:1+a_k$, $A_1A_2:1+\vartheta_ka_k$, $A_2A_2:1-a_k$ (similarly $b_k,\sigma_k$ at $\mathsf B$), fitness is additive across loci (no epistasis), $a_1>0>a_2$, $b_1>0>b_2$ (selection in opposite directions), $|a_k|+|b_k|<1$, and dominance is intermediate, $|\vartheta_k|,|\sigma_k|\le1$. A fraction $m_k<\tfrac12$ of deme $k$ are immigrants from the other deme each generation; selection and recombination act in each deme, followed by migration.

**Theorem.**

1. (Weak migration.) If dominance is strictly intermediate, $-1<\vartheta_k,\sigma_k<1$ for $k=1,2$, then for sufficiently small $m_1,m_2>0$ there is a unique internal equilibrium $F_m$, a perturbation of the fully polymorphic equilibrium $F_0$ in which each deme is fixed for its locally favoured haplotype, and $F_m$ is globally asymptotically stable.
2. (Recessive local alleles.) If the locally favoured alleles are recessive ($\vartheta_1=\sigma_1=-1$, $\vartheta_2=\sigma_2=1$), nine internal equilibria can coexist when recombination is strong, of which only $F_m$ is stable, simultaneously with the four monomorphisms and four single-locus polymorphisms.
3. (Strong migration.) If migration is strong relative to selection and recombination, a stable fully polymorphic equilibrium exists for arbitrarily strong migration if and only if both loci show average overdominance (heterozygotes fitter than both homozygotes after averaging fitnesses over demes with the leading left eigenvector of the backward migration matrix); it is then globally asymptotically stable. Under intermediate dominance without average overdominance, no polymorphism is maintained under strong migration.

## Expansion

(1) uses that without migration all 16 equilibria are hyperbolic when dominance is strictly intermediate, so by Karlin–McGregor perturbation each persists as at most one nearby equilibrium; the unstable full and single-locus polymorphisms leave the simplex, leaving $F_m$, and global stability follows from Bürger's general weak-migration theorem for multilocus additive fitness. At the boundary cases $\vartheta_1=1$ or $\sigma_1=-1$ (and the mirror cases) hyperbolicity fails and allele frequencies scale with $\sqrt m$, as in mutation–selection balance with dominant alleles. (3) is the strong-migration limit: the demes mix, and the dynamics reduce to a panmictic two-locus selection–recombination system with spatially averaged fitnesses, which preserves a polymorphism only through heterozygote advantage.

## Sources

- A. Akerman, R. Bürger, "The consequences of dominance and gene flow for local adaptation and differentiation at two linked loci", *Theoretical Population Biology* 94:42–62 (2014), Section 2 (equations (2.1)–(2.6)), Sections 3.1 and 3.2, Appendix A.1, <https://doi.org/10.1016/j.tpb.2014.04.001>, PMCID: PMC4045392.
