# Relative fixation probability from context-dependent rate ratios

Fix a nucleotide change that causes a given amino acid replacement, and split its potential sites into two classes, inside a hypermutable context ($\mathrm{CpG}$) and outside it ($\neg\mathrm{CpG}$). For a lineage leading to two sister species, let $T_{\mathrm{CpG}}, T_{\neg\mathrm{CpG}}$ be the numbers of target sites in the inferred common ancestor and $R_{\mathrm{CpG}}, R_{\neg\mathrm{CpG}}$ the numbers of observed substitutions. The **context impact on divergence** is

$$I_{\mathrm{div}} = \frac{R_{\mathrm{CpG}} / T_{\mathrm{CpG}}}{R_{\neg\mathrm{CpG}} / T_{\neg\mathrm{CpG}}},$$

and the context impact on polymorphism $I_{\mathrm{poly}}$ is defined in the same way from counts of segregating sites. Let $I_\mu = \mu_{\mathrm{CpG}} / \mu_{\neg\mathrm{CpG}}$ be the impact on the mutation rate.

**Proposition.** Under an origination–fixation model, the per-site substitution rate of class $c$ is $k_c = 2N\mu_c\, u_c$, where $u_c$ is the mean fixation probability of a new mutation in class $c$. Hence

$$I_{\mathrm{div}} = I_\mu \cdot \frac{u_{\mathrm{CpG}}}{u_{\neg\mathrm{CpG}}}, \qquad \frac{u_{\mathrm{CpG}}}{u_{\neg\mathrm{CpG}}} = \frac{I_{\mathrm{div}}}{I_\mu}.$$

If selection on a replacement does not depend on its mutational context then $u_{\mathrm{CpG}} = u_{\neg\mathrm{CpG}}$ and $I_{\mathrm{div}} = I_\mu$; a ratio $I_{\mathrm{div}} / I_\mu < 1$ means that mutations in the hypermutable context are fixed less often, i.e. face stronger purifying selection. The analogous ratio $I_{\mathrm{poly}}/I_\mu$ measures the relative chance that a new mutation is observed as a polymorphism.

## Depends on

- [Selected origination flux and its weak-selection scaling function](../../../substitution-rate-with-selection.md)
- [Weak-mutation limit justifies the origination–fixation chain](../../weak-mutation-limit-justifies-the-origination-fi.md)

## Expansion

The factor $2N$ cancels in the ratio, so the comparison needs no estimate of population size, only target counts and substitution counts for the same replacement in the two contexts. For human–chimpanzee non-synonymous transitions, $I_{\mathrm{div}} \approx 7.1$ against $I_\mu \approx 14.5$, giving $u_{\mathrm{CpG}}/u_{\neg\mathrm{CpG}} \approx 0.49$; for human non-synonymous SNPs, $I_{\mathrm{poly}} \approx 11.2$, a ratio of about $0.77$. Neutral non-coding sites give $I_{\mathrm{div}}$ close to $I_\mu$, as expected. The stronger effect on divergence than on polymorphism indicates that the extra selection acts mostly as weak selection, which prevents fixation more than it prevents segregation. A proposed explanation is that sites not under strong selection lose their hypermutable contexts over time, so surviving CpG contexts are enriched at constrained sites.

## Sources

- S. Schmidt, A. Gerasimova, F. A. Kondrashov, I. A. Adzhubei, A. S. Kondrashov and S. Sunyaev, "Hypermutable non-synonymous sites are under stronger negative selection", *PLoS Genetics* 4 (2008), e1000281, Results Eq. (1), Tables 1–3 and Discussion, <https://doi.org/10.1371/journal.pgen.1000281> (PMC2583910).
