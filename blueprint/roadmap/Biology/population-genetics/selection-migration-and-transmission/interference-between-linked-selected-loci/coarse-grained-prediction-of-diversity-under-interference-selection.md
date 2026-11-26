# Coarse-grained prediction of neutral diversity under interference selection

Work in the asexual model of the [infinitesimal limit of linked selection](infinitesimal-limit-of-linked-selection.md): population size $N$, selected mutation rate $U$, effect $s$, fitness standard deviation $\sigma$. The plane of $(Ns, NU)$ splits into a **background selection regime**, where the structured coalescent on the Poisson fitness classes is accurate, and an **interference selection regime**, where the fitness distribution departs from the Poisson prediction and the structured coalescent fails. Because convergence to the infinitesimal limit is fast, the neutral diversity of an interference-regime population is approximated by that of a background-regime population with the same $N\sigma$:

1. compute $N\sigma$ from $(Ns, NU)$ by traveling-wave theory;
2. move along the curve of constant $N\sigma$ to its intersection with the **critical line**, defined for each $N\sigma$ as the point where the structured-coalescent prediction of $\pi/\pi_0$ reaches its maximal reduction (close to where Muller's ratchet starts to click frequently);
3. evaluate the structured coalescent (the site frequency spectrum, hence $\pi/\pi_0$, Tajima's $D$ and other statistics) at that corresponding point.

Populations above or to the left of the critical line are treated by steps 1–3; the others already lie in the background selection regime.

**Recombining genomes (linkage blocks).** For a chromosome with total map length $R$, treat the genome as independent, freely recombining blocks, each a fraction $\ell$ of the genome that evolves asexually with effective selected mutation rate $\ell U$. The block size is fixed self-consistently by requiring few recombination events inside a block during one pairwise coalescence time of that block, $\ell R\, T_2(\ell) \lesssim 1$, where $T_2(\ell)$ is computed from the asexual coarse-grained prediction at mutation rate $\ell U$. Effects of unlinked blocks on the effective population size are neglected.

## Depends on

- [Infinitesimal limit of linked selection](infinitesimal-limit-of-linked-selection.md)
- [Hill–Robertson interference](hill-robertson-interference.md)

## Expansion

The method is a patching argument between two asymptotic regimes, the background selection limit ($Ns \to \infty$, $U/s$ fixed) and the infinitesimal limit ($Ns \to 0$, $NU(Ns)^2$ fixed): along the critical line both approximations are roughly valid, so a few strongly selected mutations stand in for many weakly selected ones with the same fitness variance. The coarse-grained predictions recover the neutral limit as $N\sigma \to 0$ and the power-law decay of heterozygosity for large $N\sigma$, and they reproduce the excess of rare alleles and the U-shaped high-frequency spectrum seen in forward simulations, for example at parameters matching the Drosophila dot chromosome. Applied to recombining genomes, the block approximation predicts how diversity and minor allele frequency fall with local recombination rate far better than the recombining structured coalescent.

## Sources

- B. H. Good, A. M. Walczak, R. A. Neher and M. M. Desai, "Genetic diversity in the interference selection limit", PLoS Genetics (2014), e1004222, Results sections "Predicting genetic diversity by coarse-graining fitness" and "Emergence of linkage blocks in recombining genomes" (Eqs. (3), (6)–(8)), Methods "The boundary between the interference and background selection regimes", "Coarse-grained predictions" and "Determination of the effective linkage scale" (Eq. (9)), <https://doi.org/10.1371/journal.pgen.1004222>, PMCID PMC3967937.
