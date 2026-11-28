# Effective positive selection on neutral alleles near fixation under background selection

In the strong-load regime ($\lambda = U_d/s \gg 1$, $N s e^{-\lambda} \gg 1$) of the model of [lineage trajectories under linked deleterious mutations](lineage-trajectories-under-linked-deleterious-mutations.md), consider a neutral derived allele that has fixed among the most-fit individuals and is close to fixation in the whole population, so that the ancestral (wild-type) allele survives only at frequency $1 - f$ in less fit backgrounds. Let $k_c$ be the smallest number of deleterious mutations still carried by wild-type individuals; when $k_c \gg 1$,

$$k_c + 1 \approx \log_\lambda\!\left(\frac{1}{N s e^{-\lambda} (1-f)}\right).$$

**Result.** For $1 - f \ll 1/(N s e^{-\lambda})$, the wild type declines as if under selection $-s(k_c + 1)$, and the neutral derived allele behaves as if it had the frequency-dependent selection coefficient

$$s_{\mathrm{eff}}(f) = s \,\log_\lambda\!\left(\frac{1}{N s e^{-\lambda}(1-f)}\right) > 0,$$

which grows as $1 - f$ shrinks, because the fittest wild-type classes are successively lost (a ratchet) while the derived allele keeps the mutation-free class. This sweep-like behaviour of strictly neutral alleles creates the excess of high-frequency derived variants in the [site frequency spectrum under strong background selection](site-frequency-spectrum-under-strong-background-selection.md).

## Proof sketch

Once the derived allele has fixed in the mutation-free class, every surviving wild-type lineage descends from a background with at least $k_c$ mutations, and by the lineage dynamics such a lineage declines at rate about $s(k_c + 1)$ once it has passed its peak. Comparing the frequency $1 - f$ with the fluctuation scale $1/(N s e^{-\lambda})$ of the most-fit class, and using the peak sizes $\tilde g_k$ of lineages founded in class $k$, the paper obtains the logarithmic expression for $k_c$ above (its Equation 30, to leading order when $k_c \gg 1$). The wild type thus behaves as $f_{\mathrm{wt}}(t) \propto e^{-s_{\mathrm{eff}} t}$, and the derived allele gains the same coefficient with the opposite sign. At still higher frequencies ($1 - f \ll 1/(N\sigma)$) drift again dominates and the dynamics become neutral at census size $N$.

## Depends on

- [Lineage trajectories under mutation–selection balance at a non-recombining locus](lineage-trajectories-under-linked-deleterious-mutations.md)

## Sources

- I. Cvijović, B. H. Good and M. M. Desai, "The effect of strong purifying selection on genetic diversity", Genetics 209 (2018), 1235–1278, Equation 3 and the analysis of wild-type trajectories (Equations 30–35), <https://doi.org/10.1534/genetics.118.301058> (PMC6063222).
