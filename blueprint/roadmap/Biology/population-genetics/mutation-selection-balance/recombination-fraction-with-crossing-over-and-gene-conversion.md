# Recombination fraction with crossing over and gene conversion

**Setting.** Let a focal neutral site and a selected site lie $d$ base pairs apart on the same chromosome. Crossovers occur at rate $r_{\mathrm{CO}}$ per base pair per meiosis, and gene-conversion tracts are initiated at rate $\gamma$ per base pair per meiosis with mean tract length $L_{\mathrm{GC}}$ (geometrically distributed). The probability that a meiosis separates the two sites is

$$r(d) = d\, r_{\mathrm{CO}} + 2 \gamma L_{\mathrm{GC}} \bigl(1 - e^{-d / L_{\mathrm{GC}}}\bigr),$$

valid while $d\, r_{\mathrm{CO}}$ is small. The gene-conversion term grows linearly, like $2\gamma d$, for $d \ll L_{\mathrm{GC}}$ and saturates at $2 \gamma L_{\mathrm{GC}}$ for $d \gg L_{\mathrm{GC}}$.

**Use in background selection.** In the standard background-selection prediction, the expected neutral diversity at a focal site relative to its value without linked selection is

$$B = \frac{\pi}{\pi_0} = \exp\Bigl(-\sum_i \frac{u_i\, t_i}{\bigl(t_i + r_i (1 - t_i)\bigr)^2}\Bigr),$$

summed over selected sites $i$ with deleterious mutation rate $u_i$, heterozygous fitness reduction $t_i = s_i h_i$, and recombination fraction $r_i = r(d_i)$ to the focal site; in practice the sum is also integrated over a distribution of $t$. Using the crossover-only fraction $d\, r_{\mathrm{CO}}$ in place of $r(d)$ underestimates recombination between nearby sites and overstates background selection.

## Proof sketch

Two sites are separated by gene conversion when a tract covers exactly one of them. Orient tracts in the direction they extend, with length exceeding $x$ with probability $e^{-x/L_{\mathrm{GC}}}$. A tract starting between the sites at distance $x$ from the far site covers only the far site when its length exceeds $x$, contributing $\gamma\int_0^d e^{-x/L_{\mathrm{GC}}}dx$; a tract starting outside at distance $y$ from the near site covers only the near site when its length lies in $(y, y + d)$, contributing $\gamma\int_0^\infty (e^{-y/L_{\mathrm{GC}}} - e^{-(y+d)/L_{\mathrm{GC}}})dy$. Each term equals $\gamma L_{\mathrm{GC}}(1 - e^{-d/L_{\mathrm{GC}}})$, giving the factor $2$. Crossovers and conversions are rare per meiosis, so their probabilities add. At $r_i = 0$ the background-selection exponent reduces to $\sum_i u_i / t_i$, recovering the non-recombining reduction to the mutation-free class. Applied to *Drosophila melanogaster* with experimentally estimated crossover maps, $\gamma = 1.25 \times 10^{-7}$ per base pair per female meiosis and $L_{\mathrm{GC}} = 518$ bp, the predicted $B$ has genome-wide median about $0.59$ and explains roughly 58% of the variance in silent diversity across 100 kb windows, providing a null baseline for detecting sweeps and balancing selection.

## Depends on

- [Background selection on a uniformly recombining chromosome](background-selection-on-a-uniformly-recombining-chromosome.md)

## Proof depends on

- [Background selection reduces the effective size to the mutation-free class](background-selection-deterministic-reduction-fac.md)

## Sources

- J. M. Comeron, "Background selection as baseline for nucleotide variation across the Drosophila genome", PLoS Genetics 10 (2014), e1004434, <https://doi.org/10.1371/journal.pgen.1004434>, PMCID PMC4072542. Materials and Methods, "BGS with crossover and gene conversion along D. melanogaster chromosomes"; Results on genome-wide $B$ and its correlation with diversity.
