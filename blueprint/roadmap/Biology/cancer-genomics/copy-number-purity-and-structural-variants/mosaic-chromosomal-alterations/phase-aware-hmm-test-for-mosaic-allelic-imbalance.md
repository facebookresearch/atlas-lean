# Phase-aware hidden Markov model test for mosaic allelic imbalance

Let $j = 1, \dots, n$ index the heterozygous sites of one chromosome in one sample, ordered by position, with measured B-allele frequency $\mathrm{BAF}_j$ and computationally inferred haplotype phase $s_j \in \{+1, -1\}$. Define the phased deviation $y_j = s_j\,(\mathrm{BAF}_j - \tfrac12)$.

**Model.** A three-state hidden Markov model with states $\{+\Theta, -\Theta, 0\}$ describes $y_1, \dots, y_n$:

- outside a mosaic alteration the expected phased deviation is $0$;
- inside an alteration it is $+\Theta$ or $-\Theta$, where $\Theta > 0$ is the expected absolute BAF deviation $\mathbb E\,|\Delta\mathrm{BAF}|$ induced by the event;
- transitions between $+\Theta$ and $-\Theta$ represent phase switch errors, and transitions between $\pm\Theta$ and $0$ represent alteration boundaries;
- the emission at site $j$ is a noisy BAF measurement centred at the state's mean.

**Test.** For each $\Theta$ the forward algorithm gives the likelihood $L(\Theta)$ of $y_{1:n}$, integrating over switch-error and boundary positions. The test statistic is

$$\Lambda = \frac{\max_{\Theta} L(\Theta)}{L(0)},$$

where $L(0)$ is the likelihood with no alteration. Because transition parameters are only approximately known, $\Lambda$ is calibrated empirically rather than against an asymptotic law: its null distribution is computed on the same data with randomized phase, and this empirical null controls the false discovery rate. For chromosomes passing the threshold, alteration boundaries are obtained by sampling state paths from the model at $\hat\Theta$.

## Depends on

- [Allelic imbalance as a function of clonal cell fraction](allelic-imbalance-as-a-function-of-clonal-cell-fraction.md)

## Expansion

At a single site an imbalance of $\Theta$ is buried in measurement noise of standard deviation $\sigma \gg \Theta$, and unphased absolute deviations carry no consistent sign. With correct phase, all $m$ sites within an alteration deviate in the same direction, so their sum has mean $m\Theta$ against noise of order $\sigma\sqrt m$, and an event becomes detectable once $\Theta \gtrsim \sigma/\sqrt m$. This is how alterations at cell fractions near 1% become detectable when long, accurate phase is available. Switch errors flip the sign partway through an event; the $\pm\Theta$ state pair absorbs these flips instead of breaking the run. Randomizing phase keeps each site's unphased BAF distribution but destroys the sign coherence that the alternative exploits, which makes it a natural null.

## Sources

- P.-R. Loh, G. Genovese, R. E. Handsaker, et al., "Insights into clonal haematopoiesis from 8,342 mosaic chromosomal alterations", Nature 559 (2018), Methods ("Detection of mCAs using long-range haplotype phase") and Extended Data Fig. 1, <https://doi.org/10.1038/s41586-018-0321-x> (PMC6054542).
