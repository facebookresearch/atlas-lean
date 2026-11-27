# Allelic imbalance as a function of clonal cell fraction

Consider a heterozygous site with alleles $A$ and $B$ on the two homologues of a diploid genome, and a sample in which a fraction $c \in [0,1]$ of cells carries a chromosomal alteration of the homologue bearing $B$. Measure the B-allele frequency (BAF) as the share of allele copies that are $A$, and the deviation $\Delta\mathrm{BAF} = \mathrm{BAF} - \tfrac12$. Under an idealized linear-intensity model:

| Event in the altered cells | copies of $A$ | copies of $B$ | $\Delta\mathrm{BAF}$ | total copies |
|---|---|---|---|---|
| loss of the $B$ homologue | $1$ | $1-c$ | $\dfrac{c}{2(2-c)}$ | $2-c$ |
| copy-neutral LOH (B replaced by a copy of A) | $1+c$ | $1-c$ | $\dfrac{c}{2}$ | $2$ |
| gain of one extra copy of the $A$ homologue | $1+c$ | $1$ | $\dfrac{c}{2(2+c)}$ | $2+c$ |

Each $\Delta\mathrm{BAF}$ is increasing in $c$ and vanishes at $c = 0$. To first order in $c$, losses and gains give $\Delta\mathrm{BAF} \approx c/4$ with relative total intensity $\log_2(\text{total}/2) \approx \mp c/(2\ln 2)$, while copy-neutral LOH gives $\Delta\mathrm{BAF} \approx c/2$ with no intensity change. Hence detected events plotted by (total-intensity deviation, $|\Delta\mathrm{BAF}|$) fall on three lines through the origin, one per event type. The lines converge as $c \to 0$, so the copy-number state of low-cell-fraction events cannot be called confidently.

## Expansion

The table follows by counting allele copies in the mixture: normal cells contribute one $A$ and one $B$; altered cells contribute the post-event counts; weight these by $1-c$ and $c$. For example, under loss the $B$ count is $(1-c)\cdot 1 + c \cdot 0 = 1-c$, so $\mathrm{BAF} = 1/(2-c)$ and $\Delta\mathrm{BAF} = 1/(2-c) - 1/2 = c/(2(2-c))$. Inverting the appropriate row converts a measured imbalance into a clonal cell fraction once the event type is known; this is how cell fractions of detected alterations are estimated. Copy-neutral LOH is the most detectable event per unit cell fraction because it moves one allele's share by $c/2$ without diluting the total.

## Sources

- P.-R. Loh, G. Genovese, R. E. Handsaker, et al., "Insights into clonal haematopoiesis from 8,342 mosaic chromosomal alterations", Nature 559 (2018), Methods ("Detection of mCAs using long-range haplotype phase", copy-number calling and cell-fraction estimation) and Fig. 2a, <https://doi.org/10.1038/s41586-018-0321-x> (PMC6054542).
- K. B. Jacobs et al., "Detectable clonal mosaicism and its relationship to aging and cancer", *Nature Genetics* 44 (2012), 651–658, Supplementary Note, Table 1 (<https://doi.org/10.1038/ng.2270>).
