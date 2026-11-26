# Motif-context enrichment of mutations and the minimal attributable count

Fix one tumour sample and a mutational motif, for example the APOBEC target $\mathrm{T\underline{C}A}$ (mutated base underlined; the reverse complement $\mathrm{T\underline{G}A}$ is counted together with it). Let

- $\mathrm{Mut}_{TCA}$ be the number of $\mathrm{C}\to\mathrm{T}$ or $\mathrm{C}\to\mathrm{G}$ mutations at $\mathrm{T\underline{C}A}$ sites,
- $\mathrm{Mut}_{C}$ the number of all $\mathrm{C}\to\mathrm{T}$ or $\mathrm{C}\to\mathrm{G}$ mutations,
- $\mathrm{Con}_{TCA}$ and $\mathrm{Con}_{C}$ the numbers of $\mathrm{TCA}$ motifs and of cytosines (both strands) in the 41-mers centred on the mutations of the sample,

with $\mathrm{Mut}_{TCA} > 0$ and $\mathrm{Con}_{TCA}, \mathrm{Mut}_C > 0$. The **enrichment** of mutations at the motif is

$$E_{TCA} = \frac{\mathrm{Mut}_{TCA}/\mathrm{Con}_{TCA}}{\mathrm{Mut}_{C}/\mathrm{Con}_{C}} = \frac{\mathrm{Mut}_{TCA}\, \mathrm{Con}_{C}}{\mathrm{Mut}_{C}\, \mathrm{Con}_{TCA}},$$

and the **minimal number of motif mutations attributable to the motif-specific process** is

$$\mathrm{Min}_{TCA} = \mathrm{Mut}_{TCA} \cdot \frac{E_{TCA} - 1}{E_{TCA}}.$$

**Proposition.** $\mathrm{Min}_{TCA} = \mathrm{Mut}_{TCA} - \mathrm{Mut}_C \,\dfrac{\mathrm{Con}_{TCA}}{\mathrm{Con}_C}$, the excess of observed motif mutations over the count expected if cytosine mutations fell on motifs in proportion to motif abundance. Hence $\mathrm{Min}_{TCA} > 0$ iff $E_{TCA} > 1$, and $\mathrm{Min}_{TCA} \le \mathrm{Mut}_{TCA}$.

Sub-motifs are compared in the same way: under the null of motif-proportional mutation, the expected number of mutations at $\mathrm{Y\underline{T}CA}$ (pyrimidine 5′) is $\mathrm{Exp}_{YTCA} = \mathrm{Mut}_{TCA}\,\mathrm{Con}_{YTCA}/\mathrm{Con}_{TCA}$, and analogously for $\mathrm{RTCA}$ (purine 5′) and each $\mathrm{NTCA}$; a $\chi^2$ goodness-of-fit test of observed against expected counts classifies samples as A3A-like ($\mathrm{YTCA}$ excess) or A3B-like ($\mathrm{RTCA}$ excess).

## Expansion

Since $1/E_{TCA} = \mathrm{Mut}_C\,\mathrm{Con}_{TCA}/(\mathrm{Mut}_{TCA}\,\mathrm{Con}_C)$, we get $\mathrm{Mut}_{TCA}(1 - 1/E_{TCA}) = \mathrm{Mut}_{TCA} - \mathrm{Mut}_C\,\mathrm{Con}_{TCA}/\mathrm{Con}_C$. Enrichment $1$ means motif mutations are as frequent as cytosine mutations in general once corrected for motif abundance, so only the excess above that baseline can be attributed to a motif-specific mutator; this makes the estimate a lower bound. Significance of enrichment per sample is assessed by a one-sided Fisher exact test comparing $\mathrm{Mut}_{TCA}/(\mathrm{Mut}_C - \mathrm{Mut}_{TCA})$ with $\mathrm{Con}_{TCA}/(\mathrm{Con}_C - \mathrm{Con}_{TCA})$, with Benjamini–Hochberg correction across samples; samples that are not significant are assigned $\mathrm{Min}_{TCA} = 0$. Applied to cancer genomes, the A3A-like median attributable count (1,480) exceeded the A3B-like median (133) more than elevenfold.

## Sources

- K. Chan, S. A. Roberts, L. J. Klimczak et al., "An APOBEC3A hypermutation signature is distinguishable from the signature of background mutagenesis by APOBEC3B in human cancers", Nature Genetics 47 (2015), 1067–1072, Online Methods (enrichment, minimal estimate, Y/RTCA and NTCA analyses), <https://doi.org/10.1038/ng.3378>, PMCID: PMC4594173.
