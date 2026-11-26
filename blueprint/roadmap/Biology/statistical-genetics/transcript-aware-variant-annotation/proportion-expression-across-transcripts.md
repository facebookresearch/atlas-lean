# Proportion expression across transcripts

Let a gene have transcripts $t = 1, \dots, T$ with expression levels $e_1, \dots, e_T \ge 0$ in a given tissue, and let a variant $v$ fall inside the gene. Annotation assigns $v$ a consequence on each transcript; let $S_v \subseteq \{1, \dots, T\}$ be the set of transcripts on which $v$ has the consequence of interest (for instance predicted loss of function). The **expression of the annotation** is

$$E_v = \sum_{t \in S_v} e_t,$$

and the **proportion expression across transcripts** is the normalized quantity

$$\mathrm{pext}(v) = \frac{E_v}{\sum_{t=1}^{T} e_t} \in [0, 1],$$

defined when the gene is expressed. It is the share of the gene's transcriptional output in that tissue that carries the annotated consequence: $\mathrm{pext}(v) = 1$ when every expressed transcript is affected, and $\mathrm{pext}(v) \approx 0$ when the annotation rests on transcripts that are not expressed there. Averaging over tissues gives a single score per variant, and values below $0.1$, between, and above $0.9$ separate unexpressed, intermediate, and near-constitutive regions.

Two properties make it a useful filter on variant annotations. It is invariant under rescaling all transcript expression in a tissue, so tissues of different sequencing depth are comparable. And it is a weighted indicator: $\mathrm{pext}(v) = \sum_t w_t \mathbb{1}\{t \in S_v\}$ with weights $w_t = e_t/\sum_s e_s$ summing to one, so it interpolates between the binary annotation on a canonical transcript ($w$ a point mass) and the fraction of transcripts affected ($w$ uniform).

## Expansion

The quantity exists because consequence annotation is transcript-specific while variant interpretation is gene-specific: a variant truncating a minor isoform and a variant truncating every isoform receive the same label from the usual pipelines, yet only the second removes the gene's function. Weighting by expression rather than counting transcripts is what makes the metric track function, since annotation databases contain many transcripts with negligible expression. Empirically, variants in haploinsufficient and constrained gene sets have higher scores than those in gene sets tolerant of loss of function; predicted loss-of-function variants flagged as dubious by a transcript-aware filter have systematically lower scores than unflagged ones; and non-synonymous variants on near-constitutively expressed regions show stronger signs of selective constraint than those on low-expression regions. The score is a continuous summary of the isoform landscape, not a classifier: high-confidence variants may still have low scores, and the thresholds above are conventions for bucketing rather than decision rules.

## Sources

- B. B. Cummings, K. J. Karczewski, J. A. Kosmicki et al., "Transcript expression-aware annotation improves rare variant interpretation", Nature 581 (2020), 452–458, Results ("pext score summarizes isoform expression", Figs. 2–3) and Methods, <https://doi.org/10.1038/s41586-020-2329-2>, PMCID PMC7334198.
