# Reference taxa recover absolute fold changes from relative abundances

**Setting.** Let $A_j^{(g)} > 0$ be the absolute abundance of taxon $j \in \{1, \dots, P\}$ in condition $g \in \{1,2\}$, and $R_j^{(g)} = A_j^{(g)} / \sum_{j'} A_{j'}^{(g)}$ its relative abundance, the only quantity sequencing measures. Taxon $j$ is **differentially abundant (DA)** if $A_j^{(2)} \ne A_j^{(1)}$.

**Proposition (reference set).** If $T_0 \subseteq \{1, \dots, P\}$ is any nonempty set of non-DA taxa, then for every taxon $j$,

$$\frac{R_j^{(2)} \big/ \sum_{k \in T_0} R_k^{(2)}}{R_j^{(1)} \big/ \sum_{k \in T_0} R_k^{(1)}} = \frac{A_j^{(2)}}{A_j^{(1)}}.$$

**Proposition (null case).** If no taxon is DA then $R_j^{(2)} = R_j^{(1)}$ for all $j$; conversely, if all relative abundances are unchanged then all absolute fold changes $A_j^{(2)}/A_j^{(1)}$ are equal.

**Proposition (order preservation).** For any taxa $j, k$,

$$\frac{R_j^{(2)}}{R_j^{(1)}} \le \frac{R_k^{(2)}}{R_k^{(1)}} \iff \frac{A_j^{(2)}}{A_j^{(1)}} \le \frac{A_k^{(2)}}{A_k^{(1)}}.$$

**Proposition (median rule).** If fewer than half of the taxa are DA, then taxon $j$ is non-DA if and only if its relative fold change equals the median, $R_j^{(2)}/R_j^{(1)} = \mathrm{Median}_{j'}\{R_{j'}^{(2)}/R_{j'}^{(1)}\}$.

## Expansion

All four statements follow from $R_j^{(2)}/R_j^{(1)} = (A_j^{(2)}/A_j^{(1)}) \cdot (\sum_{j'} A_{j'}^{(1)} / \sum_{j'} A_{j'}^{(2)})$: compositional closure multiplies every absolute fold change by the same unknown factor, the ratio of total abundances. Dividing by the summed relative abundance of non-DA taxa cancels that factor, monotone rescaling preserves order, and when non-DA taxa (all with absolute fold change $1$) are a majority they occupy the middle of the ordered list. In practice these facts drive a differential-abundance procedure: zero counts are treated as left-censored at the detection limit and log relative abundances are fit by Tobit (censored normal) regression; a beta-uniform mixture test on the pooled $p$-values decides whether any DA taxa exist; taxa with fold-change estimates nearest the median form the reference set; and DA taxa are called by Tobit regression of log count ratios against the reference sum.

## Sources

- M. Wang, S. Fontaine, H. Jiang, G. Li, "ADAPT: Analysis of Microbiome Differential Abundance by Pooling Tobit Models", Bioinformatics (2024) btae661, Section 2.2 (Propositions 1–4) and Section 2.3 (Tobit likelihood, beta-uniform mixture test, reference selection), <https://doi.org/10.1093/bioinformatics/btae661>, PMCID PMC11959182.
