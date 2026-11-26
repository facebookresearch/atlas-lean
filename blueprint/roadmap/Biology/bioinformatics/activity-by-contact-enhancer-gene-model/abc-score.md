# ABC score

Fix a cell type. For a candidate regulatory element $E$ let its **activity** be

$$A_E = \sqrt{\mathrm{DNase}_E \cdot \mathrm{H3K27ac}_E},$$

the geometric mean of the nonnegative (quantile-normalized) chromatin accessibility and H3K27ac signals over the element, the same for every gene. For an element $E$ and a gene $G$ let $C_{E,G}$ be the **contact** frequency between $E$ and the transcription start site of $G$, a finite positive number measured by Hi-C or approximated by a power law in genomic distance, $C_{E,G} \propto d(E, G)^{-1}$. This includes the self-contact $C_{P_G,G}$ of the promoter $P_G$ of $G$, where the distance is zero and the power law is undefined; it is set to a finite positive value (the source replaces each diagonal Hi-C entry by the maximum of its four neighboring entries).

The **ABC score** of the pair is

$$\mathrm{ABC}_{E,G} = \frac{A_E\, C_{E,G}}{\displaystyle\sum_{e \in \mathcal{E}(G)} A_e\, C_{e,G}},$$

where $\mathcal{E}(G)$ is the set of all candidate elements within 5 Mb of the promoter of $G$, including the promoter of $G$ itself. The score is defined only for genes whose denominator is positive, that is, some element of $\mathcal{E}(G)$ has positive activity; when every activity in $\mathcal{E}(G)$ vanishes the gene gets no score. An element is predicted to regulate $G$ when $\mathrm{ABC}_{E,G}$ exceeds a threshold. For fixed $G$ with positive denominator the scores are nonnegative and sum to $1$ over $\mathcal{E}(G)$.

## Expansion

The score encodes the assumption that each element contributes independently and additively to transcription, with a contribution proportional to how active it is times how often it touches the promoter; normalizing by the total over the neighborhood turns this into the fraction of the gene's regulatory input supplied by $E$, which is compared with the fractional expression change caused by perturbing $E$. The geometric mean demands both signals: accessibility alone also marks insulator-bound sites, and acetylation alone spreads over neighbors of strong enhancers. Including the gene's own promoter in the denominator lets it act as a competing input. Against CRISPR perturbation data in K562 cells, the score correlated with measured effects (Spearman $\rho = -0.63$ for regulatory pairs) and gave an area under the precision–recall curve of $0.65$, versus $0.39$ for genomic distance and $0.22$ and $0.29$ for activity or contact alone; replacing cell-type Hi-C by the distance power law changed this little.

## Sources

- C. P. Fulco, J. Nasser, T. R. Jones et al., "Activity-by-contact model of enhancer–promoter regulation from thousands of CRISPR perturbations", Nature Genetics 51 (2019), <https://doi.org/10.1038/s41588-019-0538-0>, PMCID PMC6886585. Results (ABC model and Figure 3) and Methods, "Calculating the contribution of one candidate element relative to others in the region".
