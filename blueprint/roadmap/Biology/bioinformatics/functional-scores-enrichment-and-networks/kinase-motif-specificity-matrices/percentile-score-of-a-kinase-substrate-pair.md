# Percentile score of a kinase-substrate pair

Fix a kinase with specificity matrix $M$ and a reference set $\mathcal{S}$ of experimentally identified phosphorylation sites. Let $F_M$ be the empirical distribution function of the scores of the reference set,

$$F_M(t) = \frac{1}{|\mathcal{S}|} \sum_{s \in \mathcal{S}} \mathbf{1}\{S_M(s) \le t\} .$$

The percentile score of a candidate substrate $s^\star$ for this kinase is $100 \cdot F_M\big(S_M(s^\star)\big) \in [0,100]$: the rank of $s^\star$ within the kinase's own score distribution over the reference phosphoproteome. Scoring one site against a panel of kinases $M_1,\dots,M_K$ and ranking the resulting percentile scores gives, for each site, an ordering of kinases that is invariant to any strictly increasing reparametrization of an individual kinase's raw scores.

## Depends on

- [Normalized specificity matrix and multiplicative substrate score](normalized-specificity-matrix-and-multiplicative-substrate-score.md)

## Remarks

Raw motif scores are not comparable between kinases: a promiscuous kinase with a flat matrix produces scores on a different scale from a kinase with a sharply defined motif, so the largest raw score across a panel would be dominated by scale rather than by specificity. Applying each kinase's own empirical distribution function is the probability-integral transform restricted to the reference set, which maps every kinase to a common uniform-like scale and makes "top $k$ kinases for this site" meaningful. The choice of reference set matters: it defines the null against which favourability is judged, so a reference restricted to one tissue or one enrichment protocol shifts all percentiles together.

## Sources

- Johnson JL, Yaron TM, Huntsman EM, et al. An atlas of substrate specificities for the human serine/threonine kinome. *Nature* 613:759-766 (2023), Methods, "Substrate scoring" and "Kinase enrichment analysis". DOI <https://doi.org/10.1038/s41586-022-05575-3>. PMCID PMC9876800.
