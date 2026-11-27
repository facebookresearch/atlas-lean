# Normalized specificity matrix and multiplicative substrate score

Let $P$ be a peptide-array densitometry matrix with rows indexed by candidate residues $a \in \mathcal{A}$ and columns by positions $j \in \mathcal{J}$ relative to the phospho-acceptor. Column-normalizing by the total signal of the randomized residues $\mathcal{R} \subseteq \mathcal{A}$ gives the specificity matrix

$$M_{a,j} = \frac{P_{a,j}}{\sum_{b \in \mathcal{R}} P_{b,j}}, \qquad \sum_{b \in \mathcal{R}} M_{b,j} = 1 .$$

For a substrate peptide $s = (s_j)_{j \in \mathcal{J}}$ with $s_j \in \mathcal{A}$, the score of $s$ under $M$ is the product of the corresponding entries, rescaled by the probability of the peptide under a random background $q$,

$$S(s) = \frac{\prod_{j \in \mathcal{J}} M_{s_j, j}}{\prod_{j \in \mathcal{J}} q_{s_j}} ,$$

so that $S(s) = 1$ for a peptide whose residues are exactly as frequent as background at every position, and $\log S(s) = \sum_{j} \log(M_{s_j,j}/q_{s_j})$ is additive across positions.

## Remarks

The product form encodes the modelling assumption that positions contribute independently to recognition, the same assumption that underlies a position weight matrix; taking logarithms turns it into a sum of per-position log-odds. Normalizing each column by the randomized residues makes entries comparable across positions despite unequal total signal, and excluding the phospho-acceptor residues from the normalization set avoids letting the fixed central residue dominate. Rows for residues that are absent by design (for example cysteine in a library that omits it) are set to a fixed value so that a peptide containing them is neither rewarded nor penalized.

## Sources

- Johnson JL, Yaron TM, Huntsman EM, et al. An atlas of substrate specificities for the human serine/threonine kinome. *Nature* 613:759-766 (2023), Methods, "Substrate scoring". DOI <https://doi.org/10.1038/s41586-022-05575-3>. PMCID PMC9876800.
