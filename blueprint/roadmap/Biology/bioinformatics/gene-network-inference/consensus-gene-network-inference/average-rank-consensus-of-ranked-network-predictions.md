# Average-rank consensus of ranked network predictions

Let $E$ be the set of candidate regulatory edges (transcription factor, target gene) and let methods $j = 1, \dots, M$ each submit a ranked list of edges. Write $P_{i,j} \in \{1, 2, \dots\}$ for the rank that method $j$ assigns to edge $i$; each method submits its top $100{,}000$ edges, and an edge absent from method $j$'s list receives the common rank $P_{i,j} = 100{,}001$ (one past the list length). The **community score** of edge $i$ is its average rank

$$\bar r_i = \frac{1}{M}\sum_{j=1}^{M} P_{i,j},$$

and the **community network** lists edges in increasing order of $\bar r_i$ (a Borda count). The rule uses only ranks, so it is invariant under any strictly increasing transformation of each method's internal confidence scores and needs no calibration across methods.

**Evaluation.** Against a gold standard of known interactions, each ranked list gives an area under the ROC curve (AUROC) and under the precision–recall curve (AUPR). Each area is converted to a p-value $p$ using a null distribution of areas from random edge lists (25,000 random networks, extrapolated in the tail by a fitted stretched exponential). Over the networks $i = 1, 2, 3$ with gold standards,

$$\mathrm{score}_{\mathrm{ROC}} = \frac13\sum_{i=1}^{3} -\log_{10} p_{\mathrm{ROC},i}, \qquad
\mathrm{score}_{\mathrm{PR}} = \frac13\sum_{i=1}^{3} -\log_{10} p_{\mathrm{PR},i}, \qquad
\mathrm{score} = \frac{\mathrm{score}_{\mathrm{ROC}} + \mathrm{score}_{\mathrm{PR}}}{2}.$$

**Observed behaviour.** In a blind benchmark of 35 methods on *E. coli*, *S. cerevisiae*, *S. aureus* and in silico expression data, the average-rank community network ranked first on the in silico network and third on *E. coli*, performed better than individual methods on average even when only five methods were combined, improved further as more methods were added, and was robust to including up to about 20% poorly performing methods.

## Expansion

Averaging ranks pools independent evidence: an edge that several unrelated methods place high obtains a low average rank, whereas a false positive specific to one method's bias is diluted by the other $M-1$ ranks. Methods of different families (regression, mutual information, correlation, Bayesian networks) err on different motifs, so their errors are only partly correlated and the averaged ranking is more stable than any single ranking. Poor methods add roughly uniform noise to every edge's average, which shifts all averages similarly and so changes the ordering little.

## Sources

- D. Marbach, J. C. Costello, R. Küffner, et al., "Wisdom of crowds for robust gene network inference", Nature Methods 9 (2012), Results ("Community networks outperform individual inference methods") and Methods ("Performance metrics"), <https://doi.org/10.1038/nmeth.2016> (PMC3512113).
