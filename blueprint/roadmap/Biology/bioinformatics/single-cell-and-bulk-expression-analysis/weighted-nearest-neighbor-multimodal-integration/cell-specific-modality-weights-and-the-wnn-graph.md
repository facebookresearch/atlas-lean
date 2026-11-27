# Cell-specific modality weights and the weighted nearest neighbor graph

Let $N$ cells be measured in $M \ge 2$ modalities, cell $i$ having a low-dimensional profile $X_i^m \in \mathbb{R}^{d_m}$ in modality $m$, and let $d$ denote Euclidean distance. For each modality $m$ fix a $k$-nearest-neighbour graph, with $\mathrm{knn}_m(i) = \{\mathrm{knn}_{m,i,1}, \dots, \mathrm{knn}_{m,i,k}\}$ the neighbours of $i$ ordered by distance, and a cell-specific bandwidth $\sigma_{m,i} > d(X_i^m, X^m_{\mathrm{knn}_{m,i,1}})$.

**Predictions.** The prediction of $X_i^m$ from the neighbours of $i$ in modality $n$ (possibly $n = m$) is the neighbourhood average

$$\hat X^m_{i,n} = \frac{1}{k} \sum_{j=1}^{k} X^m_{\mathrm{knn}_{n,i,j}} .$$

**Affinities.** With $\rho_{m,i} = d(X_i^m, X^m_{\mathrm{knn}_{m,i,1}})$ (the distance to the first neighbour, "local connectivity"), the affinity between $X_i^m$ and a point $y \in \mathbb{R}^{d_m}$ is

$$\theta_m(X_i^m, y) = \exp\!\left(-\frac{\max\{d(X_i^m, y) - \rho_{m,i},\, 0\}}{\sigma_{m,i} - \rho_{m,i}}\right) \in (0, 1].$$

**Modality weights.** For $m \ne n$ the affinity ratio is

$$s_{m,n}(i) = \frac{\theta_m(X_i^m, \hat X^m_{i,m})}{\theta_m(X_i^m, \hat X^m_{i,n}) + \varepsilon}, \qquad \varepsilon > 0 \text{ small},$$

and the weights are

$$w_m(i) = \frac{\sum_{n \ne m} e^{s_{m,n}(i)}}{\sum_{m'} \sum_{n \ne m'} e^{s_{m',n}(i)}} .$$

Then $w_m(i) > 0$ and $\sum_m w_m(i) = 1$. For $M = 2$ (RNA $r$, protein $p$) this is the two-term softmax $w_r(i) = e^{s_r(i)} / (e^{s_r(i)} + e^{s_p(i)})$ with $s_r = s_{r,p}$, $s_p = s_{p,r}$.

**WNN graph.** The weighted similarity of cells $i$ and $j$ is

$$\theta_{\mathrm{w}}(i, j) = \sum_{m=1}^{M} w_m(i)\, \theta_m(X_i^m, X_j^m),$$

and the weighted nearest neighbours of $i$ are the $k$ cells with largest $\theta_{\mathrm{w}}(i, \cdot)$ within the candidate set $\bigcup_m \{\mathrm{knn}_{m,i,1}, \dots, \mathrm{knn}_{m,i,200}\}$. Because the weights belong to cell $i$, $\theta_{\mathrm{w}}$ and the resulting graph are in general not symmetric.

Properties:

- each affinity equals $1$ whenever $d(X_i^m, y) \le \rho_{m,i}$ and decays exponentially beyond the first-neighbour distance, so a sparsely sampled cell is not penalized for the gap to its first neighbour;
- $s_{m,n}(i)$ is large exactly when modality $m$'s own neighbours predict $X_i^m$ better than modality $n$'s neighbours do; a modality carrying no information about cell identity (for example pure noise) has $\theta_m(X_i^m, \hat X^m_{i,m}) \approx \theta_m(X_i^m, \hat X^m_{i,n})$, so $s_{m,n}(i) \approx 1$, and its weight is smaller than that of a modality whose ratios exceed $1$;
- if all weights of cell $i$ except $w_m(i)$ vanish, $\theta_{\mathrm{w}}(i, \cdot) = \theta_m(X_i^m, X^m_{\cdot})$ and the WNN neighbours reduce to modality-$m$ neighbours within the candidate set.

## Remarks

The affinity is the UMAP kernel with the local-connectivity offset subtracted from both numerator and denominator. The bandwidth $\sigma_{m,i}$ is chosen, in the spirit of large-margin nearest neighbours, as the mean distance from $i$ to the 20 cells with the smallest non-zero Jaccard (shared-neighbour) similarity to $i$: cells that are similar but probably in a different state. This makes the bandwidth adapt to rare states rather than being tied to a fixed neighbour rank. Positivity and normalization of the weights follow directly from the softmax form. Downstream, the WNN graph replaces a single-modality graph for UMAP, shared-nearest-neighbour clustering and trajectory inference.

## Sources

- Y. Hao, S. Hao, E. Andersen-Nissen, et al., "Integrated analysis of multimodal single-cell data", Cell 184 (2021) 3573–3587, STAR Methods sections "Performing within and cross-modality predictions", "Calculating cell-specific modality weights", "Calculating a WNN graph" and "Extending WNN to process more than two simultaneously measured modalities", <https://doi.org/10.1016/j.cell.2021.04.048> (PMC8238499).
