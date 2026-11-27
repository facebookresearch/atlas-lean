# Maximum-diversity soft clustering

**Setting.** Cells $i = 1,\dots,N$ have unit-norm embeddings $Z_i \in \mathbb R^d$ (for example, normalized principal components) and one-hot batch indicators $\phi_i \in \{0,1\}^B$; batch $b$ has $N_b$ cells. Clusters $k = 1,\dots,K$ have unit-norm centroids $Y_k$, and $R_{ki} > 0$ with $\sum_k R_{ki} = 1$ is the soft assignment of cell $i$.

**Batch–cluster dependence.** The observed and independence-expected soft counts of batch $b$ in cluster $k$ are

$$O_{bk} = \sum_i \mathbf 1[i \in b]\,R_{ki}, \qquad E_{bk} = \frac{N_b}{N}\sum_i R_{ki},$$

and $\sum_{b,k} O_{bk}\log(O_{bk}/E_{bk}) = \sum_{i,k} R_{ki}\,\phi_i^\top\log(O_{\cdot k}/E_{\cdot k})$ is a Kullback–Leibler measure of dependence between batch and cluster.

**Objective.** With entropy weight $\sigma > 0$ and diversity weight $\theta \ge 0$,

$$\min_{R,\,Y}\ \sum_{i,k} R_{ki}\,2\bigl(1 - Y_k^\top Z_i\bigr) + \sigma R_{ki}\log R_{ki} + \sigma\theta\,R_{ki}\,\phi_i^\top\log\frac{O_{\cdot k}}{E_{\cdot k}},$$

where $2(1 - Y_k^\top Z_i) = \|Z_i - Y_k\|^2$ for unit vectors. For $\theta = 0$ this is entropy-regularized soft $k$-means, which tends to hard $k$-means as $\sigma \to 0$ and to uniform assignment as $\sigma \to \infty$.

**Assignment update.** With $O$ and $E$ held fixed (computed from the other cells), the minimizer over $R_{\cdot i}$ on the probability simplex is

$$R_{ki} = \frac{\exp\bigl(-2(1-Y_k^\top Z_i)/\sigma\bigr)\prod_b (E_{bk}/O_{bk})^{\theta\phi_{bi}}}{\sum_{\hat k}\exp\bigl(-2(1-Y_{\hat k}^\top Z_i)/\sigma\bigr)\prod_b (E_{b\hat k}/O_{b\hat k})^{\theta\phi_{bi}}},$$

so clusters already over-represented in cell $i$'s batch ($O > E$) are down-weighted. The centroid update is the spherical $k$-means step $Y_k \propto \sum_i R_{ki} Z_i$, renormalized to unit length.

## Expansion

The Lagrangian $\sum_k [2R_{ki}(1-Y_k^\top Z_i) + \sigma R_{ki}\log R_{ki} + \sigma\theta R_{ki}\phi_i^\top\log(O_{\cdot k}/E_{\cdot k})] + \lambda(\sum_k R_{ki} - 1)$ has stationarity condition $\log R_{ki} = -2(1-Y_k^\top Z_i)/\sigma - \theta\,\phi_i^\top\log(O_{\cdot k}/E_{\cdot k}) - 1 - \lambda/\sigma$, and normalization eliminates $\lambda$. Because $O$ and $E$ depend on $R$, assignments are updated in small blocks with $O$ and $E$ recomputed on the held-out cells. In practice $1$ is added to $O$ and $E$ to avoid infinite penalties, and $\theta$ is discounted for small batches as $\theta_b = \theta_{\max}\bigl[1 - e^{-(N_b/(K\tau))^2}\bigr]$.

## Sources

- I. Korsunsky, N. Millard, J. Fan et al., "Fast, sensitive and accurate integration of single-cell data with Harmony", Nature Methods 16 (2019) 1289–1296, Supplementary Note 1, Section 2 ("Maximum Diversity Clustering", Eqs (1)–(8), Algorithm 2), <https://doi.org/10.1038/s41592-019-0619-0> (PMC6884693).
