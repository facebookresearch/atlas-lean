# Copula mixture model and the irreproducible discovery rate

**Data.** Two replicate experiments each assign a significance score to the same $n$ candidate findings (peaks, binding sites, chromatin interactions), giving pairs $(x_{i,1}, x_{i,2})$, $i = 1,\dots,n$, in which larger scores mean stronger evidence. Only the ranks of the scores within each replicate are used.

**Model.** Each finding is *reproducible* with probability $\pi_1$ or *irreproducible* with probability $\pi_0 = 1 - \pi_1$, with latent label $K_i \in \{0,1\}$. Given the label, a latent pair $(z_{i,1}, z_{i,2})$ is drawn from

$$K_i = 1: \; \mathcal{N}\!\left(\begin{pmatrix}\mu\\ \mu\end{pmatrix}, \begin{pmatrix}\sigma^2 & \rho\sigma^2\\ \rho\sigma^2 & \sigma^2\end{pmatrix}\right), \qquad K_i = 0: \; \mathcal{N}\!\left(\begin{pmatrix}0\\ 0\end{pmatrix}, I_2\right),$$

with $\mu > 0$ and $0 < \rho \le 1$, so reproducible findings have high and correlated latent scores and irreproducible ones have low, independent scores. The observed scores are monotone transforms of the latent ones, $x_{i,r} = F_r^{-1}\bigl(G(z_{i,r})\bigr)$, where $G(z) = \pi_0\Phi(z) + \pi_1\Phi\bigl((z-\mu)/\sigma\bigr)$ is the latent marginal distribution and $F_r$ the unknown marginal distribution of replicate $r$. The dependence between replicates is thus a mixture of a Gaussian copula and the independence copula, and the parameters $(\pi_1, \mu, \sigma, \rho)$ are estimated from the ranks by an expectation–maximization pseudo-likelihood.

**Definitions.** Writing $h_1$, $h_0$ for the two component densities of the latent pair, the *local irreproducible discovery rate* of finding $i$ is the posterior probability that it is irreproducible,

$$\mathrm{idr}_i = \frac{\pi_0\, h_0(z_{i,1}, z_{i,2})}{\pi_0\, h_0(z_{i,1}, z_{i,2}) + \pi_1\, h_1(z_{i,1}, z_{i,2})}.$$

For a selected set $S$ of findings the *irreproducible discovery rate* is the average

$$\mathrm{IDR}(S) = \frac{1}{|S|}\sum_{i \in S}\mathrm{idr}_i ,$$

and selecting the findings with smallest $\mathrm{idr}_i$ until $\mathrm{IDR}(S) \le \alpha$ controls the expected fraction of irreproducible findings in the selected set at level $\alpha$, in the same way that the local false discovery rate controls the false discovery rate in a two-group model.

**Two-dimensional findings.** For interactions defined by two genomic anchors, a finding of replicate $1$ corresponds to the findings of replicate $2$ whose two anchors both overlap its anchors (or lie within a maximal gap). When several findings of replicate $2$ correspond to $x_{i,1}$, one is chosen by minimizing an ambiguity-resolution value: the distance between anchor midpoints, minus the relative anchor overlap, or the sum of the ranks. The paired scores of the resulting one-to-one correspondence enter the same copula mixture model.

## Remarks

Because the model is specified through ranks and a copula, it is invariant to any monotone rescaling of the scores in each replicate, so replicates scored on different scales can be compared. The mixture formalizes the empirical pattern that the top findings of two replicates are consistent while the bulk below some point are not: in the latent space the reproducible component is a correlated elongated cloud, the irreproducible one a round cloud near the origin. The local rate $\mathrm{idr}_i$ is Bayes' rule for the label, and the average over the selected set is the expected proportion of irreproducible findings in it, by linearity of expectation.

## Sources

- K. Krismer, Y. Guo and D. K. Gifford, "IDR2D identifies reproducible genomic interactions", Nucleic Acids Research (2020), introduction (IDR as a copula mixture with one reproducible and one irreproducible component; a finding's IDR as the probability of belonging to the irreproducible component), Figure 1C–D and Eq. (1) (two-dimensional correspondence and ambiguity resolution), <https://doi.org/10.1093/nar/gkaa030>, PMCID PMC7102997.
- Q. Li, J. B. Brown, H. Huang and P. J. Bickel, "Measuring reproducibility of high-throughput experiments", Annals of Applied Statistics 5 (2011), 1752–1779, <https://doi.org/10.1214/11-AOAS466> (the copula mixture model, local idr and IDR).
