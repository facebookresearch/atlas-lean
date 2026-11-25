# The score is the log-likelihood ratio of the alignment

If every column $A_k$ of an alignment has positive [site likelihood](site-lik.md) under both models, then the [PhyloCSF score](score.md) is

$$\mathrm{sc}(A) = \log \frac{\mathcal{L}_C(A)}{\mathcal{L}_N(A)},$$

where $\mathcal{L}_C$ and $\mathcal{L}_N$ are the [alignment likelihoods](align-lik.md) under the coding and non-coding models.
