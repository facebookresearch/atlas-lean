# PhyloCSF's score threshold test is most powerful for unnormalized weights

Let the leaf set be finite, and suppose every column has positive [site likelihood](site-lik.md) under both models. Let $c$ be real and $\phi$ any map from alignments of $m$ columns to $[0, 1]$ such that

$$\sum_{A} \phi(A)\, \mathcal{L}_N(A) \le \sum_{A} \phi_c(A)\, \mathcal{L}_N(A).$$

Then

$$\sum_{A} \phi(A)\, \mathcal{L}_C(A) \le \sum_{A} \phi_c(A)\, \mathcal{L}_C(A),$$

where the sums run over all alignments, $\mathcal{L}_C, \mathcal{L}_N$ are the [alignment likelihoods](align-lik.md) and $\phi_c$ the [threshold test](score-test.md). The weights need not sum to one; size and power in the probabilistic sense need $\sum_A \mathcal{L}(A) = 1$ for each model.
