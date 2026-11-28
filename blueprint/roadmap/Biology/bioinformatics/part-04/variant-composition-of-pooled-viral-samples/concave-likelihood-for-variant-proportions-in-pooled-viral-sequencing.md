# Concave likelihood for variant proportions in pooled viral sequencing

**Model.** A pooled sample (for example wastewater) contains a mixture of $v$ viral variants with unknown proportions $w = (w_1, \dots, w_v)$ in the simplex

$$
\mathcal{S} = \Big\{w : 0 \le w_j \le 1,\ \sum_{j=1}^v w_j = 1\Big\}.
$$

At each of $s$ marker polymorphisms, the sequencing reads give $c_i^a$ reads with the alternate allele and $c_i^r$ with the reference allele; coverage $c_i^a + c_i^r$ may differ between sites. A **signature matrix** $P = (P_{ij})$ records the probability $P_{ij}$ that a read from variant $j$ carries the alternate allele at polymorphism $i$, estimated from curated genomes of each variant. Reads are drawn independently. A read at site $i$ comes from variant $j$ with probability $w_j$ and then carries the alternate allele with probability $P_{ij}$, so the alternate-allele probability at site $i$ is the mixture $\sum_j P_{ij} w_j$. The latent read-to-variant assignments $Z^a_{ij}, Z^r_{ij}$ satisfy $\sum_j Z^a_{ij} = c^a_i$ and $\sum_j Z^r_{ij} = c^r_i$.

**Lemma (likelihood).** For a sample with counts $(c_i^a, c_i^r)_{i \le s}$ and signature matrix $P$, the log-likelihood of the variant proportions is, up to an additive constant,

$$
\ell(w) = \sum_{i=1}^s c_i^a \log\Big(\sum_{j=1}^v P_{ij} w_j\Big) + \sum_{i=1}^s c_i^r \log\Big(1 - \sum_{j=1}^v P_{ij} w_j\Big).
$$

**Lemma (concavity).** $\ell : \mathcal{S} \to \mathbb{R}$ is concave. Hence every local maximizer on the simplex is a global maximizer, the maximum-likelihood composition $\hat w$ is the solution of a convex program, and it is unique whenever $\ell$ is strictly concave, for instance when $P$ has full column rank and the relevant counts are positive.

## Expansion

Conditionally on the coverage, the alternate count at site $i$ is binomial with success probability $p_i(w) = (Pw)_i$, and independence across sites gives $\ell$. Each term is a non-negative multiple of $\log$ or of $\log(1 - \cdot)$ composed with an affine function of $w$, and since $\log$ is concave and concavity is preserved under affine maps and non-negative sums, $\ell$ is concave. The constraint set is a polytope, so the maximization is a convex optimization problem that standard disciplined convex solvers handle reliably. Standard errors follow from bootstrap resampling of reads. In practice the estimates tracked the replacement of the wild type by the Alpha variant in longitudinal wastewater samples and recovered known dilution ratios. The identifiability of $w$ rests on the variant signatures being linearly independent across the marker sites.

## Sources

- Renan Valieris, Rodrigo Drummond, Alexandre Defelicibus, Emmanuel Dias-Neto et al., "A mixture model for determining SARS-Cov-2 variant composition in pooled samples", arXiv (2021), Section 2 (variant composition model, Lemma 1), Section 3 (likelihood maximization, Lemma 2), <https://doi.org/10.48550/arXiv.2110.01117>.
