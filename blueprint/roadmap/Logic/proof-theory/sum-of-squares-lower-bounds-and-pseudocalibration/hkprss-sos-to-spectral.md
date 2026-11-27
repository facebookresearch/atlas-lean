# Hopkins et al.: SoS distinguishers for noise-robust problems yield spectral distinguishers

Let $(\mu, \nu)$ be a planted-versus-null hypothesis testing problem on $\{\pm 1\}^N$ that is noise-robust and invariant under a large permutation group. If degree-$d$ sum-of-squares distinguishes $\mu$ from $\nu$ (it certifies a bound violated by $\mu$ that holds for $\nu$ with high probability), then there is a spectral distinguisher: a matrix $Q(G)$ of dimension $N^{O(d)}$ whose entries are polynomials of degree $O(d)$ in the input, such that $\lambda_{\max}(Q(G))$ separates $\mu$ from $\nu$. In particular SoS lower bounds follow from low-degree polynomial lower bounds for such problems, and planted clique, sparse PCA and tensor PCA thresholds for SoS coincide with their low-degree thresholds.

## Proof sketch

Write the SoS certificate on the null distribution as a polynomial identity and use symmetry and noise-robustness to average it over the group and a noise operator. The averaged certificate's matrix of coefficients has low-degree polynomial entries, and its top eigenvalue under the planted distribution is large because the planted solution violates the certified inequality; this yields the spectral test.

## Depends on

- [The Lasserre / sum-of-squares hierarchy for Boolean polynomial optimization](lasserre-hierarchy.md)
- [Low-degree likelihood ratio and low-degree advantage](../../../Probability/high-dimensional-probability/low-degree-likelihood-ratio-method/low-degree-likelihood-ratio.md)

## Sources

- S. B. Hopkins, P. K. Kothari, A. Potechin, P. Raghavendra, T. Schramm, D. Steurer, "The power of sum-of-squares for detecting hidden structures", FOCS (2017), arXiv:1710.05017.
