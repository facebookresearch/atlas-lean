# Wigner's semicircle law

For a Wigner matrix $W_n$ (real symmetric, with independent, identically distributed
upper-triangular entries of mean $0$ and variance $1$; Tao's Theorem 2.4.2 allows the diagonal a
different law), the empirical spectral distribution of $W_n / \sqrt{n}$ converges almost surely
to the semicircle distribution $\sigma$, with density $\frac{1}{2\pi}\sqrt{4 - x^2}$ on $[-2, 2]$.
The moment method proves it by showing that
$\frac{1}{n}\mathbb{E}\operatorname{tr}(W_n/\sqrt{n})^{2k}$ tends to the Catalan number $C_k$,
which counts non-crossing pair partitions (equivalently Dyck words), and that $C_k$ is the $2k$-th
moment of $\sigma$;
concentration then upgrades convergence in expectation to almost sure convergence.

- [Wigner matrix](wigner-matrix.md)
- [Wigner matrices are Hermitian](wigner-matrix-is-hermitian.md)
- [Empirical spectral measure of a Hermitian matrix](empirical-spectral-measure-herm.md)
- [Semicircle distribution](semicircle-law.md)
- [Wigner's semicircle law](wigner-semicircle.md)
- [Semicircle density](semicircle-pdfreal.md)
- [The semicircle density is nonnegative](semicircle-pdfreal-nonneg.md)
- [The semicircle density is continuous](continuous-semicircle-pdfreal.md)
- [Semicircle distribution defined by its density](semicircle-real.md)
- [The two semicircle distributions agree](semicircle-law-eq-semicircle-real.md)
- [Integrals against the semicircle distribution](integral-semicircle-real.md)
- [The even moments of the semicircle distribution are the Catalan numbers](integral-pow-two-mul-semicircle-real.md)
- [The odd moments of the semicircle distribution vanish](integral-pow-two-mul-add-one-semicircle.md)
- [Semicircle moments count Dyck words](integral-pow-two-mul-semicircle-real-eq.md)
- [The semicircle distribution is supported in [-2, 2]](semicircle-real-compl-icc.md)
- [Powers are integrable against the semicircle distribution](integrable-pow-semicircle-real.md)
- [The semicircle distribution is determined by its moments](eq-semicircle-real-of-integral-pow-eq.md)
- [The moments of the semicircle law count noncrossing pair partitions](integral-pow-semicircle-real-eq-card-non.md)
- [Normalised real Wigner matrix](wigner-matrix-real.md)
- [Expected moments of a Wigner matrix converge to the semicircle moments](tendsto-expected-moment-wigner-matrix-re.md)
- [Symmetric matrix of an upper-triangular array](symmetric-matrix.md)
- [The symmetric matrix of an array is Hermitian](symmetric-matrix-is-hermitian.md)
- [Concentration of linear spectral statistics](concentration-trace-lipschitz.md)

## Related topics

- [Operator norm of random matrices](../operator-norm-of-random-matrices/README.md)
- [Catalan numbers](../../../Combinatorics/catalan-numbers-lattice-paths/catalan-numbers/catalan-numbers/README.md)
- [Noncrossing pair partitions and the Catalan count](../../../Combinatorics/set-partitions/noncrossing-partitions/noncrossing-pair-partitions-and-the-catalan-count/README.md)
- [Weyl's eigenvalue inequalities](../../../Analysis/operator-theory/eigenvalue-inequalities/weyl-s-eigenvalue-inequalities/README.md)
- [Talagrand's concentration inequality](../../concentration-inequalities/talagrand-s-concentration-inequality/README.md)
- [Moment problem for compactly supported measures](../../../Analysis/harmonic-analysis/integral-transforms/moment-problem-for-compactly-supported-measures/README.md)
- [Matrix concentration inequalities](../../concentration-inequalities/matrix-concentration-inequalities/README.md)
- [Free probability](../free-probability/README.md)
- [Ben Arous–Guionnet large deviations](../../large-deviations/ben-arous-guionnet-large-deviations/README.md)
