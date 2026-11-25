# Matrix concentration inequalities

Tail and expectation bounds for the extreme eigenvalues of random Hermitian matrices, following J. A. Tropp, *An Introduction to Matrix Concentration Inequalities* (Found. Trends Mach. Learn. 8, 2015, [arXiv:1501.01571](https://arxiv.org/abs/1501.01571)). The matrix Laplace transform method bounds $\mathbb{P}\{\lambda_{\max}(Y) \ge t\}$ and $\mathbb{E}\, \lambda_{\max}(Y)$ by the trace moment generating function $\mathbb{E} \operatorname{tr} e^{\theta Y}$. For a sum of independent random matrices, Lieb's concavity theorem makes matrix cumulant generating functions subadditive, and per-summand cgf bounds then give the matrix Chernoff and Bernstein inequalities.

- [Trace moment generating function](trace-mgf.md)
- [Matrix Laplace transform method, upper tail](measure-real-le-lambda-max-le.md)
- [Matrix Laplace transform method, lower tail](measure-real-lambda-min-le-le.md)
- [Matrix Laplace transform method, expectation bound](integral-lambda-max-le.md)
- [Expectation of a random matrix](expect.md)
- [Subadditivity of matrix cumulant generating functions](integral-trace-exp-sum-le.md)
- [Matrix Gaussian series](gaussian-series.md)
- [Matrix Gaussian series, Hermitian case](matrix-gaussian-series.md)
- [Matrix Chernoff inequality](matrix-chernoff.md)
- [Matrix Bernstein inequality, Hermitian case](matrix-bernstein.md)
- [Matrix Hoeffding inequality](matrix-hoeffding.md)

## Related topics

- [Lieb's concavity theorem](../../../LinearAlgebra/positive-definite-matrices/lieb-s-concavity-theorem/README.md)
- [Eigenvalues and spectral norm of Hermitian matrices](../../../LinearAlgebra/eigenvalues-and-canonical-forms/eigenvalues-and-spectral-norm-of-hermitian-matri/README.md)
- [Hoeffding's inequality](../hoeffding-s-inequality/README.md)
- [Cramér's theorem](../../large-deviations/cram-r-s-theorem/README.md)
- [Peierls and Klein inequalities](../../../Analysis/operator-theory/eigenvalue-inequalities/peierls-and-klein-inequalities/README.md)
- [Randomized range finder](../../../LinearAlgebra/matrix-decompositions/randomized-range-finder/README.md)
- [Kadison–Singer problem](../../../Analysis/operator-algebras/kadison-singer-problem/README.md)
- [Wigner's semicircle law](../../high-dimensional-probability/wigner-s-semicircle-law/README.md)
- [Generalization bounds and concentration](../../../ComputerScience/machine-learning/generalization-bounds-and-concentration/README.md)
