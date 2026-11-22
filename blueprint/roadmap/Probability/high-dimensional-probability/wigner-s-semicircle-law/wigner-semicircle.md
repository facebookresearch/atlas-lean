# Wigner's semicircle law

Let $(\Omega, \mu)$ be a probability space and let
$X_{ij} : \Omega \to \mathbb{R}$, for $i, j \in \mathbb{N}$, be measurable functions. Suppose that
the family $(X_{ij})_{i \le j}$ is mutually independent, that all $X_{ij}$ with $i \le j$ have the
same distribution, and that for $i \le j$ both $X_{ij}$ and $X_{ij}^2$ are integrable with
$\mathbb{E}[X_{ij}] = 0$ and $\mathbb{E}[X_{ij}^2] = 1$. For $n \ge 1$ and
$\omega \in \Omega$, let $W_n(\omega)$ be the $n \times n$ Wigner matrix of $X$ and let
$L_n(\omega)$ be the image of its empirical spectral measure under $x \mapsto x / \sqrt{n}$, that
is, the empirical spectral measure of $W_n(\omega) / \sqrt{n}$. Then for $\mu$-almost every $\omega$,
every bounded continuous function $f : \mathbb{R} \to \mathbb{R}$ satisfies

$$\int f \, dL_n(\omega) \to \int f \, d\sigma \quad (n \to \infty),$$

where $\sigma$ is the semicircle distribution.

## Informally uses

- [The even moments of the semicircle distribution are the Catalan numbers](integral-pow-two-mul-semicircle-real.md):
  the moment method shows that $\frac{1}{n}\mathbb{E}\operatorname{tr}(W_n/\sqrt{n})^{2k} \to C_k$
  and identifies the limit through this computation.
- [The odd moments of the semicircle distribution vanish](integral-pow-two-mul-add-one-semicircle.md):
  the odd normalised traces tend to $0$, the odd moments of the limit.

## Background

- [Talagrand's concentration inequality around a median](../../concentration-inequalities/talagrand-s-concentration-inequality/talagrand-concentration-median.md):
  background; concentration of the linear statistics $\frac{1}{n}\operatorname{tr} f(W_n/\sqrt{n})$
  upgrades convergence in expectation to almost sure convergence.
- [Hoffman–Wielandt inequality for Hermitian matrices](../../../LinearAlgebra/positive-definite-matrices/hoffman-wielandt-hermitian.md):
  background; it bounds how far the empirical spectral distribution moves under a perturbation of
  small Frobenius norm, which is how truncation reduces the theorem to bounded entries.
- [Lipschitz linear statistics of Hermitian spectra are stable](../../../LinearAlgebra/positive-definite-matrices/abs-sum-sub-sum-le-of-lipschitz-with.md):
  background; the form of that bound used for linear statistics $\frac{1}{n}\sum_i f(\lambda_i)$.
- [Expected moments of a Wigner matrix converge to the semicircle moments](tendsto-expected-moment-wigner-matrix-re.md):
  background; the first half of the moment method under moments of all orders (Anderson, Guionnet
  and Zeitouni, Lemma 2.1.6 in the authors' 2009 pre-publication manuscript).
- [Concentration of linear spectral statistics](concentration-trace-lipschitz.md):
  background; for entries satisfying a logarithmic Sobolev inequality, the fluctuations of
  $\operatorname{tr} f(X_N)$ are exponentially small at scale $N^2$, which gives almost sure
  convergence by Borel–Cantelli.
- [Ben Arous–Guionnet large deviation principle](../../large-deviations/ben-arous-guionnet-large-deviations/ben-arous-guionnet-ldp.md):
  background; for Gaussian ensembles the empirical spectral measure satisfies a large deviation
  principle at speed $N^2$ whose rate function vanishes only at $\sigma$, another route to the law.
- [Strong Bai–Yin theorem, upper bound](../operator-norm-of-random-matrices/wigner-op-norm-le-two-add.md):
  background; under a fourth moment the spectrum also stays inside $[-2 - \varepsilon, 2 + \varepsilon]$.

## Sources

- E. Wigner, 'Characteristic vectors of bordered matrices with infinite dimensions', Ann. of Math. (2) 62 (1955) 548–564 (the expected moments of the eigenvalue distribution of random-sign real symmetric matrices, with zero diagonal and off-diagonal entries ±v, converge to the semicircle moments; extended to a wider class in Ann. of Math. 67 (1958)). Pastur's universality extending to all variances with finite second moments: L. Pastur, 'On the spectrum of random matrices', Teor. Mat. Fiz. 10 (1972) 102–112. Listed as §102 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Problem `wigner_semicircle` of the lean-eval benchmark.
- T. Tao, *Topics in Random Matrix Theory*, Graduate Studies in Mathematics 132, American Mathematical Society, 2012, Theorem 2.4.2: this almost-sure statement, with diagonal entries allowed a different law.
