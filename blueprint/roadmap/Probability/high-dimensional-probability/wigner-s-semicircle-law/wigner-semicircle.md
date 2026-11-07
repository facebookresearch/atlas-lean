# Wigner's semicircle law

Let $(\Omega, \mu)$ be a probability space and let
$X_{ij} : \Omega \to \mathbb{R}$, for $i, j \in \mathbb{N}$, be measurable functions. Suppose that
the family $(X_{ij})_{i \le j}$ is mutually independent, that all $X_{ij}$ with $i \le j$ have the
same distribution, and that for $i \le j$ both $X_{ij}$ and $X_{ij}^2$ are integrable with
$\mathbb{E}[X_{ij}] = 0$ and $\mathbb{E}[X_{ij}^2] = 1$. For $n \in \mathbb{N}$ and
$\omega \in \Omega$, let $W_n(\omega)$ be the Wigner matrix of $X$ and let $L_n(\omega)$ be the
image of its empirical spectral measure under $x \mapsto x / \sqrt{n}$ (for $n \ge 1$, the
empirical spectral measure of $W_n(\omega) / \sqrt{n}$). Then for $\mu$-almost every $\omega$,
every bounded continuous function $f : \mathbb{R} \to \mathbb{R}$ satisfies

$$\int f \, dL_n(\omega) \to \int f \, d\sigma \quad (n \to \infty),$$

where $\sigma$ is the semicircle distribution.

## Sources

- E. Wigner, 'Characteristic vectors of bordered matrices with infinite dimensions', Ann. of Math. (2) 62 (1955) 548–564 (Gaussian case). Pastur's universality extending to all variances with finite second moments: L. Pastur, 'On the spectrum of random matrices', Teor. Mat. Fiz. 10 (1972) 102–112. Listed as §102 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `wigner_semicircle`.
