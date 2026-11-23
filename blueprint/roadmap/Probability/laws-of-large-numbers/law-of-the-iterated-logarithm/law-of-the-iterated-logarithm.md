# Law of the iterated logarithm

Let $X_0, X_1, \dots$ be independent, identically distributed,
measurable real random variables on a probability space such that $X_0$ is integrable,
$\mathbb{E}[X_0^2] < \infty$, $\mathbb{E}[X_0] = 0$ and $\operatorname{Var}(X_0) = 1$, and let
$S_n = X_0 + \dots + X_{n-1}$. Then almost surely
$\limsup_{n \to \infty} S_n / \sqrt{2 n \log \log n} = 1$ and
$\liminf_{n \to \infty} S_n / \sqrt{2 n \log \log n} = -1$.

Proof: Hartman–Wintner truncation and exponential maximal bounds give the upper half; a CLT block
argument and the second Borel–Cantelli lemma give the lower half.

## Sources

- A. Y. Khinchin 1924, A. N. Kolmogorov 1929, P. Hartman and A. Wintner, On the law of the iterated logarithm, Amer. J. Math. 63 (1941) 169–176; textbook in Durrett, Probability Theory and Examples, 5th ed., Foundations of Modern Probability (Hartman-Wintner LIL). Lean i.i.d. mean-zero variance-one normalized `√(2 n log log n)` form.
