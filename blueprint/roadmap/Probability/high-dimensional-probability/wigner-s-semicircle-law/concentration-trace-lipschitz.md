# Concentration of linear spectral statistics

Let $N \ge 1$ and $c > 0$, and let $X_N$ be the real symmetric $N \times N$ random matrix, on a probability space,
with independent measurable entries $X_{ij}$, $i \le j$, whose laws $\nu_{ij}$ satisfy the logarithmic Sobolev
inequality with constant $c/N$ in the following form: for every nonnegative Lipschitz function $h$ with
$\int h \, d\nu_{ij} = 1$,

$$\frac{2N}{c}\, \int h \log h \, d\nu_{ij} \le \int_{\{h > 0\}} \frac{|\nabla h|^2}{h} \, d\nu_{ij},$$

where $|\nabla h|(x)$ is the local Lipschitz constant of $h$ at $x$; for $h = f^2$ this is
$\int f^2 \log f^2 \le \frac{2c}{N} \int |f'|^2$ when $\int f^2 = 1$. Then for every
$L$-Lipschitz $f : \mathbb{R} \to \mathbb{R}$ and every $\delta > 0$,

$$\mathbb{P}\Bigl(\bigl|\operatorname{tr} f(X_N) - \mathbb{E}\operatorname{tr} f(X_N)\bigr| \ge \delta N\Bigr)
\le 2 \exp\Bigl(-\frac{N^2 \delta^2}{4 c L^2}\Bigr),$$

where $\operatorname{tr} f(X_N) = \sum_i f(\lambda_i)$. For the normalised trace
$\frac{1}{N}\operatorname{tr} f(X_N) = \int f \, dL_N$ this is a deviation of $\delta$ at probability
$e^{-O(N^2)}$, the large deviation scale of the empirical spectral measure. Gaussian entries of
variance $1/N$ satisfy the hypothesis with $c = 1$.

Proof in the source: the map from the entries to $\operatorname{tr} f(X_N)$ is Lipschitz with
constant at most $\sqrt{2N}\,L$ for the Euclidean norm on the entries (Lemma 2.3.1, from the
Hoffman–Wielandt inequality, Lemma 2.1.19), the product of the entry laws satisfies the logarithmic Sobolev inequality with
constant $c/N$ (tensorisation), and Herbst's argument (Lemma 2.3.3) gives the Gaussian tail.

## Informally uses

- [Hoffman–Wielandt inequality for Hermitian matrices](../../../LinearAlgebra/positive-definite-matrices/hoffman-wielandt-inequality/hoffman-wielandt-hermitian.md):
  the Lipschitz bound for the spectral map.
- [Logarithmic Sobolev inequality](../../concentration-inequalities/transport-cost-inequalities/README.md):
  the hypothesis and its tensorisation.

## Sources

- G. W. Anderson, A. Guionnet and O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press, 2010 (numbering of the authors' pre-publication manuscript (2009), https://www.math.nyu.edu/~zeitouni/cupbook.pdf), Theorem 2.3.5, inequality (2.3.9), with Lemmas 2.3.1 and 2.3.3.
- A. Guionnet and O. Zeitouni, "Concentration of the spectral measure for large matrices",
  *Electron. Comm. Probab.* 5 (2000), 119–136, as reproduced in A. Guionnet, *Probability Surveys*
  1 (2004), Theorem 3.2(b).
