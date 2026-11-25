# The Laplace mechanism for vector-valued queries

Let $f : X \to \mathbb{R}^k$ have $\ell_1$-sensitivity at most $\Delta > 0$:
$\sum_{i} |f(x)_i - f(y)_i| \le \Delta$ for all neighbours $x, y$. For $\varepsilon > 0$, releasing
$f(x) + (Y_1, \dots, Y_k)$ with $Y_i$ independent $\mathrm{Lap}(0, \Delta/\varepsilon)$ is
$\varepsilon$-differentially private.

The proof fixes two neighbours $x, y$ and views coordinate $i$ as a mechanism on the two-point
set $\{x, y\}$ whose privacy loss is $|f(x)_i - f(y)_i| \varepsilon / \Delta$; basic composition then
bounds the joint loss by the sum, which is at most $\varepsilon$. The source instead multiplies the
coordinate density ratios directly; both arguments rest on the same pointwise bound.

## Informally uses

- [Shifting the Laplace density](../../../Probability/distributions/continuous/laplace-distribution/laplace-pdfreal-le-exp-mul.md): the coordinatewise density ratio bound, whose product over the coordinates is the source's proof.

## Sources

- C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Foundations and Trends in Theoretical Computer Science 9(3–4), 2014, <https://www.cis.upenn.edu/~aaroth/privacybook.html>, Definition 3.3 and Theorem 3.6.
- C. Dwork, F. McSherry, K. Nissim and A. Smith, *Calibrating noise to sensitivity in private data analysis*, TCC 2006 (the Laplace mechanism, cited in Dwork and Roth 2014, Section 3.7).
