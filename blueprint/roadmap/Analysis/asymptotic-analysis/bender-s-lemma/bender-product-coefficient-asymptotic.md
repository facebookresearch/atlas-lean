# Bender's lemma on coefficients of a product of power series

Let $(a_n)$ and $(b_n)$ be
real sequences such that $A(z) = \sum_n a_n z^n$ has radius of convergence $\alpha \in [0, \infty]$
and $\sum_n b_n z^n$ has radius of convergence $\beta$, where $\beta \ge 0$ is a real number with
$\beta < \alpha$. Suppose that $b_n \neq 0$ for all sufficiently large $n$, that
$b_{n-1} / b_n \to \beta$ as $n \to \infty$, and that $A(\beta) \neq 0$. Then the coefficients
$c_n = \sum_{k=0}^{n} a_k b_{n-k}$ of the product of the formal power series $\sum_n a_n z^n$ and
$\sum_n b_n z^n$ satisfy $c_n \sim A(\beta) \, b_n$ as $n \to \infty$.

The hypothesis that $b_n$ is eventually nonzero makes the ratios $b_{n-1} / b_n$ meaningful; with
the convention $x / 0 = 0$ the statement fails at $\beta = 0$ without it: for $A(z) = 1 + z$ and
$b$ vanishing at every even index and growing fast at odd indices, every ratio is $0$ while the
even product coefficients stay nonzero.

## Sources

- Dennis E. Davenport, Louis W. Shapiro, Lara K. Pudwell, and Leon C. Woodson, "The Boundary of Ordered Trees," Journal of Integer Sequences 18 (2015). Source file: `https://cs.uwaterloo.ca/journals/JIS/VOL18/Davenport/dav3.tex` (Bender's lemma, lines 521-523). File SHA-256: `32a240baaed6ae2300ec1302ccf7d3cd50dc1976868c161f0029c77d0d43b845`. Span SHA-256 (LF joining, no terminal LF): `665087b645846d87aadb08ae26e311b6d717dd5340e113e601cacab26f1c0d85`. Concept: `jis_grounded_6fda7dab32c4f4ae24158c9e` (dependency `jis_dep_2479eb9e033e69c0a770ff11`). It follows from `bender_product_coefficient_asymptotic_general`; the hypothesis `hB` is unused and keeps the source's shape. Proves `Wanted` entry `bender_product_coefficient_asymptotic`.
