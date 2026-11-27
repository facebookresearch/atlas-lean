# Asymptotic p-value bound for the local similarity statistic

**Statistic.** Let $X = (X_1,\dots,X_n)$ and $Y = (Y_1,\dots,Y_n)$ be standardized time series and $D \ge 0$ a maximal lag. With $P_{i,0} = P_{0,j} = N_{i,0} = N_{0,j} = 0$, define for $1 \le i,j \le n$ with $|i-j| \le D$

$$P_{i,j} = \max\{0,\ P_{i-1,j-1} + X_i Y_j\}, \qquad N_{i,j} = \max\{0,\ N_{i-1,j-1} - X_i Y_j\},$$

$\hat P = \max_{|i-j|\le D} P_{i,j}$, $\hat N = \max_{|i-j|\le D} N_{i,j}$, and the local similarity score

$$\mathrm{LSA}(X,Y) = \operatorname{sign}(\hat P - \hat N)\,\frac{\max\{\hat P, \hat N\}}{n}.$$

The computation for $m$ series takes $O(m^2 n D)$ time.

**Lemma (tail event).** For every $x$, $\{|\mathrm{LSA}| > x\} = \bigcup_{i,j}\{P_{i,j} > xn\} \cup \bigcup_{i,j}\{N_{i,j} > xn\}$, the unions over $|i-j| \le D$.

**Lemma (reflected walk).** If $Z_1, Z_2,\dots$ are i.i.d., $S_0 = 0$, $S_k = Z_1+\cdots+Z_k$, and $q_0 = 0$, $q_{k} = \max\{0, q_{k-1} + Z_k\}$, then $q_k$ has the same distribution as $\max\{S_0,\dots,S_k\}$.

**Theorem.** Assume, under the null hypothesis of no association, that the products $X_iY_j$ entering each recursion are independent with mean $0$ and variance $\sigma^2 = \operatorname{Var}(X_1Y_1)$. Let $G(y) = \sqrt{2/\pi}\int_0^{y} e^{-t^2/2}\,dt$ for $y \ge 0$ be the distribution function of $|Z|$, $Z$ standard normal. Then, asymptotically as $n\to\infty$,

$$P\bigl(|\mathrm{LSA}| > x\bigr) \;\lesssim\; 2\,\bigl[n^2 - (n-D-1)(n-D)\bigr]\Bigl(1 - G\bigl(x\sqrt{n}/\sigma\bigr)\Bigr),$$

where $n^2 - (n-D-1)(n-D)$ is the number of index pairs with $|i-j|\le D$; for standardized products ($\sigma = 1$) the bound is $2\,\bigl[n^2-(n-D-1)(n-D)\bigr]\bigl(1-G(x\sqrt n)\bigr)$.

## Expansion

The tail-event lemma is the definition of $\mathrm{LSA}$ rewritten: $|\mathrm{LSA}| > x$ iff $\max(\hat P,\hat N) > xn$ iff some $P_{i,j}$ or $N_{i,j}$ exceeds $xn$. Along each diagonal, $P_{i,j}$ is a Lindley (reflected random walk) recursion, so by the reflected-walk lemma it has the law of the running maximum of partial sums of at most $\min(i,j) \le n$ products. The Erdős–Kac (Nevzorov–Petrov) invariance principle for maxima of partial sums under the Lindeberg condition gives $P(\max_{k\le m} S_k \le \sigma\sqrt{m}\,y) \to G(y)$ uniformly in $y$, so $P(P_{i,j} > xn) \approx 1 - G(xn/(\sigma\sqrt{m})) \le 1 - G(x\sqrt n/\sigma)$ since $m \le n$. The same holds for $N_{i,j}$. Boole's inequality over the $2[n^2-(n-D-1)(n-D)]$ events gives the bound. It is conservative and asymptotic; the authors recommend at least about 30 time points.

## Sources

- W. E. Durno, N. W. Hanson, K. M. Konwar, S. J. Hallam, "Expanding the boundaries of local similarity analysis", BMC Genomics 14 (Suppl 1) (2013) S3, Lemmas 1–2 and Theorems 3–4, <https://doi.org/10.1186/1471-2164-14-S1-S3>, PMCID PMC3549818.
- Q. Ruan, D. Dutta, M. S. Schwalbach, J. A. Steele, J. A. Fuhrman, F. Sun, "Local similarity analysis reveals unique associations among marine bacterioplankton species and environmental factors", Bioinformatics 22 (2006) 2532–2538, <https://doi.org/10.1093/bioinformatics/btl417>.
