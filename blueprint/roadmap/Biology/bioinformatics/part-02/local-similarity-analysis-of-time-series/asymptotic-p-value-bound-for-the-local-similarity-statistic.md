# Asymptotic p-value bound for the local similarity statistic

**Statistic.** Let $X = (X_1,\dots,X_n)$ and $Y = (Y_1,\dots,Y_n)$ be standardized time series and $D \ge 0$ a maximal lag. With $P_{i,0} = P_{0,j} = N_{i,0} = N_{0,j} = 0$, define for $1 \le i,j \le n$ with $|i-j| \le D$

$$P_{i,j} = \max\{0,\ P_{i-1,j-1} + X_i Y_j\}, \qquad N_{i,j} = \max\{0,\ N_{i-1,j-1} - X_i Y_j\},$$

$\hat P = \max_{|i-j|\le D} P_{i,j}$, $\hat N = \max_{|i-j|\le D} N_{i,j}$, and the local similarity score

$$\mathrm{LSA}(X,Y) = \operatorname{sign}(\hat P - \hat N)\,\frac{\max\{\hat P, \hat N\}}{n}.$$

The computation for $m$ series takes $O(m^2 n D)$ time.

**Lemma (tail event).** For every $x$, $\{|\mathrm{LSA}| > x\} = \bigcup_{i,j}\{P_{i,j} > xn\} \cup \bigcup_{i,j}\{N_{i,j} > xn\}$, the unions over $|i-j| \le D$.

**Lemma (reflected walk).** If $Z_1, Z_2,\dots$ are i.i.d., $S_0 = 0$, $S_k = Z_1+\cdots+Z_k$, and $q_0 = 0$, $q_{k} = \max\{0, q_{k-1} + Z_k\}$, then $q_k$ has the same distribution as $\max\{S_0,\dots,S_k\}$.

**Theorem.** (1) (Boole bound) For every $x$,

$$P\bigl(|\mathrm{LSA}| > x\bigr) \le \sum_{|i-j|\le D}\Bigl[P\bigl(P_{i,j} > xn\bigr) + P\bigl(N_{i,j} > xn\bigr)\Bigr].$$

(2) (Limit of each term) Let $G(y) = \sqrt{2/\pi}\int_0^{y} e^{-t^2/2}\,dt$ for $y \ge 0$ be the distribution function of $|Z|$, $Z$ standard normal. If $Z_1, Z_2, \dots$ are i.i.d. with mean $0$ and variance $\sigma^2 \in (0,\infty)$ and $S_k = Z_1 + \cdots + Z_k$, then $P(\max_{k\le m} S_k \le \sigma\sqrt{m}\,y) \to G(y)$ uniformly in $y \ge 0$ as $m \to \infty$.

Under the null hypothesis of no association, taking the products $X_iY_j$ along each diagonal to be i.i.d. with mean $0$ and variance $\sigma^2 = \operatorname{Var}(X_1Y_1)$ and replacing each term of (1) by the limit in (2) with $m = n$ gives the approximate p-value

$$P\bigl(|\mathrm{LSA}| > x\bigr) \approx 2\,\bigl[n^2 - (n-D-1)(n-D)\bigr]\Bigl(1 - G\bigl(x\sqrt{n}/\sigma\bigr)\Bigr),$$

where $n^2 - (n-D-1)(n-D)$ is the number of index pairs with $|i-j|\le D$. This is an approximation, not an asymptotic inequality: for fixed $x$ the true tail can decay more slowly in $n$ than the right-hand side (for i.i.d. standard normal $X_i, Y_i$ and $x = 1/2$, Cramér's theorem gives $P(|\mathrm{LSA}| > 1/2) \ge e^{-(0.1130 + o(1))n}$, while the right-hand side is $e^{-(0.125 + o(1))n}$). The source states it as an inequality (Theorem 4).

## Expansion

The tail-event lemma is the definition of $\mathrm{LSA}$ rewritten: $|\mathrm{LSA}| > x$ iff $\max(\hat P,\hat N) > xn$ iff some $P_{i,j}$ or $N_{i,j}$ exceeds $xn$. Along each diagonal, $P_{i,j}$ is a Lindley (reflected random walk) recursion, so by the reflected-walk lemma it has the law of the running maximum of partial sums of at most $\min(i,j) \le n$ products. Boole's inequality over the $2[n^2-(n-D-1)(n-D)]$ events gives (1). The Erdős–Kac invariance principle for maxima of partial sums of i.i.d. variables gives (2), and $1 - G(xn/(\sigma\sqrt{m})) \le 1 - G(x\sqrt n/\sigma)$ for $m \le n$. The invariance principle has an additive $o(1)$ error, so substituting the limit is a heuristic for each term, not a bound that tends to $0$; the authors recommend at least about 30 time points.

## Sources

- W. E. Durno, N. W. Hanson, K. M. Konwar, S. J. Hallam, "Expanding the boundaries of local similarity analysis", BMC Genomics 14 (Suppl 1) (2013) S3, Lemmas 1–2 and Theorems 3–4, <https://doi.org/10.1186/1471-2164-14-S1-S3>, PMCID PMC3549818.
- Q. Ruan, D. Dutta, M. S. Schwalbach, J. A. Steele, J. A. Fuhrman, F. Sun, "Local similarity analysis reveals unique associations among marine bacterioplankton species and environmental factors", Bioinformatics 22 (2006) 2532–2538, <https://doi.org/10.1093/bioinformatics/btl417>.
