# Tracy–Widom limit of the trace-normalized largest Wishart eigenvalue

Let $m, n \to \infty$ along a sequence with $n / m \to \gamma \in [1, \infty)$. For each term, let
$M \in \mathbb{R}^{m \times n}$ have i.i.d. $\mathcal{N}(0, 1)$ entries, and let
$\lambda_1 \ge \dots \ge \lambda_m$ be the eigenvalues of $X = M M^\top$. Define the unnormalized and
trace-normalized largest eigenvalues

$$L = \lambda_1, \qquad L' = \frac{m n\, \lambda_1}{\sum_{i=1}^m \lambda_i},$$

and the Johnstone centring and scaling

$$\mu(m, n) = \bigl(\sqrt{n - 1} + \sqrt{m}\bigr)^2, \qquad \sigma(m, n) = \bigl(\sqrt{n - 1} + \sqrt{m}\bigr)\left(\frac{1}{\sqrt{n - 1}} + \frac{1}{\sqrt{m}}\right)^{1/3}.$$

Then $(L' - \mu)/\sigma$ converges in distribution to the Tracy–Widom law $F_1$ of
[Johnstone's Tracy–Widom limit](../../../Probability/high-dimensional-probability/johnstone-largest-eigenvalue-tracy-widom.md).

The corresponding limit for $L$ is Johnstone's theorem applied to the $n \times m$ matrix $M^\top$, whose Gram
matrix $(M^\top)^\top M^\top$ is $X$; it is the input of the proof below, not a conclusion of this page. Patterson, Price and Reich state the limit for $L'$ with $\gamma > 1$; the
argument below covers $\gamma = 1$ as well.

## Depends on

- [Johnstone's Tracy–Widom limit](../../../Probability/high-dimensional-probability/johnstone-largest-eigenvalue-tracy-widom.md)

## Proof depends on

- [The square of a standard normal variable is chi-square with one degree of freedom](../../../Probability/distributions/continuous/chi-square-distribution/gaussian-real-map-sq.md)

## Expansion

Johnstone's theorem with $X$ replaced by $M^\top$ (sample size $n$, dimension $m$) gives
$(L - \mu)/\sigma \Rightarrow F_1$. The trace $S = \sum_i \lambda_i$ is a sum of $mn$ independent $\chi_1^2$
variables, so $S/(mn) = 1 + O_p((mn)^{-1/2})$. Since $\lambda_1 = O_p(\mu)$ with $\mu = \Theta(n)$ and
$\sigma = \Theta(n^{1/2} m^{-1/6})$, the difference $(L' - L)/\sigma = \lambda_1 (mn/S - 1)/\sigma$ is
$O_p(m^{-1/3})$ and tends to $0$ in probability, so Slutsky's theorem gives the same limit for $L'$.

## Sources

- N. Patterson, A. L. Price, and D. Reich, "Population Structure and Eigenanalysis", PLOS Genetics 2 (2006), e190, <https://doi.org/10.1371/journal.pgen.0020190> (PMC1713260). (Theorem 2.)
- I. M. Johnstone, *On the distribution of the largest eigenvalue in principal components analysis*, Ann. Statist. 29 (2001), 295–327, Theorem 1.1.
