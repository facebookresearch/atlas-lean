# Tracy–Widom limit of the trace-normalized largest Wishart eigenvalue

Let $M \in \mathbb{R}^{m \times n}$ have i.i.d. $\mathcal{N}(0, 1)$ entries, and let
$\lambda_1 \ge \dots \ge \lambda_m$ be the eigenvalues of $X = M M^\top$. Define the
unnormalized and trace-normalized largest eigenvalues

$$L = \lambda_1, \qquad L' = \frac{m \lambda_1}{\sum_{i=1}^m \lambda_i} \cdot n,$$

and the Johnstone centering and scaling parameters

$$\mu(m, n) = \bigl(\sqrt{n - 1} + \sqrt{m}\bigr)^2, \qquad \sigma(m, n) = \bigl(\sqrt{n - 1} + \sqrt{m}\bigr)\left(\frac{1}{\sqrt{n - 1}} + \frac{1}{\sqrt{m}}\right)^{1/3}.$$

As $m, n \to \infty$ with $n / m \to \gamma \in [1, \infty)$, both $(L - \mu)/\sigma$ and
$(L' - \mu)/\sigma$ converge in distribution to the Tracy–Widom law $\mathrm{TW}_1$.

## Depends on

- [Method-of-moments estimator for effective number of markers in a Wishart matrix](effective-number-of-markers-wishart-estimator.md)

## Expansion

By Johnstone's theorem, $(L - \mu)/\sigma \Rightarrow \mathrm{TW}_1$. Meanwhile, the sample trace
$S = \sum_{i=1}^m \lambda_i$ has mean $mn$ and standard deviation $O(\sqrt{mn})$, so
$S/(mn) = 1 + O_p((mn)^{-1/2})$. Since $\mu = \Theta(n)$ and $\sigma = \Theta(n^{1/2} m^{-1/6})$,
the discrepancy $(L' - L)/\sigma = O_p(m^{-1/3})$ vanishes in probability, so Slutsky's theorem
gives the same $\mathrm{TW}_1$ limit for $L'$.

## Sources

- N. Patterson, A. L. Price, and D. Reich, "Population Structure and Eigenanalysis", PLOS Genetics 2 (2006), e190, <https://doi.org/10.1371/journal.pgen.0020190> (PMC1713260). (Theorem 2.)
