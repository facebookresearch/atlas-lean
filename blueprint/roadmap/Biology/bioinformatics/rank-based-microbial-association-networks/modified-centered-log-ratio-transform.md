# Modified centered log-ratio transform for zero-inflated compositions

**Definition.** Let $x_i \in \mathcal S^p$ be a composition (non-negative entries summing to one) for sample $i$, with zero set $Z_i = \{ j : x_{ij} = 0 \}$ and non-zero set $N_i$, $|N_i| = p - q_i \ge 1$. Let

$$\tilde g(x_i) = \Big( \prod_{j \in N_i} x_{ij} \Big)^{1/(p - q_i)}$$

be the geometric mean of the non-zero entries. For a shift $\varepsilon \ge 0$ the modified centered log-ratio transform is

$$\mathrm{mclr}_\varepsilon(x_i)_j = \begin{cases} 0, & j \in Z_i, \\ \log\{ x_{ij} / \tilde g(x_i) \} + \varepsilon, & j \in N_i. \end{cases}$$

For $\varepsilon = 0$ this is the ordinary clr transform $\log\{x_{ij}/g(x_i)\}$ applied to the non-zero proportions only. The data-driven shift is $\varepsilon = |z_{\min}| + c$ with $z_{\min} = \min_{i, j \in N_i} \log\{x_{ij}/\tilde g(x_i)\}$ and a constant $c > 0$ (default $c = 1$).

**Properties.**

- With this $\varepsilon$, every non-zero entry is mapped to a value $\ge c > 0$, so zeros remain the strictly smallest values in every sample and, within each sample, the order of all entries of $x_i$ is preserved in $\mathrm{mclr}_\varepsilon(x_i)$. Rank-based statistics (for example Kendall's $\tau$) computed on transformed data therefore treat zeros as ties at the bottom without any pseudo-count.
- The transform is scale invariant: $\mathrm{mclr}_\varepsilon(a x_i) = \mathrm{mclr}_\varepsilon(x_i)$ for $a > 0$, because $\tilde g(a x_i) = a\,\tilde g(x_i)$; it can therefore be applied to raw counts or to proportions.

## Expansion

Order preservation holds because $t \mapsto \log(t/\tilde g(x_i)) + \varepsilon$ is strictly increasing on $(0,\infty)$ and its minimum over all non-zero entries in the data set is at least $c$. Adding pseudo-counts instead would alter the observed non-zero proportions and make zeros indistinguishable from small counts. The transformed data are then modelled by the truncated Gaussian copula, with zeros as truncated latent values.

## Sources

- G. Yoon, I. Gaynanova, C. L. Müller, "Microbial Networks in SPRING - Semi-parametric Rank-Based Correlation and Partial Correlation Estimation for Quantitative Microbiome Data", Frontiers in Genetics 10:516 (2019), Section 2 (modified clr transform, Eq. 2 and Figure 1), <https://doi.org/10.3389/fgene.2019.00516> (PMC6563871).
