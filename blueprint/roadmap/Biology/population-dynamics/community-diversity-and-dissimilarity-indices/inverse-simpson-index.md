# Inverse Simpson index

Let a community be described by the relative abundances $p = (p_1,\dots,p_S)$ of $S$ types, with $p_i \ge 0$ and $\sum_i p_i = 1$. Simpson's concentration is $\lambda(p) = \sum_{i=1}^{S} p_i^2$, the probability that two individuals drawn independently with replacement are of the same type, and the inverse Simpson index is

$$D_2(p) = \frac{1}{\lambda(p)} = \Big(\sum_{i=1}^{S} p_i^{2}\Big)^{-1} .$$

It satisfies $1 \le D_2(p) \le S$, with $D_2(p) = S$ exactly at the uniform distribution $p_i = 1/S$ and $D_2(p) = 1$ exactly when one type has $p_i = 1$. If a community consists of $m$ equally abundant types then $D_2 = m$, so $D_2$ is measured in units of effective types. It is the Hill number of order $2$, $D_q = (\sum_i p_i^q)^{1/(1-q)}$ at $q = 2$, and is a Schur-concave function of $p$: any transfer of abundance from a rarer to a commoner type decreases it.

## Remarks

Expressing diversity as an effective number of types, rather than as a probability or an entropy, makes it linear in the quantity people reason about: a community with $D_2 = 10$ is as diverse, by this criterion, as ten equally common types, and doubling $D_2$ means doubling that count. The order $q = 2$ fixes how rare types are weighted: because abundances are squared, $D_2$ is dominated by the common types and is far less sensitive than species richness ($q = 0$) to sampling depth and to singletons, which is why it is preferred for census data where rare types are incompletely observed. The bounds follow from the Cauchy-Schwarz inequality $\big(\sum_i p_i\big)^2 \le S \sum_i p_i^2$ for the upper bound on $\lambda^{-1}$ and from $\sum_i p_i^2 \le \max_i p_i \le 1$ for the lower one.

## Sources

- Human Microbiome Project Consortium. Structure, function and diversity of the healthy human microbiome. *Nature* 486:207-214 (2012), Figure 1A, within-subject alpha diversity by body habitat. DOI <https://doi.org/10.1038/nature11234>. PMCID PMC3564958.
- Simpson EH. Measurement of diversity. *Nature* 163:688 (1949). DOI <https://doi.org/10.1038/163688a0>.
