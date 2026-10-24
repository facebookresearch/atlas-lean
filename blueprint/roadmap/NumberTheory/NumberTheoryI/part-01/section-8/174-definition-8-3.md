---
article_id: af_ffda754beb4d658867e9c9ba
declaration: abbrev
origin: cited
statement: formalized
lean: MetricCompletion
---

# Definition 8.3

Let $X$ be a metric space. Cauchy sequences $(x_n)$ and $(y_n)$ are equivalent if $d(x_n, y_n) \rightarrow 0$ as $n \rightarrow \infty$; this defines an equivalence relation on the set of Cauchy sequences in $X$ and we use $[(x_n)]$ to denote the equivalence class of $(x_n)$. The completion of $X$ is the metric space $\widehat{X}$ whose elements are equivalence classes of Cauchy sequences with the metric $d([(x_n)], [(y_n)]) \coloneqq \lim_{n \rightarrow \infty} d(x_n, y_n)$ (this limit exists and depends only on the equivalence classes of $(x_n)$ and $(y_n)$). We may canonically embed $X$ in its completion $\widehat{X}$ via the map $x \mapsto \hat{x} = [(x, x, \ldots)]$. When $X$ is a topological ring we extend the ring operations to $\widehat{X}$ by defining $[(x_n)] + [(y_n)] \coloneqq [(x_n + y_n)]$ and $[(x_n)][(y_n)] \coloneqq [(x_n y_n)]$; the additive and multiplicative identities $0 \coloneqq \hat{0}$ and $1 \coloneqq \hat{1}$. When the metric on $X$ is induced by an absolute value $|\,|$, we extend $|\,|$ to an absolute value on $\widehat{X}$ via $|[(x_n)]| \coloneqq \lim_{n \rightarrow \infty} |x_n|$.

## Depends on

- [Definition 1.2](../section-1/section-1-2/001-definition-1-2.md)
- [Definition 8.1](172-definition-8-1.md)
- [Definition 8.2](173-definition-8-2.md)

## Sources

- [MIT 18.785 Number Theory I (Fall 2021), Section 8.1](../../../../../sources/v1/NumberTheoryI.md)
