---
article_id: af_ad3d54a80b8b09bd756ee8ef
declaration: abbrev
origin: cited
statement: formalized
lean: FourierAnalysis.mellinTransform
---

# Definition 17.11

The Mellin transform of a function $f: \mathbb{R}_{>0} \rightarrow \mathbb{C}$ is the complex function defined by $$\mathcal{M}(f)(s)\coloneqq \int_{0}^{\infty} f(t) t^{s-1} d t$$ whenever this integral converges. It is holomorphic on $\operatorname{Re} s \in (a, b)$ for any interval $(a, b)$ in which the integral $\int_{0}^{\infty}|f(t)| t^{\sigma-1} d t$ converges for all $\sigma \in (a, b)$.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.785 Number Theory I (Fall 2021), Section 17.1.2](../../../../../sources/v1/NumberTheoryI.md)
