---
article_id: af_8b2bf5c372a7178de93d7a9b
declaration: def
origin: cited
statement: formalized
lean: RayClassField.HasDirichletDensity
---

# Definition 18.22

The Dirichlet density of a set of primes $S$ is given by $$d(S)\coloneqq \lim_{s \rightarrow 1^{+}} \frac{\sum_{p \in S} p^{-s}}{\sum_{p} p^{-s}}$$ defined whenever this limit exists (one can also define notions of lower and upper Dirichlet density using liminf and lim sup which both agree with $d(S)$ whenever it is defined). This definition differs from the more common notion of natural density $$\delta(S)\coloneqq \lim_{x \rightarrow \infty} \frac{\#\{p \leq x: p \in S\}}{\#\{p \leq x\}}.$$

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.785 Number Theory I (Fall 2021), Section 18.4](../../../../../../sources/v1/NumberTheoryI.md)
