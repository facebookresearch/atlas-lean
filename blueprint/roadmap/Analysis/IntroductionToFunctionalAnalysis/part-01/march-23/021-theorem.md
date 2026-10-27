---
article_id: af_f02f8ed93f397497b07fa815
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MeasureTheory.SimpleFunc.exists_monotone_tendsto
---

# Theorem (March 23, 2021)

If $f: E \to [0, \infty]$ is a nonnegative measurable function, then there exists a sequence of simple functions $\{\phi_n\}$ such that the following properties hold: (a) We have a pointwise increasing sequence of functions dominated by $f$: $0 \leq \phi_0(x) \leq \phi_1(x) \leq \cdots \leq f(x)$ for all $x \in E$. (b) Pointwise convergence holds: $\lim_{n \to \infty} \phi_n(x) = f(x)$ for all $x \in E$. (c) For all $B \geq 0$, $\phi_n \to f$ converges uniformly on the set $\{x \in E \mid f(x) \leq B\}$ where $f$ is bounded.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.102 Introduction to Functional Analysis (Spring 2021), March 23, 2021](../../../../../sources/v1/IntroductionToFunctionalAnalysis.md)
