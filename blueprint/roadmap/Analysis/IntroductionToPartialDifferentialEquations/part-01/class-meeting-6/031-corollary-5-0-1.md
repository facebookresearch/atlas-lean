---
article_id: af_0d1dd384a65974fbaa1875e5
declaration: theorem
origin: cited
statement: formalized
lean: CM6.dirichlet_uniqueness_comparison_stability
---

# Corollary 5.0.1

Let $\Omega \subset \mathbb{R}^{n}$ be a bounded domain and let $f \in C(\Omega)$. Then the PDE $\Delta u=0$ for $x \in \Omega$, $u(x)=f(x)$ for $x \in \partial \Omega$ has at most one solution $u_{f} \in C^{2}(\Omega) \cap C(\bar{\Omega})$. Furthermore, if $u_{f}$ and $u_{g}$ are the solutions corresponding to the data $f, g \in C(\bar{\Omega})$, then (1) (Comparison Principle) If $f \geq g$ on $\partial \Omega$ and $f \neq g$, then $u_{f}>u_{g}$ in $\Omega$. (2) (Stability Estimate) For any $x \in \Omega$, we have that $|u_{f}(x)-u_{g}(x)| \leq \max_{y \in \partial \Omega}|f(y)-g(y)|$.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Theorem 5.1 (Strong Maximum Principle)](030-strong-maximum-principle.md)

## Sources

- [MIT 18.152 Introduction to Partial Differential Equations (Fall 2011), Class Meeting #6, Section 5 (Maximum Principle)](../../../../../sources/v1/IntroductionToPartialDifferentialEquations.md)
