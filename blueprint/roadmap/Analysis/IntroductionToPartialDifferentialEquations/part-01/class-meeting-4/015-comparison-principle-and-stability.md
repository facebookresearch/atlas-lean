---
article_id: af_09b297c66efba70ff98b7863
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: WeakMaximumPrinciple.corollary_1_0_1
---

# Corollary 1.0.1 (Comparison Principle and Stability)

Suppose that $v$, $w$ are solutions to the heat equations $v_{t}-D v_{x x}=f$ and $w_{t}-D w_{x x}=g$. Then (1) (Comparison): If $v \geq w$ on $\partial_{p} Q_{T}$ and $f \geq g$, then $v \geq w$ on all of $Q_{T}$. (2) (Stability): $\max_{\bar{Q}_{T}}|v-w| \leq \max_{\partial_{p} Q_{T}}|v-w|+T \max_{\bar{Q}_{T}}|f-g|$.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Theorem 1.1 (Weak Maximum Principle)](014-weak-maximum-principle.md)

## Sources

- [MIT 18.152 Introduction to Partial Differential Equations (Fall 2011), Class Meeting #4, Section 1 (The Weak Maximum Principle)](../../../../../sources/v1/IntroductionToPartialDifferentialEquations.md)
