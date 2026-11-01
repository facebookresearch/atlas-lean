---
article_id: af_571fbaf341f8a6debf188fdc
declaration: theorem
origin: cited
lean: PDEClassification.classification_theorem_3_1
---

# Theorem 3.1 (Classification of second order constant-coefficient PDEs)

Consider the following second order constant coefficient PDE $\mathcal{L} u(x) \coloneqq A^{\alpha \beta} \partial_{\alpha} \partial_{\beta} u(x) + B^{\alpha} \partial_{\alpha} u(x) + Cu(x) = 0$ where $\partial_{\alpha} \coloneqq \frac{\partial}{\partial x^{\alpha}}$. Then there exists a linear change of variables $y^{\mu} = M_{\alpha}{}^{\mu} x^{\alpha}$ such that: If all of the eigenvalues of $A^{\mu \nu}$ have the same (non-zero) sign, then can be written as $\pm \mathcal{L} u = \Delta_{y} u(y) + \widetilde{B}^{\alpha} \frac{\partial}{\partial y^{\alpha}} u(y) + Cu(y) = 0$, where $\Delta_{y} \coloneqq \sum_{\mu=0}^{n} \frac{\partial^{2}}{(\partial y^{\alpha})^{2}}$. If $n$ of the eigenvalues of $A$ have the same (non-zero) sign, and the remaining one has the opposite (non-zero) sign, then can be written as $\pm \mathcal{L} u = \square_{y} u(y) + \widetilde{B}^{\alpha} \frac{\partial}{\partial y^{\alpha}} u(y) + Cu(y) = 0$, where $\square_{y} \coloneqq (m^{-1})^{\alpha \beta} \frac{\partial}{\partial y^{\alpha}} \frac{\partial}{\partial y^{\beta}}$ is the standard linear wave operator, and $(m)^{-1} = \operatorname{diag}(-1,1,1,\cdots,1)$. If $n$ eigenvalues $\lambda^{(1)}, \cdots, \lambda^{(n)}$ of $A$ have the same (non-zero) sign, and the remaining one is $\lambda^{(0)}=0$, then can be written as $\pm \mathcal{L} u = \widetilde{B}^{0} \frac{\partial}{\partial y^{0}} u + \sum_{i=1}^{n} \frac{\partial^{2}}{(\partial y^{i})^{2}} u + \sum_{i=1}^{n} \widetilde{B}^{i} \frac{\partial}{\partial y^{i}} u + Cy = 0$. Furthermore, let $v^{(0)}, v^{(1)}, \cdots, v^{(n)}$ be a corresponding diagonalizing unit-length co-vector basis. Then if the non-zero vector $B$ satisfies $B^{\alpha} v_{\alpha}^{(0)} \neq 0$, we also have that $\widetilde{B}^{0} \neq 0$.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.152 Introduction to Partial Differential Equations (Fall 2011), Class Meeting #15, Section 3](../../../../../sources/v1/IntroductionToPartialDifferentialEquations.md)
