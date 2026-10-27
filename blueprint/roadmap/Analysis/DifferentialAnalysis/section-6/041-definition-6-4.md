---
article_id: af_02d4f05c0b4a0758af5d563a
declaration: structure
origin: cited
statement: formalized
lean: TestFunctions.ContDiffZeroAtInftyN
---

# Definition 6.4

The space $\mathcal{C}_0^{k}(\mathbb{R}^{n}) \subset \mathcal{C}_0^{1}(\mathbb{R}^{n})$, $k \geq 1$, is defined inductively by requiring that $\frac{\partial u}{\partial x_{j}} \in \mathcal{C}_0^{k-1}(\mathbb{R}^{n})$, $j = 1, \ldots, n$. The norm on $\mathcal{C}_0^{k}(\mathbb{R}^{n})$ is taken to be $\|u\|_{\mathcal{C}^{k}} = \|u\|_{\mathcal{C}^{k-1}} + \sum_{j=1}^{n} \left\|\frac{\partial u}{\partial x_{j}}\right\|_{\mathcal{C}^{k-1}}$.

## Depends on

- [Definition 6.2](039-definition-6-2.md)

## Sources

- [MIT 18.155 Differential Analysis (Fall 2004), Section 6](../../../../sources/v1/DifferentialAnalysis.md)
