---
article_id: af_99236754aa643fc9d77e81ec
declaration: def
origin: cited
statement: formalized
lean: Chapter3.SatisfiesOracleInequality
---

# Definition 3.2

Let $R(\cdot)$ be a risk function and let $\mathcal{H} = \{\varphi_1, \ldots, \varphi_M\}$ be a dictionary of functions from $\mathbb{R}^d$ to $\mathbb{R}$. Let $K$ be a subset of $\mathbb{R}^M$. The oracle on $K$ with respect to $R$ is defined by $\varphi_{\bar{\theta}}$, where $\bar{\theta} \in K$ is such that $R(\varphi_{\bar{\theta}}) \leq R(\varphi_\theta)$, for all $\theta \in K$. Moreover, $R_K = R(\varphi_{\bar{\theta}})$ is called oracle risk on $K$. An estimator $\hat{f}$ is said to satisfy an oracle inequality (over $K$) with remainder term $\varphi$ in expectation (resp. with high probability) if there exists a constant $C \geq 1$ such that $\mathbb{E}[R(\hat{f})] \leq C \inf_{\theta \in K} R(\varphi_\theta) + \varphi_{n,M}(K)$, or $\mathbb{P}\{R(\hat{f}) \leq C \inf_{\theta \in K} R(\varphi_\theta) + \varphi_{n,M,\delta}(K)\} \geq 1 - \delta$, for all $\delta > 0$, respectively. If $C = 1$, the oracle inequality is sometimes called exact.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.S997 High-Dimensional Statistics (Spring 2015), Chapter 3, Section 3.1](../../../../sources/v1/HighDimensionalStatistics.md)
