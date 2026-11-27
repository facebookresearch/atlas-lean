# Stochastic cone of a Lie Markov model

**Definitions.** Let $\mathfrak L_{GM}$ be the complex span of the $n(n-1)$ elementary rate matrices $L_{ij}$ ($i\neq j$), and $\mathfrak L_{GM}^{\mathbb R}$ their real span. The cone of stochastic rate matrices is

$$\mathfrak L_{GM}^{+}=\Bigl\{\sum_{i\neq j}\alpha_{ij}L_{ij}:\alpha_{ij}\ge 0\Bigr\}.$$

A **stochastic basis** of a complex subspace $\mathfrak L\subseteq\mathfrak L_{GM}$ is a basis of non-negative combinations of the $L_{ij}$. Following Definition 2.1, a **Lie Markov model** is a complex Lie subalgebra of $\mathfrak L_{GM}$ that has a stochastic basis. Its **stochastic cone** is $\mathfrak L^{+}=\mathfrak L\cap\mathfrak L_{GM}^{+}$ and its rays are the rays of this cone.

**Theorem 2.2.** For every complex subspace $\mathfrak L\subseteq\mathfrak L_{GM}$, $\mathfrak L^{+}$ is a strongly convex polyhedral cone in $\mathfrak L_{GM}^{\mathbb R}$, and

$$\dim\mathfrak L^{+}\le\dim_{\mathbb C}\mathfrak L,$$

with equality if and only if $\mathfrak L$ has a stochastic generating set (equivalently, a stochastic basis).

Consequently the dimension of a Lie Markov model (Definition 2.3) is both its complex dimension and the dimension of its set of stochastic rate matrices. If a Lie algebra $\mathfrak L$ has no stochastic basis, the complex span $\mathfrak L'=\mathbb C\mathfrak L^{+}$ is a strictly smaller Lie algebra with a stochastic basis and the same stochastic cone (Remark 2), so requiring a stochastic basis picks the smallest Lie algebra carrying a given set of stochastic rate matrices.

## Expansion

$\mathfrak L^{+}$ is the intersection of two polyhedral cones (a linear subspace is one), hence polyhedral by Farkas's theorem, and it contains no line because $\mathfrak L_{GM}^{+}$ has non-negative coordinates. Since $\mathfrak L^{+}$ consists of real matrices, the complex span of $\mathfrak L^{+}$ has complex dimension equal to the real dimension of its real span, and it sits inside $\mathfrak L$. A stochastic generating set lies in $\mathfrak L^{+}$ and spans $\mathfrak L$, giving equality; conversely, a real basis of $\mathbb R\mathfrak L^{+}$ chosen inside $\mathfrak L^{+}$ spans a complex subspace of full dimension, hence all of $\mathfrak L$. Real brackets of real matrices are real, so $\mathbb C\mathfrak L^{+}$ inherits bracket closure.

## Sources

- Jesús Fernández-Sánchez, Jeremy G. Sumner, Peter D. Jarvis and Michael D. Woodhams, "Lie Markov models with purine/pyrimidine symmetry", arXiv:1206.1401 (2012), Section 2 (Definition 2.1, Theorem 2.2, Remarks 1–2, Definition 2.3), <https://doi.org/10.48550/arXiv.1206.1401>. Published version: Journal of Mathematical Biology 70(4) (2015), 855–891, <https://doi.org/10.1007/s00285-014-0773-z>; locators above refer to the arXiv version.
