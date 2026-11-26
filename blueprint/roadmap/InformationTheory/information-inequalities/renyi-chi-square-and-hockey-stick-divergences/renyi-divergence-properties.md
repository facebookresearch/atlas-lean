# Nonnegativity, data processing and adaptive composition of Renyi divergence

Let $\alpha > 1$ and let $p, q$ be discrete probability distributions on a countable set $X$.

1. (Nonnegativity) $M_\alpha(p\|q) \ge 1$, so $D_\alpha(p\|q) \ge 0$, and $D_\alpha(p\|p) = 0$.
2. (Data processing) For every Markov kernel $K$ from $X$ to a countable set $Y$, writing $pK(y) = \sum_x p(x) K(x)(y)$, one has $M_\alpha(pK\|qK) \le M_\alpha(p\|q)$ (this already holds for $\alpha \ge 1$), hence $D_\alpha(pK\|qK) \le D_\alpha(p\|q)$; in particular $D_\alpha(f_*p\|f_*q) \le D_\alpha(p\|q)$ for every map $f$.
3. (Adaptive composition) If $K, L$ are Markov kernels from $X$ to $Y$ with $D_\alpha(K(x)\|L(x)) \le B$ for every $x$ in the support of $p$, then the joint laws of $(x, y)$ with $x \sim p, y \sim K(x)$ and $x \sim q, y \sim L(x)$ satisfy $D_\alpha \le D_\alpha(p\|q) + B$.

## Proof sketch

The function $(u, v) \mapsto u (u/v)^{\alpha-1}$ is jointly convex and positively homogeneous on $[0,\infty)^2$ (weighted AM-GM), so it is subadditive. Summing over a kernel's fibers gives data processing for $M_\alpha$, and the trivial kernel to a point gives $M_\alpha(p\|q) \ge M_\alpha(1\|1) = 1$. For composition, the Renyi moment of the joint law factors as $\sum_x p(x)(p(x)/q(x))^{\alpha-1} M_\alpha(K(x)\|L(x))$, and each conditional moment is at most $e^{(\alpha-1)B}$.

## Depends on

- [Renyi divergence of discrete distributions](renyi-divergence.md)

## Sources

- I. Mironov, "Renyi Differential Privacy", IEEE 30th Computer Security Foundations Symposium (CSF), 2017.
- A. Renyi, "On Measures of Entropy and Information", Proceedings of the Fourth Berkeley Symposium on Mathematical Statistics and Probability, Vol. 1, University of California Press, 1961.
