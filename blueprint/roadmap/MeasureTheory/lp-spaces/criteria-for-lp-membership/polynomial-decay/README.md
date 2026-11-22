# Polynomial decay implies L^p membership

Let $E$ be a normed additive commutative group and $f : \mathbb{R} \to E$ almost everywhere strongly
measurable. If there are real numbers $C \ge 0$ and $q > 1$ with $\|f(x)\| \le C (1 + |x|)^{-q}$ for
almost every $x \in \mathbb{R}$, then $f$ lies in $L^p(\mathbb{R})$, for Lebesgue measure, for every
$p \in [1, \infty]$.

## Idea

For $1 \le p < \infty$, $\|f\|^p \le C^p (1 + |x|)^{-qp}$, which is integrable on $\mathbb{R}$ because
$qp > 1$; for $p = \infty$ the bound makes $f$ essentially bounded by $C$. The condition $q > 1$ is
what $p = 1$ needs: $(1 + |x|)^{-1}$ is not integrable. Measurability cannot be dropped: a
non-measurable function can satisfy the bound.

## Statements

- [Polynomial decay implies $L^p$ membership](mem-lp-of-polynomial-decay-ae.md)
- [Pointwise polynomial decay implies $L^p$ membership](mem-lp-of-polynomial-decay.md): the special case of a bound at every point.
