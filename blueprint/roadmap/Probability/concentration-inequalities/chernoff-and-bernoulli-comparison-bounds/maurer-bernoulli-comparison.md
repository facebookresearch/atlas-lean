# Maurer's comparison of bounded i.i.d. means with Bernoulli means

Let $\varphi : [0,1] \to [0, \infty)$ be convex, let $n \ge 1$, and let $X_1, \dots, X_n$ be i.i.d. random variables with values in $[0,1]$ and mean $p$. Then

$$
\mathbb{E}\Big[\varphi\Big(\frac{X_1 + \dots + X_n}{n}\Big)\Big] \le \sum_{k=0}^{n} \binom{n}{k} p^k (1-p)^{n-k}\, \varphi\Big(\frac{k}{n}\Big),
$$

that is, the expectation is at most the same expectation for $n$ independent Bernoulli($p$) trials. Pointwise, for every $x \in [0,1]^n$, $\varphi(\frac1n \sum_i x_i) \le \sum_{T \subseteq [n]} \prod_{i \in T} x_i \prod_{i \notin T}(1 - x_i)\, \varphi(|T|/n)$.

## Proof sketch

A point $x$ of the cube is the convex combination of the vertices $\mathbf 1_T$ with weights $\prod_{i\in T} x_i \prod_{i \notin T}(1-x_i)$, whose barycenter is $x$; Jensen's inequality applied to the convex function $y \mapsto \varphi(\frac1n\sum_i y_i)$ gives the pointwise bound. Taking expectations, independence turns the expected weight of each vertex $T$ into $p^{|T|}(1-p)^{n-|T|}$, and grouping vertices by $|T| = k$ produces the binomial sum.

## Sources

- A. Maurer, "A Note on the PAC Bayesian Theorem", arXiv preprint cs/0411099, 2004.
