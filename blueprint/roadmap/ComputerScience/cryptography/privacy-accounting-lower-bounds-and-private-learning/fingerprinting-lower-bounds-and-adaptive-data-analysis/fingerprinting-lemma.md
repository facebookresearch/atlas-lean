# Fingerprinting lemma for estimating a random coin bias

Let $p$ be drawn uniformly from $[-1,1]$, let $x_1, \dots, x_n \in \{\pm 1\}$ be independent with $\mathbb{E}[x_i] = p$, and let $f : \{\pm1\}^n \to [-1,1]$ be any function. Then there are absolute constants $c, C > 0$ with

$$
\mathbb{E}_{p, x}\Big[ f(x)\sum_{i=1}^n (x_i - p) \Big] \ge c - C\,\mathbb{E}_{p,x}\big[|f(x) - p|\big].
$$

Thus any estimator of the bias that is accurate on average must be correlated with the samples: the total correlation $\sum_i \mathbb{E}[f(x)(x_i - p)]$ is bounded below by a constant. In a private algorithm each single correlation term is small, which yields lower bounds on $n$.

## Proof sketch

Write $g(p) = \mathbb{E}_x[f(x) \mid p]$; differentiating under the product measure gives $g'(p) = \frac{1}{1-p^2}\mathbb{E}_x\big[f(x)\sum_i (x_i - p) \mid p\big]$. Integrating by parts against the uniform prior (with the weight $1-p^2$ chosen so that boundary terms vanish) rewrites $\mathbb{E}[f(x)\sum_i (x_i - p)]$ as $\mathbb{E}[(1-p^2)g'(p)] = \mathbb{E}[2p\,g(p)]$, and an accurate $g(p) \approx p$ forces this to be a positive constant, with the error term controlled by $\mathbb{E}|f - p|$.

## Proof depends on

- [Tardos codes: optimal fully collusion-resilient fingerprinting](tardos-fingerprinting-code.md)

## Sources

- T. Steinke, J. Ullman, "Between Pure and Approximate Differential Privacy", Journal of Privacy and Confidentiality 7 (2017), arXiv:1501.06095.
- M. Bun, J. Ullman, S. Vadhan, "Fingerprinting Codes and the Price of Approximate Differential Privacy", STOC (2014); SIAM Journal on Computing 47 (2018), arXiv:1311.3158.
