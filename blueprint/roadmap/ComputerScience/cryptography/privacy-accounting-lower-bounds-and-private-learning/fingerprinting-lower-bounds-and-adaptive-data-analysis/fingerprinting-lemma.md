# Fingerprinting lemma for estimating a random coin bias

Let $f : \{\pm 1\}^n \to [-1, 1]$ be any function. Suppose $p$ is drawn uniformly from $[-1, 1]$ and, conditionally on $p$, $c = (c_1, \dots, c_n) \in \{\pm 1\}^n$ is a vector of $n$ independent bits, each with expectation $p$. Writing $\bar{c} = \frac{1}{n} \sum_{i=1}^n c_i$ for the coordinate-wise mean of $c$,

$$
\mathbb{E}_{p, c}\Big[ f(c) \sum_{i=1}^n (c_i - p) + 2\,\lvert f(c) - \bar{c} \rvert \Big] \ge \frac{1}{3}.
$$

In the same setting the squared-error form also holds:

$$
\mathbb{E}_{p, c}\Big[ \big(f(c) - p\big) \sum_{i=1}^n (c_i - p) \Big] \ge \frac{1}{3} - \mathbb{E}_{p, c}\big[ (f(c) - p)^2 \big].
$$

Thus any estimator of the bias that is accurate on average must be correlated with the samples: the total correlation $\sum_i \mathbb{E}[f(c)(c_i - p)]$ is bounded below by a constant. In a private algorithm each single correlation term is small, which yields lower bounds on $n$.

## Proof sketch

The proof is analytic and uses no fingerprinting code. Write $g(p) = \mathbb{E}[f(c) \mid p]$, a polynomial in $p$. For a $\pm1$ variable with mean $p$, $(1-p^2)\frac{d}{dp}\Pr[c_i = b] = (b - p)\Pr[c_i = b]$ for $b = \pm 1$, so differentiating the product measure gives the identity $(1-p^2)\,g'(p) = \mathbb{E}\big[f(c)\sum_i (c_i - p) \mid p\big]$ (Steinke and Ullman's Lemma 9, rescaled from bits in $\{0, 1\}$ to $\{\pm 1\}$). Integrating by parts against the uniform density $1/2$ on $[-1,1]$, the boundary terms vanish because of the weight $1 - p^2$, and $\mathbb{E}\big[f(c)\sum_i (c_i - p)\big] = \mathbb{E}[(1-p^2)g'(p)] = \mathbb{E}[2p\,g(p)] = \mathbb{E}[2p\,f(c)]$ (their Lemma 10 with $\alpha = \beta = 1$, rescaled). For the first form, $\mathbb{E}[2p\,\bar{c}] = \mathbb{E}[2p^2] = 2/3$ and $\lvert 2p \rvert \le 2$, so $\mathbb{E}[2p\,f(c)] \ge 2/3 - 2\,\mathbb{E}\lvert f(c) - \bar{c} \rvert$, which gives the bound $2/3 \ge 1/3$. For the second form, $\mathbb{E}[p \sum_i (c_i - p)] = 0$, and $2p\,f(c) = f(c)^2 + p^2 - (f(c) - p)^2 \ge p^2 - (f(c) - p)^2$ with $\mathbb{E}[p^2] = 1/3$.

## Sources

- M. Bun, T. Steinke, J. Ullman, "Make Up Your Mind: The Price of Online Queries in Differential Privacy", SODA (2017), arXiv:1604.04618, Section 3.2, Lemma 3.6 (the first form).
- G. Kamath, J. Ullman, "A Primer on Private Statistics", arXiv:2005.00010, Lemma 3.7 (the squared-error form, credited to Bun, Steinke and Ullman).
- T. Steinke, J. Ullman, "Tight Lower Bounds for Differentially Private Selection", FOCS (2017), arXiv:1704.03024, Section 3.2.1 (Lemmas 9 and 10: the identity in the $\{0, 1\}$ parametrization).
- C. Dwork, A. Smith, T. Steinke, J. Ullman, S. Vadhan, "Robust Traceability from Trace Amounts", FOCS (2015).
