# Fingerprinting lemma for estimating a random coin bias

Let $p$ be drawn uniformly from $[-1,1]$ and, conditionally on $p$, let $x_1, \dots, x_n \in \{\pm 1\}$ be independent with conditional means $\mathbb{E}[x_i \mid p] = p$. Let $f : \{\pm1\}^n \to [-1,1]$ be any function. Then

$$
\mathbb{E}_{p, x}\Big[ f(x)\sum_{i=1}^n (x_i - p) \Big] \ge \frac{2}{3} - 2\,\mathbb{E}_{p,x}\big[|f(x) - p|\big].
$$

Thus any estimator of the bias that is accurate on average must be correlated with the samples: the total correlation $\sum_i \mathbb{E}[f(x)(x_i - p)]$ is bounded below by a constant. In a private algorithm each single correlation term is small, which yields lower bounds on $n$.

## Proof sketch

The proof is analytic and uses no fingerprinting code. Write $g(p) = \mathbb{E}[f(x) \mid p]$, a polynomial in $p$. For a $\pm1$ variable with mean $p$, $(1-p^2)\frac{d}{dp}\Pr[x = b] = (b - p)\Pr[x = b]$ for $b = \pm 1$, so differentiating the product measure gives the identity $(1-p^2)\,g'(p) = \mathbb{E}\big[f(x)\sum_i (x_i - p) \mid p\big]$. Integrating by parts against the uniform density $1/2$ on $[-1,1]$, the boundary terms vanish because of the weight $1 - p^2$, and $\mathbb{E}\big[f(x)\sum_i (x_i - p)\big] = \mathbb{E}[(1-p^2)g'(p)] = \mathbb{E}[2p\,g(p)]$. Finally $\mathbb{E}[2p\,g(p)] = \mathbb{E}[2p^2] + \mathbb{E}[2p(g(p) - p)] \ge 2/3 - 2\,\mathbb{E}|g(p) - p| \ge 2/3 - 2\,\mathbb{E}|f(x) - p|$, using $|p| \le 1$ and Jensen's inequality.

## Sources

- C. Dwork, A. Smith, T. Steinke, J. Ullman, S. Vadhan, "Robust Traceability from Trace Amounts", FOCS (2015).
- T. Steinke, J. Ullman, "Interactive Fingerprinting Codes and the Hardness of Preventing False Discovery", COLT (2015), arXiv:1410.1228, Lemma 2.11.
- T. Steinke, J. Ullman, "Tight Lower Bounds for Differentially Private Selection", FOCS (2017), arXiv:1704.03024, Section 3.2.1 (Lemmas 9 and 10).
