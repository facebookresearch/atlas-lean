# Each multiaccuracy correction decreases the squared distance to the Bayes predictor

Let $D$ be a distribution over $X \times \{0,1\}$ with Bayes predictor $p^*(x) = \mathbb{E}[y \mid x]$, let $p : X \to [0,1]$ be a predictor, and let $\mathcal{C}$ be a collection of functions $c : X \to [-1,1]$ (indicators of subpopulations being the main example). Suppose $\mathbb{E}[c(x)(y - p(x))] \ge \alpha > 0$ for some $c \in \mathcal{C}$, and let $p'(x) = \Pi_{[0,1]}\big(p(x) + \alpha c(x)\big)$, where $\Pi_{[0,1]}$ is projection onto $[0,1]$. Then

$$
\mathbb{E}\big[(p'(x) - p^*(x))^2\big] \le \mathbb{E}\big[(p(x) - p^*(x))^2\big] - \alpha^2 .
$$

The same holds on a single level set $\{p = v\}$ with $\mathbb{E}[c(x)(y-v)\mathbf{1}[p(x)=v]] \ge \alpha$, where the update is applied on that level set only.

## Proof sketch

Since $\mathbb{E}[c(x)(y - p(x))] = \mathbb{E}[c(x)(p^*(x) - p(x))]$, expanding the square gives $\mathbb{E}[(p + \alpha c - p^*)^2] = \mathbb{E}[(p - p^*)^2] - 2\alpha\mathbb{E}[c(p^* - p)] + \alpha^2\mathbb{E}[c^2] \le \mathbb{E}[(p-p^*)^2] - 2\alpha^2 + \alpha^2$. Projection onto $[0,1]$ only moves values closer to $p^*(x) \in [0,1]$.

## Depends on

- [Multiaccurate predictors](multiaccurate-predictor.md)

## Sources

- U. Hebert-Johnson, M. P. Kim, O. Reingold, G. N. Rothblum, "Multicalibration: Calibration for the (Computationally-Identifiable) Masses", ICML (2018), arXiv:1711.08513, Lemma 3.2.
- M. P. Kim, A. Ghorbani, J. Zou, "Multiaccuracy: Black-Box Post-Processing for Fairness in Classification", AIES (2019), arXiv:1805.12317.
