# Multicalibration by iterated level-set corrections terminates quickly

Let $D$ be a distribution over $X \times \{0,1\}$ with Bayes predictor $p^*(x) = \mathbb{E}[y \mid x]$, let $p : X \to [0,1]$ be a predictor, and let $\mathcal{C}$ be a collection of functions $c : X \to [-1,1]$ (indicators of subpopulations being the main example). Fix $\alpha \in (0,1]$ and a discretization width $\lambda \le \alpha^2/4$. Start from any predictor with values in the grid $\lambda\mathbb{Z} \cap [0,1]$; while some $c \in \mathcal{C}$ has $\sum_v \big|\mathbb{E}[c(x)(y-v)\mathbf{1}[p(x)=v]]\big| > \alpha$, set $p(x) \leftarrow p(x) + \alpha\,\sigma_{p(x)}\,c(x)$ simultaneously on every level set, where $\sigma_v$ is the sign of $\mathbb{E}[c(x)(y-v)\mathbf{1}[p(x)=v]]$, then clip to $[0,1]$ and round to the nearest grid value. This process terminates after at most $2/\alpha^2$ corrections and outputs a predictor that is $\alpha$-multicalibrated with respect to $\mathcal{C}$. Each step needs one call to an auditor that finds a violating $c$, which can be implemented with polynomially many samples (in $1/\alpha$, $1/\lambda$ and $\log|\mathcal{C}|$ for finite $\mathcal{C}$) and, for structured $\mathcal{C}$, with a weak agnostic learner for $\mathcal{C}$.

## Proof sketch

By the potential lemma the update decreases $\mathbb{E}[(p - p^*)^2] \le 1$ by at least $2\alpha \cdot \alpha - \alpha^2 = \alpha^2$, clipping does not increase it, and rounding increases it by at most $\lambda + \lambda^2/4 \le \alpha^2/2$, so each correction gains at least $\alpha^2/2$. When no violation exceeds $\alpha$ the predictor is multicalibrated by definition. Empirical auditing uses fresh samples per round and uniform convergence over $\mathcal{C}$ restricted to the level sets.

## Depends on

- [Multicalibrated predictors](multicalibrated-predictor.md)

## Proof depends on

- [Each multiaccuracy correction decreases the squared distance to the Bayes predictor](multiaccuracy-correction-potential-decrease.md)
- [Uniform convergence implies ERM is an agnostic PAC learner](../pac-learning/agnostic-pac-learning-and-uniform-convergence/uniform-convergence-implies-erm-is-an-agnostic-pac-learner.md)

## Sources

- U. Hebert-Johnson, M. P. Kim, O. Reingold, G. N. Rothblum, "Multicalibration: Calibration for the (Computationally-Identifiable) Masses", ICML (2018), arXiv:1711.08513, Algorithm 3.2, Lemma 3.6 and Theorem 3.7 (for sets of measure at least $\gamma$ and relative errors on level sets; the version above uses the summed $\ell_1$ form of the condition).
- P. Gopalan, A. T. Kalai, O. Reingold, V. Sharan, U. Wieder, "Omnipredictors", ITCS (2022), arXiv:2109.05389, Definition 5.3 and Theorem 9.2.
