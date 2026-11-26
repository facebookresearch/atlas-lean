# Multicalibration by iterated level-set corrections terminates quickly

Let $D$ be a distribution over $X \times \{0,1\}$ with Bayes predictor $p^*(x) = \mathbb{E}[y \mid x]$, let $p : X \to [0,1]$ be a predictor, and let $\mathcal{C}$ be a collection of functions $c : X \to [-1,1]$ (indicators of subpopulations being the main example). Fix $\alpha > 0$ and a discretization width $\lambda \le \alpha$. Start from any predictor with values in the grid $\lambda\mathbb{Z} \cap [0,1]$; while some $c \in \mathcal{C}$ and level $v$ violate the multicalibration condition on $\{p = v\}$ by more than $\alpha$ (in the per-level sense), apply the corresponding correction and round the corrected values back to the grid. This process terminates after $O(1/\alpha^2)$ corrections (for $\lambda$ a small constant fraction of $\alpha$), and outputs a predictor that is $O(\alpha)$-multicalibrated with respect to $\mathcal{C}$. Each step needs one call to an auditor that finds a violating $c$, which can be implemented with polynomially many samples (in $1/\alpha$, $1/\lambda$ and $\log|\mathcal{C}|$ for finite $\mathcal{C}$) and, for structured $\mathcal{C}$, with a weak agnostic learner for $\mathcal{C}$.

## Proof sketch

By the potential lemma each correction decreases $\mathbb{E}[(p - p^*)^2] \le 1$ by an amount of order $\alpha^2$ (the rounding to the grid costs at most a constant fraction of this when $\lambda$ is small compared with the violation), so the number of corrections is bounded. When no violation exceeds $\alpha$ the predictor is multicalibrated by definition. Empirical auditing uses fresh samples per round and uniform convergence over $\mathcal{C}$ restricted to the level sets.

## Depends on

- [Multicalibrated predictors](multicalibrated-predictor.md)

## Proof depends on

- [Each multiaccuracy correction decreases the squared distance to the Bayes predictor](multiaccuracy-correction-potential-decrease.md)
- [Uniform convergence implies ERM is an agnostic PAC learner](../pac-learning/agnostic-pac-learning-and-uniform-convergence/uniform-convergence-implies-erm-is-an-agnostic-pac-learner.md)

## Sources

- U. Hebert-Johnson, M. P. Kim, O. Reingold, G. N. Rothblum, "Multicalibration: Calibration for the (Computationally-Identifiable) Masses", ICML (2018), arXiv:1711.08513.
