# No class with three concepts is learnable faster than exponentially

Let $H \subseteq \{0,1\}^X$ contain at least three concepts. Then $H$ is not learnable faster than $e^{-n}$: for every learner there are a realizable $P$ and constants $C, c > 0$ such that $\mathbb{E}[\mathrm{er}_P(\hat h_n)] \ge C e^{-cn}$ for infinitely many $n$.

## Proof sketch

Three distinct concepts give two concepts $h_0 \ne h_1$ and a point $x_0$ where they agree together with a point $x_1$ where they disagree, or a symmetric configuration. Put mass $1 - p$ on a point where the two candidate targets agree and mass $p$ on a point where they disagree; with probability $(1-p)^n$ the sample never shows the disagreement point, and then the learner errs with probability at least one half under one of the two targets. Choosing the worse target gives error at least $\tfrac{p}{2}(1-p)^n$ for infinitely many $n$.

## Depends on

- [Realizable distributions, learning curves and universal rates](universal-rate.md)

## Sources

- O. Bousquet, S. Hanneke, S. Moran, R. van Handel, A. Yehudayoff, "A Theory of Universal Learning", STOC (2021), arXiv:2011.04483.
