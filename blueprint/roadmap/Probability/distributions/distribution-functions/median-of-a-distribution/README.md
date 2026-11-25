# Median of a distribution

Let $\nu$ be a measure on $\mathbb{R}$, typically a probability measure. A real number $m$ is a median of $\nu$ when $\nu((-\infty, m]) \ge 1/2$ and $\nu([m, \infty)) \ge 1/2$, where a set of infinite measure counts as having measure $0$ in these inequalities.

## Idea

A median splits the mass in half: at least half lies on each side of $m$, with $m$ itself counted on both sides. A probability measure always has a median, but it need not be unique: for a fair coin on $\{0, 1\}$, every $m \in [0, 1]$ is a median. Unlike the mean, the median needs no integrability and is insensitive to extreme values. Its main property is optimality: a median $m$ of a probability measure $\nu$ with a finite mean minimises $y \mapsto \int |\theta - y| \, d\nu(\theta)$, so it is the best constant prediction under absolute loss, as the mean is under squared loss. These absolute deviations are integrable exactly when $\nu$ has a mean.

## Statements

- [Median of a measure on the real line](is-median.md)
- [A median minimizes the expected absolute loss](integral-abs-sub-le-of-is-median.md): a median minimises expected absolute loss
- [Absolute deviations are integrable exactly when the mean exists](integrable-abs-sub-iff.md): lemma used for the minimisation property
- [Absolute-deviation minimizers of a sample are the median interval](sample-median-interval-minimizes-absolute-deviation.md)
