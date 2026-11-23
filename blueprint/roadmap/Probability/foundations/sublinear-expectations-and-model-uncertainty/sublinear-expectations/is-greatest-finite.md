# Representation on a finite scenario set

Let $\Omega$ be a finite set and let $\mathbb{E}$ be a [sublinear
expectation](is-sublinear-expectation.md) on the space of all functions $\Omega \to \mathbb{R}$.
Let $Q$ be the set of probability vectors $q$ on $\Omega$ ($q \ge 0$, $\sum_\omega q(\omega) = 1$)
with $\sum_\omega q(\omega) Y(\omega) \le \mathbb{E}[Y]$ for every $Y$. Then for every
$X : \Omega \to \mathbb{R}$,

$$\mathbb{E}[X] = \max_{q \in Q} \sum_{\omega} q(\omega)\, X(\omega),$$

the maximum being attained. This is the finite case of Theorem 2.1 of Chapter I of the source,
which the Notes to Chapter I attribute to Huber (*Robust Statistics*, 1981).

## Background

- [Representation of a sublinear expectation as a maximum of linear expectations](is-greatest.md):
  the general statement, of which this is the case $\mathcal{H} = \mathbb{R}^\Omega$ with $\Omega$
  finite, where every linear expectation is a probability vector.

## Sources

- S. Peng, *Nonlinear Expectations and Stochastic Calculus under Uncertainty*,
  arXiv:1002.4546v1, 2010, Chapter I, Theorem 2.1.
- P. J. Huber, *Robust Statistics*, Wiley, 1981.
