# Lai-Robbins asymptotic lower bound

Let $\mathcal{E} = \mathcal{M}_1 \times \dots \times \mathcal{M}_k$ be a class of $k$-armed stochastic bandits
whose arm distributions have finite means. A policy is consistent over $\mathcal{E}$ if
$R_n(\nu) = o(n^p)$ for every $\nu \in \mathcal{E}$ and every $p > 0$. For $P \in \mathcal{M}_i$ and $\mu^*$
define $d_{\inf}(P, \mu^*, \mathcal{M}_i) = \inf\{\mathrm{KL}(P, P') : P' \in \mathcal{M}_i,\ \mu(P') > \mu^*\}$,
with $\inf \emptyset = \infty$. For every consistent policy, every $\nu \in \mathcal{E}$ and every
suboptimal arm $i$ (gap $\Delta_i > 0$),
$\liminf_{n \to \infty} \mathbb{E}[T_i(n)] / \log n \ge 1 / d_{\inf}(P_i, \mu^*, \mathcal{M}_i)$ (with $1/\infty = 0$
and $1/0 = \infty$), and hence
$\liminf_{n \to \infty} R_n / \log n \ge \sum_{i : \Delta_i > 0} \Delta_i / d_{\inf}(P_i, \mu^*, \mathcal{M}_i)$.
For the class of Gaussian arms with unit variance, $d_{\inf} = \Delta_i^2/2$ and the bound becomes
$\sum_{i : \Delta_i > 0} 2/\Delta_i$.

## Expansion

This node states a precise result. A good expansion adds a page for the pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: relative entropy (Kullback–Leibler divergence) of probability measures on a general measurable space, with values in $[0, \infty]$.

## Depends on

- [Stochastic k-armed bandits: canonical history law and regret](stochastic-k-armed-bandits-canonical-history-law-and-regret.md)

## Proof depends on

- [Divergence decomposition for stochastic bandits](divergence-decomposition-for-stochastic-bandits.md)

## Sources

- T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020 (author copy), Definition 16.1 (consistency), the definition of $d_{\inf}$ and Theorem 16.2, whose proof establishes the bound on $\mathbb{E}[T_i(n)]$; Section 16.1 also treats the unit-variance Gaussian class. <https://tor-lattimore.com/downloads/book/book.pdf>
