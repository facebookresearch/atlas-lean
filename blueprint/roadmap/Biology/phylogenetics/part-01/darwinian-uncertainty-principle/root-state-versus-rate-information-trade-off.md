# Root-state versus rate information trade-off

**Setting.** Let $T$ be a rooted phylogenetic tree with $n$ leaves and positive edge lengths (times). A single discrete character with states $\{1, \dots, k\}$ evolves along $T$ under the **equal input model**: from any state the process jumps to state $j$ at rate $\lambda\pi_j$, where $\pi$ is the equilibrium distribution; equivalently, *resampling events* occur at rate $\lambda$ along every edge, and at each event the state is redrawn from $\pi$ independently of its current value. The root state $\rho$ is drawn from $\pi$; $X$ denotes the leaf states. Given $\pi$, the global rate of actual state changes is $\lambda\big(1 - \sum_i \pi_i^2\big)$; treating $\pi$ as random, let $r = \lambda\,\mathbb{E}\big[1 - \sum_i\pi_i^2\big]$ be the expected global transition rate, proportional to $\lambda$. Write $I_\rho(r) = I(\rho; X)$ and $I_\pi(r) = I(\pi; X)$ for the mutual information that the leaf data carry about the root state and about the equilibrium frequencies.

**Theorem 1.** For every tree and every number of leaves:
1. $I_\rho(r)$ is monotone decreasing in $r$, with $I_\rho(r) \to 0$ as $r \to \infty$;
2. $I_\pi(r)$ is bounded above by a monotone increasing function $J(r)$ that agrees with $I_\pi$ at $r = 0$ and in the limit $r \to \infty$, where it equals the information about $\pi$ in $n$ independent draws from $\pi$ (a tree with infinitely long edges).

Hence the rates most favourable for reconstructing the root are least favourable for learning the process, and conversely: no single rate makes both estimation tasks accurate.

**Theorem 2.** For any continuous-time Markov model with strictly positive off-diagonal rates, on Yule trees of fixed height whose number of leaves tends to infinity, both the root state and the full rate matrix can be estimated with error tending to zero. On star trees and on Kingman coalescent trees this fails: the root-state error stays bounded away from zero however many leaves are sampled.

## Depends on

- [Pupko's algorithm computes the joint maximum-likelihood reconstruction](../../maximum-likelihood-ancestral-reconstruction/pupko-is-joint-ml.md)

## Expansion

Both parts of Theorem 1 use the data-processing inequality: if $U \to V \to W$ is a Markov chain then $I(U; W) \le I(U; V)$. For the root, letting edge rates vary individually, raising the rate on one edge is equivalent (by coupling) to inserting extra resampling, which garbles the signal passing through that edge, so $I(\rho; X)$ cannot increase. For $\pi$, consider the unobservable richer record of all resampling events and states on the tree; its information about $\pi$ dominates $I(\pi; X)$, and with more resampling events the record contains more independent draws from $\pi$, so this bound $J(r)$ increases with $r$. On a Yule tree of fixed height the many short pendant subtrees near the tips carry fresh information about the rates, and maximum parsimony recovers the root because early branching is dense: each off-diagonal rate $q_{ij}$ can be consistently estimated by a ratio built from the numbers of typical three-leaf pendant subtrees showing state patterns $(i, i, j)$ and $(i,\cdot,\cdot)$ and the total heights of their cherries, using the known distribution of numbers and heights of such subtrees in a Yule tree. On a star tree, switching the root state can be exactly compensated by changing $\pi$ and $\lambda$ (non-identifiability), and on a coalescent tree the shorter root edge has an exponential length that does not shrink with $n$, so the root signal saturates.

## Sources

- O. Gascuel and M. Steel, "A Darwinian uncertainty principle", Systematic Biology 69 (2020), 521–529, Mathematical Results and Appendix (Theorems 1–2 with proof sketches), <https://doi.org/10.1093/sysbio/syz054>, PMCID: PMC7188465.
- O. Gascuel and M. Steel, "Inferring ancestral sequences in taxon-rich phylogenies", Mathematical Biosciences 227 (2010), 125–135.
