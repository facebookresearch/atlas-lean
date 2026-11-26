# Stability of randomly switching asymptotically linear reaction networks

**Setting.** Fix $n$ stochastic reaction networks $X^1, \dots, X^n$ on $d$ species with rate functions $\lambda_{i, y \to y'}$, and $d \times d$ matrices $M_i$ such that the mean drift is asymptotically linear:

$$\sum_{y \to y' \in \mathcal{R}_i} \lambda_{i, y\to y'}(x)\,(y'_m - y_m) = (M_i x)_m + o(\|x\|_{\ell^1}), \qquad x \in \mathbb{Z}^d_{\ge 0}.$$

Let $Q$ be the generator of an irreducible Markov chain on $\{1,\dots,n\}$ with stationary law $w$, set $M = \sum_i w_i M_i$, and for $\kappa > 0$ let $Z_\kappa$ be the Markov chain on $\mathbb{Z}^d_{\ge 0} \times \{1,\dots,n\}$ whose environment switches according to $\kappa Q$ and whose species counts evolve as $X^i$ while the environment is $i$.

**Theorem (fast switching, recurrence).** If some $v \in \mathbb{R}^d_{>0}$ satisfies $vM \in \mathbb{R}^d_{<0}$, then for all sufficiently large $\kappa$ the chain $Z_\kappa$ is exponentially ergodic.

**Theorem (slow switching, recurrence).** If for each $i$ some $v^i \in \mathbb{R}^d_{>0}$ satisfies $v^i M_i \in \mathbb{R}^d_{<0}$, then for all sufficiently small $\kappa$ the chain $Z_\kappa$ is exponentially ergodic.

**Theorem (fast switching, transience).** Suppose each $X^i$ has mass-action kinetics and at most monomolecular reactions. If some $v \in \mathbb{R}^d_{\ge 0}$ satisfies $(vM)_m > 0$ for every $m \in \operatorname{supp}(v)$, then for all sufficiently large $\kappa$ every state is evanescent ($\|Z_\kappa(t)\|_{\ell^1} \to \infty$ with positive probability).

**Single network.** Taking $n = 1$: a network with drift matrix $M$ and a positive $v$ with $vM < 0$ componentwise is exponentially ergodic.

The averaged matrix $M$ and the individual $M_i$ can disagree: two evanescent networks can switch into an exponentially ergodic one at high switching rate, and two ergodic ones into an evanescent one.

## Depends on

- [Non-explosivity of complex-balanced stochastic reaction networks](non-explosivity-of-complex-balanced-stochastic-reaction-networks.md)

## Expansion

The Lyapunov function is linear, $V(x,i) = v\cdot x$ plus a bounded environment correction solving a Poisson equation for $\kappa Q$. Under fast switching the drift seen by $V$ is the stationary average $vMx$, so a negative linear drift gives a Foster-Lyapunov condition and exponential ergodicity. Under slow switching each environment lasts long enough to contract on its own, so separate $v^i$ suffice. Transience uses the same linear functional with positive drift on the support of $v$; monomolecular mass-action rates make the drift exactly linear, which controls the fluctuations needed to escape to infinity.

## Sources

- D. Cappelletti, A. Howells, C. Xu, "Stability of randomly switching stochastic reaction networks with asymptotically linear transition rates" (2025), Setting SAL, Theorems 4, 8, 10, 16 and Corollaries 9, 19-20, Propositions 22 and 26, <https://doi.org/10.48550/arXiv.2507.09421>.
