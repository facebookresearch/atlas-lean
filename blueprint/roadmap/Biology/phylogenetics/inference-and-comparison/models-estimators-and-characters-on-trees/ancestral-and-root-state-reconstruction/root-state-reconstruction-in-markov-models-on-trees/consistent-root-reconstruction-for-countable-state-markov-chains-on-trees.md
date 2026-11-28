# Consistent root-state reconstruction for countable-state Markov models on trees

Let $\{T^k\}_{k\ge1}$ be a nested sequence of rooted trees with edge lengths and common root $\rho$, where $T^k$ has $k$ leaves $\partial T^k$ and is obtained from $T^{k-1}$ by adding a leaf edge. Along the branches a stable, conservative continuous-time Markov chain with countable state space $\mathcal{S}$ and transition matrices $(\mathbf{P}_t)_{t\ge0}$ evolves, started at the root from a distribution $\pi$; the leaf states $X_{\partial T^k}$ are observed. Assume

1. (bounded height) $h^* = \sup_k \max_{x\in\partial T^k}\ell_x < \infty$, where $\ell_x$ is the root-to-$x$ distance;
2. (initial-state identifiability) for every $t\ge0$ the rows of $\mathbf{P}_t$ are pairwise distinct (true, for example, for reversible chains and for uniform chains, including all finite-state chains).

A sequence of estimators $F_k:\mathcal{S}^{\partial T^k}\to\mathcal{S}$ is **consistent** if $\mathbb{P}^\pi[F_k(X_{\partial T^k}) = X_\rho]\to1$. Let $T^k(s)$ be $T^k$ truncated at distance $s$ from the root; the trees satisfy the **big bang condition** if $|\partial T^k(s)|\to\infty$ as $k\to\infty$ for every $s>0$. Let $\mathcal{D}_i=\{j: p_{ij}(t)>0 \text{ for some } t>0\}$ be the set of states reachable from $i$.

**Theorem.** A consistent sequence of root estimators exists if and only if at least one of the following holds:

- (a) *downstream disjointness*: $\mathcal{D}_i\cap\mathcal{D}_j=\emptyset$ for all $i\ne j$ with $\pi(i)\wedge\pi(j)>0$;
- (b) the trees satisfy the big bang condition.

If neither holds, there is $\epsilon>0$ with $\sup_{F_k}\mathbb{P}^\pi[F_k(X_{\partial T^k})=X_\rho]\le1-\epsilon$ for every $k$.

**Quantitative bound.** Under the big bang condition, for every $\epsilon>0$ and $k$ there is an estimator $F_k$ such that, for all $s>0$,

$$\mathbb{P}^\pi\bigl[F_k(X_{\partial T^k})\ne X_\rho\bigr] < \epsilon + C_0\,\Delta_\epsilon^{-2}\,q^*_\epsilon\,s + n_\epsilon\exp\bigl(-C_1\,\Delta_\epsilon^2\,|\partial T^k(s)|\bigr),$$

where $C_0,C_1$ are universal constants, $n_\epsilon$ is the number of root states carrying all but $\epsilon$ of the mass of $\pi$, $q^*_\epsilon$ bounds their jump rates, and $\Delta_\epsilon$ is a total-variation separation of the corresponding rows of $\mathbf{P}_{h^*}$. Optimizing over $s$ trades off mutations near the root against the number of nearly independent lineages.

This answers a question of Gascuel and Steel and applies to ancestral sequence reconstruction under the TKF91 insertion-deletion model.

## Expansion

1. Sufficiency of (a): each leaf state lies in exactly one reachable set $\mathcal{D}_i$ with $\pi(i)>0$, so a single leaf identifies the root.
2. Sufficiency of (b): pick one leaf below each of the $|\partial T^k(s)|$ lineages present at depth $s$; with probability at least $1-O(q^* s)$ no mutation happens above depth $s$, and the leaves are then independent draws from the row $\mathbf{P}_{t}(X_\rho,\cdot)$ with distinct means, so a majority or likelihood test concentrates exponentially in the number of lineages.
3. Necessity: without the big bang condition, finitely many lineages pass some depth $s>0$; conditioning on their states at depth $s$ leaves a nondegenerate posterior on the root unless the reachable sets separate the root states.

## Sources

- W.-T. L. Fan, S. Roch, *Necessary and sufficient conditions for consistent root reconstruction in Markov models on trees*, arXiv:1707.05702 (Theorem 1, Theorem 2 and Proposition 1). <https://doi.org/10.48550/arXiv.1707.05702> Published version: Electronic Journal of Probability, Vol. 23 (47), 1-24, 2018.
