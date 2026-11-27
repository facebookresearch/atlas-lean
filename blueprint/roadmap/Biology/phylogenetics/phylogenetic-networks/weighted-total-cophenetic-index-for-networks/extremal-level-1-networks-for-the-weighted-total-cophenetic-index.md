# Extremal level-1 networks for the weighted total cophenetic index

**Setting.** $\Phi^{**}$ is the weighted total cophenetic index of a rooted phylogenetic network (vertex weights $\phi(v) = 1$, or $\epsilon + \sum \omega(B)$ at roots of non-trivial blocks, with $0 \le \epsilon \le 2$). Let $\mathcal{BN}_n$ be the binary level-1 networks on $n$ leaves and $\mathcal{N}^{\le 2}_n$ the level-1 networks whose vertices have in-degree at most 2, so $\mathcal{BN}_n \subseteq \mathcal{N}^{\le 2}_n$.

**Theorem.**
1. *(Minimum over all level-1 networks.)* For $n \ge 2$, a level-1 network $N$ minimizes $\Phi^{**}$ among level-1 networks on $n$ leaves iff $\Phi^{**}(N) = \binom{n}{2}$. If $\epsilon > 0$, the unique minimizer is the star tree; if $\epsilon = 0$ it is the star tree or the network obtained from it by placing the root on a triangle.
2. *(Minimum over binary level-1 networks.)* For $N \in \mathcal{BN}_n$, $n \ge 2$,

$$\Phi^{**}(N) \ge \sum_{k=1}^{n-1} a(k) + \binom{n}{2},$$

where $a(k)$ is the exponent of the highest power of $2$ dividing $k!$. Equality holds exactly for networks obtained from a maximally balanced tree by expanding inner vertices into triangles; if $\epsilon > 0$, the minimizer is a maximally balanced tree.
3. *(Maximum.)* For $N \in \mathcal{BN}_n$ (resp. $\mathcal{N}^{\le 2}_n$) with $n \ge 3$,

$$\Phi^{**}(N) \le \left(\binom{n+1}{3} + \epsilon\right)\binom{n}{2},$$

with equality iff $N$ is the network $N^{\mathrm{cres}}_n$ consisting of a single crescent block on $n + 1$ vertices with the $n$ leaves attached.

## Depends on

- [Weighted total cophenetic index of a phylogenetic network](weighted-total-cophenetic-index-of-a-phylogenetic-network.md)

## Expansion

Every network has $\phi(\rho_N) \ge 1$, giving $\Phi^{**} \ge \binom{n}{2}$ with equality only when no non-root relevant vertex contributes, i.e. the star (or its triangle-rooted twin when the triangle weight $\epsilon + 1$ cannot be told apart). Among binary networks, the recursion $\Phi^{**}(N) = \sum_i \Phi^{**}(\partial N(v_i)) + \phi(\rho_N)\binom{n}{2}$ reduces minimization to the tree case, where the total cophenetic index is minimized by maximally balanced trees with value $\sum_{k<n} a(k)$. For the maximum, the root carries a block of maximal weight $\binom{n+1}{3}$, which is a crescent, and it multiplies the largest possible binomial $\binom{n}{2}$, mirroring the caterpillar as the most imbalanced tree.

## Sources

- Linda Knüver, Mareike Fischer, Marc Hellmuth and Kristina Wicke, "The weighted total cophenetic index: A novel balance index for phylogenetic networks", Discrete Applied Mathematics 359 (2024), 89–142, <https://doi.org/10.1016/j.dam.2024.07.037>; numbering as in arXiv:2307.08654: Theorems 12.3, 12.13 and 12.17.
