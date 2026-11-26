# Dynamic Θ-random graph and the Λ-coalescent with momentum

**Θ-dynamic random graph.** Let $\Theta$ be a finite nonnegative measure on $[0,1]\times(0,1]$, $\theta = \int_{\{0\}\times[0,1]}q\,\Theta(du,dq)$, and $N$ a Poisson point process on $[0,\infty)\times(0,1]^2$ with intensity $dt\,\Theta(du,dq)\,u^{-2}\mathbf{1}_{u>0}$. The Θ-dynamic random graph $G^n = (G^n_t)_{t\ge0}$ on vertices $[n] = \{1,\dots,n\}$ starts with no edges and, at each atom $(t,u,q)$ of $N$, performs a $(u,q)$-merger: each vertex is colored independently with probability $u$, and each pair of colored vertices not already adjacent is joined independently with probability $q$. In addition, each non-adjacent pair is joined at rate $\theta$.

**Coalescent with momentum.** The Θ-coalescent with momentum $\Pi^n = (\Pi^n_t)_{t\ge0}$ is the partition of $[n]$ into the vertex sets of the connected components of $G^n_t$. Its block size spectrum up to order $d$ is

$$\mathtt{C}^n_t = (\mathtt{C}^n_{t,1},\dots,\mathtt{C}^n_{t,d}),\qquad \mathtt{C}^n_{t,i} = \big|\{A \in \Pi^n_t : |A| = i\}\big|.$$

**Properties.**
- The graph processes $(G^n)_n$ are exchangeable and consistent (restricting $G^{n+1}$ to $[n]$ gives $G^n$ in law), so they couple naturally across $n$.
- $\Pi^n$ is exchangeable but not consistent, so it does not extend to a partition process of $\mathbb{N}$.
- Mergers are size-biased: for $\Theta = \Lambda\times\delta_1$, a $u$-merger involves a block $A$ when any of its vertices is colored, which has probability $1 - (1-u)^{|A|}$, so a given collection of blocks $A_1,\dots,A_m$ merges with probability $\prod_i\big(1 - (1-u)^{|A_i|}\big) = u^m\prod_i|A_i| + O(u^{m+1})$, and two blocks merge through the $\theta$-mechanism at rate $\theta|A||B|$. In the classical Λ-coalescent of population genetics each block is marked with probability $u$ regardless of size.

## Depends on

- [Merger rates of a coalescent with simultaneous multiple collisions](../../coalescent-theory/coalescents/xi-coalescents-simultaneous-multiple-collisions.md)

## Expansion

The Poisson construction is the paintbox construction of a Λ-coalescent applied to vertices rather than blocks: an event selects a random fraction $u$ of individuals and connects them, and connected components are the merged blocks. Because a large block has more vertices that can be selected, larger blocks merge faster ("momentum"), the multiplicative analogue of Λ-coalescent merger rates, much as the multiplicative coalescent relates to Kingman's. A motivating reading is social bubbles: an atom is a gathering attended independently with probability $u$ at which friendships form with probability $q$, and a block is a group of individuals linked by chains of friendships. Restricting the graph is consistent while the component partition is not, because a component of $G^{n+1}$ restricted to $[n]$ can split.

## Sources

- Frederic Alberti, Florin Boenkost and Fernando Cordero, "On the block size spectrum of a class of exchangeable dynamic random graphs", arXiv:2406.08972 (2024), Definitions 2.1, 2.2 and 2.3 and Section 2, <https://doi.org/10.48550/arXiv.2406.08972>.
