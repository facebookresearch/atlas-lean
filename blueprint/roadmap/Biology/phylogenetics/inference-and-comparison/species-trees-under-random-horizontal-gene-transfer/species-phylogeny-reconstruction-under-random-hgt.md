# Species phylogeny reconstruction from gene tree topologies under random HGT

**Model.** Let $T_s$ be a rooted binary species phylogeny on $n$ leaves with branch durations $\tau(e)$; two points of $T_s$ are *contemporaneous* if they are at the same time distance from the root. Each branch $e$ carries an HGT rate $\lambda(e)$ and, for each gene $g$, a substitution rate $\mu_g(e)$. A gene tree $T_g$ is generated as follows: recipient locations are a Poisson process of rate $\lambda(e)$ along each branch; for a recipient $x$ a donor $y$ is chosen uniformly among the locations contemporaneous with $x$; processing events chronologically from the root, each transfer is an SPR move that prunes the gene subtree below $x$ and regrafts it at $y$. Each gene-tree edge, which maps to a (partial) species branch $e$ over a time interval of length $\ell$, gets length $\mu_g(e)\,\ell$. The data are, for $N$ independent genes, **$\epsilon$-contractions** of the gene trees: unrooted topologies restricted to paths between leaves, with degree-$2$ vertices suppressed and some edges of length at most $\epsilon$ contracted.

**Bounded-rates model.** Constants $0\le\rho_\lambda\le1$, $0<\rho_\tau,\rho_\mu\le1$, $0<\bar\tau,\bar\lambda,\bar\mu<\infty$ with, for all branches $e$ and genes $g$, $\rho_\lambda\bar\lambda \le \lambda(e)\le\bar\lambda$, $\underline\tau := \rho_\tau\bar\tau\le\tau(e)\le\bar\tau$, $\underline\mu := \rho_\mu\bar\mu\le\mu_g(e)\le\bar\mu$.

**Theorem.**

1. (Reconstruction at low HGT rate.) Fix the constants above and $0\le\epsilon<\underline\tau\,\underline\mu$. If $\bar\lambda$ is a sufficiently small constant (independent of $n$), the topology of $T_s$ can be reconstructed with probability at least $1 - 1/\mathrm{poly}(n)$ from $\epsilon$-contractions of $N = \Omega(\log n)$ independent gene trees. The same holds from ultrametric $\epsilon$-distortions of the gene trees (estimated branch lengths within $\epsilon$) when $\mu_g(e)\equiv\mu$ and $\epsilon < \underline\tau\mu/2$.
2. (Hardness at high HGT rate.) With $\rho_\lambda = 0$ and any $\rho_\tau,\rho_\mu,\bar\tau,\bar\mu$, there is a constant $\bar\lambda$ large enough that for every $n$ there are two species phylogenies that produce the same $N = \Omega(n^{1/6})$ gene trees with probability at least $1/2$.

## Depends on

- [Quartet support and determination of trees by quartets](../../quartet-support-and-determination-of-trees-by-qu/README.md)

## Expansion

At low constant HGT rate each gene tree is a few SPR moves away from $T_s$ near any given node, so for a pair of nodes $u, v$ of $T_s$ a typical gene tree contains, with probability close to $1$, real subtrees that are copies of "diluted" versions of the species subtrees below $u$ and $v$ (some leaves transferred away), and the graph distance between their roots estimates the species-tree distance. The algorithm reconstructs the species tree bottom-up from cherries, at each level identifying diluted subtrees in polynomial time and taking a majority over the $\Omega(\log n)$ genes, which gives the high-probability guarantee by a union bound over pairs. The impossibility result couples two phylogenies differing in a deep region: at high transfer rate the gene trees mix that region thoroughly, and the coupling succeeds on all $N$ genes simultaneously with probability at least $1/2$ as long as $N$ is at most a small power of $n$.

## Sources

- Constantinos Daskalakis, Sebastien Roch, "Species trees are recoverable from unrooted gene tree topologies under a constant rate of horizontal gene transfer", arXiv (2015). Section 2 (Definition of the stochastic HGT model, $\epsilon$-contractions, bounded-rates model), Theorems 1–3, Propositions 1–4. <https://doi.org/10.48550/arXiv.1508.01962>. Published version: "Species trees from gene trees despite a high rate of lateral genetic transfer: a tight bound (extended abstract)", Proceedings of the Twenty-Seventh Annual ACM-SIAM Symposium on Discrete Algorithms (SODA 2016), 1621–1630, <https://doi.org/10.1137/1.9781611974331.ch110>; locators above refer to the arXiv version.
