# The number of accessible paths in the hypercube converges to a product of exponentials

**Setting (House-of-Cards landscape).** On the hypercube $\{0,1\}^L$, assign i.i.d. Uniform$[0,1]$ fitness values to every genotype except two: the target $(1,\dots,1)$ gets value $1$, and the starting genotype $(0,\dots,0)$ gets value $x$. A shortest path from $(0,\dots,0)$ to $(1,\dots,1)$ flips each coordinate once, and there are $L!$ such paths. A path is **open** (accessible) if the fitness values along it are strictly increasing. Let $\Theta$ be the number of open paths. A simplified model replaces the hypercube by a rooted tree whose arity decreases from $L$ at the root to $1$. It has $L!$ root-to-leaf paths, with independent values at every node and value $1$ at every leaf.

**First moments.** Each path is open with probability $(1-x)^{L-1}/(L-1)!$, so $\mathbb{E}^x\Theta = L(1-x)^{L-1}$ on both graphs. With $x$ uniform, $\mathbb{E}^*\Theta = 1$. At the scale $x = X/L$, $\mathbb{E}^{X/L}(\Theta/L) \to e^{-X}$, and $\operatorname{Var}^{X/L}(\Theta/L) \to e^{-2X}$ on the tree and $3e^{-2X}$ on the hypercube.

**Theorem.** Fix $X \ge 0$ and let $x = X/L$. As $L\to\infty$:

1. on the tree, $\Theta/L$ converges in law to $e^{-X}\,\mathcal{E}$ with $\mathcal{E}$ a standard exponential variable;
2. on the hypercube, $\Theta/L$ converges in law to $e^{-X}\,\mathcal{E}_1\mathcal{E}_2$ with $\mathcal{E}_1, \mathcal{E}_2$ independent standard exponentials.

Moreover, on the tree with $x = (\ln L + X)/L$, $\mathbb{E}\Theta \to e^{-X}$ and $\operatorname{Var}\Theta \to e^{-2X} + e^{-X}$. When $x$ is uniform on $[0,1]$, $\mathbb{P}^*(\Theta \ge 1) \sim (\ln L)/L$.

So although on average one accessible path leads to the fittest genotype, a random start almost never has one. When one exists, the start had fitness $O(\ln L/L)$, and the count of paths fluctuates on the scale of its mean.

## Expansion

Proposition 1 comes from counting pairs of open paths by the level at which they separate. On the tree, the second-moment computation together with a recursive decomposition at the root proves the exponential limit. The proof works with Laplace transforms $F_k(z) = \exp\big[-\int_0^z (1-F_{k-1}(z'))\,dz'/z'\big]$, $F_0(z) = e^{-z}$. Section 6 of the source reads $F_k$ as the Laplace transform of $Y_k$, the total position at generation $k$ of a cascade of Poisson processes with intensity $\mathbf{1}_{(0,1]}(x)\,dx/x$. Path counts restricted to the first $k$ levels converge to $e^{-X}Y_k$, and $Y_k$ converges to a standard exponential as $k\to\infty$ (Theorem 4). On the hypercube, the graph looks locally like such a tree near both the start corner and the target corner. Paths decorrelate in the middle, so the count factorizes into two independent tree-like contributions, one from each end. This explains the product $\mathcal{E}_1\mathcal{E}_2$ and the variance constant $3 = \mathbb{E}(\mathcal{E}_1\mathcal{E}_2)^2 - 1$.

## Depends on

- [Accessible mutational paths in the House-of-Cards landscape](../../population-genetics/selection-migration-and-transmission/fitness-landscapes/accessible-adaptive-paths.md)

## Sources

- J. Berestycki, É. Brunet and Z. Shi, "The number of accessible paths in the hypercube", *Bernoulli* 22 (2016), 653–680, <https://doi.org/10.3150/14-BEJ641>; preprint arXiv:1304.0246 (2013), Proposition 1 and Theorems 1–4, <https://doi.org/10.48550/arXiv.1304.0246>.
- P. Hegarty and A. Martinsson, "On the existence of accessible paths in various models of fitness landscapes", *Annals of Applied Probability* 24 (2014), 1375–1395, <https://doi.org/10.1214/13-AAP949> (source of the hypercube variance in Proposition 1).
