# Word encoding and stretched-exponential growth of d-combining tree-child networks

**Setting.** As in [one-component d-combining tree-child networks](counting-one-component-d-combining-tree-child-networks.md): rooted $d$-combining tree-child networks with $n$ labeled leaves, tree vertices of outdegree $2$ and reticulations of indegree $d \ge 2$. Let $\mathrm{TC}^{(d)}_{n,k}$ count those with $k$ reticulations and $\mathrm{TC}^{(d)}_n = \sum_k \mathrm{TC}^{(d)}_{n,k}$. Every such network has exactly $n - k - 1$ *free* tree vertices (both children non-reticulations).

**Words.** Let $\mathcal{C}^{(d)}_{n,k}$ be the words over $\omega_1,\dots,\omega_n$ in which $k$ letters occur $d+1$ times and $n-k$ letters occur twice, such that in every prefix each letter either has occurred at most $d-2$ times or occurs at least as often as every $\omega_j$ with $j > i$ (the $0$th, $1$st and $2$nd occurrences of a twice-occurring letter count as its $(d-1)$st, $d$th and $(d+1)$st). Equivalently, these are fillings of Young tableaux with $k$ columns of height $d+1$ and $n-k$ of height $2$, with vertical walls in rows $3$ to $d+1$.

**Theorem (encoding).** With $c^{(d)}_{n,k} = |\mathcal{C}^{(d)}_{n,k}|$,

$$\mathrm{TC}^{(d)}_{n,k} = \frac{n!}{2^{\,n-k-1}}\,c^{(d)}_{n-1,k}.$$

For $d = 2$ this gives a proven word formula for bicombining tree-child networks, analogous to the Pons–Batle conjecture.

**Theorem (asymptotics).** With $a_1 = -2.33810741\ldots$ the largest zero of the Airy function $\mathrm{Ai}$,

$$\mathrm{TC}^{(d)}_n = \Theta\big(\mathrm{TC}^{(d)}_{n,n-1}\big) = \Theta\Big((n!)^d\,\gamma(d)^n\,e^{3a_1\beta(d)n^{1/3}}\,n^{\alpha(d)}\Big),$$

$$\alpha(d) = -\frac{d(3d-1)}{2(d+1)}, \qquad \beta(d) = \Big(\frac{d-1}{d+1}\Big)^{2/3}, \qquad \gamma(d) = 4\,\frac{(d+1)^{d-1}}{(d-1)!}.$$

So a stretched exponential $e^{c\,n^{1/3}}$ appears for every $d \ge 2$. More precisely $\mathrm{TC}^{(2)}_n \sim \sqrt e\,\mathrm{TC}^{(2)}_{n,n-1}$ and $\mathrm{TC}^{(d)}_n \sim \mathrm{TC}^{(d)}_{n,n-1}$ for $d \ge 3$.

**Theorem (reticulations and twigs).** For a uniformly random $d$-combining tree-child network with $n$ leaves and $T^{(d)}_n$ reticulations: $n - 1 - T^{(2)}_n \to \mathrm{Poisson}(1/2)$, while for $d \ge 3$ the limit of $n - 1 - T^{(d)}_n$ is degenerate at $0$. The expected number of twigs is $O(1)$ for $d = 2$ and tends to $0$ for $d \ge 3$.

## Depends on

- [Counting one-component d-combining tree-child networks](counting-one-component-d-combining-tree-child-networks.md)

## Expansion

Networks are built by repeatedly removing a reticulation together with its leaf, or a cherry, and recording which edges the removed arcs were attached to; the free-edge count $2(n-k-1)$ explains the factor $2^{n-k-1}$, and the leaf labels the factor $n!$. The prefix condition encodes the order in which reticulation arcs are inserted into the growing network. The maximally reticulated words $c^{(d)}_{n,n}$ satisfy a recurrence of the type studied for Young tableaux with walls and for compacted trees, whose analysis produces the Airy-function exponent $e^{3a_1\beta n^{1/3}}$. Networks with fewer reticulations contribute a convergent series relative to $k = n-1$: for $d = 2$ the relative weights tend to $(1/2)^j/j!$, giving the factor $\sqrt e$ and the Poisson$(1/2)$ law, and for $d \ge 3$ they vanish.

## Sources

- Yu-Sheng Chang, Michael Fuchs, Hexuan Liu, Michael Wallner and Guan-Ru Yu, "Enumerative and distributional results for d-combining tree-child networks", arXiv:2209.03850 (2022), Theorems 1.8–1.9, Corollaries 1.10–1.11, and Section 3 (Definition 3.1, Theorem 3.4, Lemma 3.6), <https://doi.org/10.48550/arXiv.2209.03850>. Published version: Advances in Applied Mathematics 157 (2024) 102704, <https://doi.org/10.1016/j.aam.2024.102704>.
