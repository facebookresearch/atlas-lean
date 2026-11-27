# Generating function and asymptotic count of rooted binary perfect phylogenies

**Definition.** A *rooted binary perfect phylogeny* with sample size $s$ is a rooted binary unlabeled tree with $n \le s$ leaves together with an assignment of a positive integer to each leaf, the integers summing to $s$; the integer at a leaf counts indistinguishable sampled lineages carrying the same haplotype. Two perfect phylogenies are identified if they differ by swapping the two subtrees at a node. Let $b_s$ be the number of rooted binary perfect phylogenies with sample size $s$ (summing over all $n$), with $b_0 = 0$, $b_1 = 1$.

**Proposition (recursion).** For $s \ge 2$,

$$b_s = 1 + \sum_{i=1}^{s-1} \tfrac12\, b_{s-i}\, b_i + \tfrac12\, b_{s/2}\,\mathbf{1}\{s \text{ even}\},$$

the leading $1$ counting the single-leaf tree with value $s$.

**Proposition (generating function).** $B(z) = \sum_{s \ge 1} b_s z^s$ satisfies

$$B(z) = \tfrac12 B(z)^2 + \tfrac12 B(z^2) + \frac{z}{1-z}.$$

**Theorem (asymptotics).** The radius of convergence $\beta$ of $B$ satisfies $1/4 \le \beta \le \rho \approx 0.4027$, where $\rho$ is the radius of convergence for rooted binary unlabeled trees, and

$$b_s \sim \frac{\gamma}{2\sqrt{\pi}}\left(\frac1r\right)^{s} s^{-3/2} \approx 0.3519 \cdot (3.2599)^s\, s^{-3/2}, \qquad \gamma \approx 1.2476,\ r \approx 0.3068,$$

which grows faster than the Wedderburn–Etherington count $\approx 0.3188\,(2.4833)^s s^{-3/2}$ of rooted binary unlabeled trees with $s$ leaves.

## Expansion

A perfect phylogeny with more than one leaf splits at the root into an unordered pair of perfect phylogenies with sample sizes $i$ and $s-i$; ordered pairs are counted twice except when both subtrees coincide, which is possible only for $i = s/2$, hence the $\tfrac12$ terms. The functional equation is the standard Pólya-type equation for unordered binary trees with the leaf generating function replaced by $z/(1-z)$ (a leaf of any positive size). Treating $B(z^2)$ as analytic on a larger disk turns the equation into a quadratic in $B(z)$ with a square-root singularity at $z = r$; singularity analysis then gives the $s^{-3/2}$ law.

## Sources

- Chloe E. Shiff and Noah A. Rosenberg, "Enumeration of rooted binary perfect phylogenies", Discrete Applied Mathematics 380 (2026), 538–561, <https://doi.org/10.1016/j.dam.2025.10.053>; numbering as in arXiv:2410.14915: Propositions 1–2, Corollary 4 and Theorem 5 (Section 3).
