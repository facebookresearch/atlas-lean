# UniFrac distances as branch sums

**Setting.** A rooted phylogeny on the taxa has branches $b = 1, \dots, B$ with lengths $l_b > 0$. For a community (sample) $i$ with taxon abundances at the leaves, let $p_{ib}$ be the proportion of individuals in sample $i$ that descend from branch $b$ (recursively: a leaf branch carries its leaf's abundance and an internal branch the sum over its child branches, normalized by the sample total).

**Definitions.** For samples $i, j$:

- *Unweighted UniFrac*, the fraction of total branch length unique to one of the two communities:

$$d_u(i,j) = \frac{\sum_{b=1}^B l_b \,\bigl|\mathbf 1(p_{ib} > 0) - \mathbf 1(p_{jb} > 0)\bigr|}{\sum_{b=1}^B l_b}.$$

- *Raw weighted UniFrac* and its normalized version:

$$d_w(i,j) = \sum_{b=1}^B l_b\, |p_{ib} - p_{jb}|, \qquad d_{wn}(i,j) = \frac{\sum_b l_b\, |p_{ib} - p_{jb}|}{\sum_b l_b\,(p_{ib} + p_{jb})}.$$

- *Generalized UniFrac* with $\alpha \in [0,1]$:

$$d_g(i,j,\alpha) = \frac{\sum_b l_b\,(p_{ib} + p_{jb})^\alpha \left|\dfrac{p_{ib} - p_{jb}}{p_{ib} + p_{jb}}\right|}{\sum_b l_b\,(p_{ib} + p_{jb})^\alpha},$$

with terms having $p_{ib} + p_{jb} = 0$ omitted; $\alpha = 1$ gives $d_{wn}$.

Unweighted UniFrac depends only on presence and absence; raw weighted UniFrac equals the earth mover's distance between the two abundance distributions on the tree, with branch lengths as transport costs.

**Branch contributions.** Since each distance is a sum over branches, the share of branch $b$ in, for example, $d_u$ is $l_b\,|\mathbf 1(p_{ib} > 0) - \mathbf 1(p_{jb} > 0)| \big/ \bigl(d_u(i,j)\sum_{b'} l_{b'}\bigr)$. Deep branches (many descendants) are shared by almost all samples and contribute little to $d_u$ but much to $d_w$; hence unweighted UniFrac emphasizes shallow parts of the phylogeny and weighted UniFrac deep parts, with generalized UniFrac in between as $\alpha$ varies.

## Depends on

- [Coupling of two probability measures](../../../../MeasureTheory/optimal-transport/kantorovich-duality/is-coupling.md)

## Expansion

A branch contributes to $d_u$ only if exactly one sample has descendants below it, which almost never holds for branches with many descendants; in $d_w$ its contribution is the difference in descendant mass, which is largest near the root. Real microbiome data show the effect starkly: in the source's antibiotic time course, branches with at most 9 descendants carry about 90% of unweighted but only about 25% of weighted UniFrac.

## Sources

- J. Fukuyama, "Emphasis on the deep or shallow parts of the tree provides a new characterization of phylogenetic distances", *Genome Biology* (2019), Background, Eqs. (1)–(4), Results ("Branch contributions", Fig. 1) and Appendix Eqs. (16)–(17). <https://doi.org/10.1186/s13059-019-1735-y> (PMC6599322)
