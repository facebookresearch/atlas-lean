# Voronoi and UPGMA regions around a tritomy

Near a tree metric with a single tritomy $T$, dissimilarity space decomposes as $\operatorname{span} C_T \oplus \operatorname{span} K_T$, where $K_T$ is the planar fan of the three binary resolution cones (see [angles between resolution cones](angles-between-resolution-cones-at-a-tritomy.md)), spanned by the orthogonal projections $p_{AB}, p_{AC}, p_{BC}$ of the resolution directions. A distance-based method assigns each data point to one resolution; the **Voronoi cell** of a resolution cone is the set of dissimilarity maps closer in Euclidean distance to it than to the other two (the least-squares choice).

**Proposition.** The boundary between the Voronoi cells of $C_{T_{AB}}$ and $C_{T_{AC}}$ is determined by the angle bisector of $p_{AB}$ and $p_{AC}$ in $\operatorname{span} K_T$.

**Theorem (rooted, equidistant).** If $T$ is a ranked rooted tree with one tritomy having daughter clades of sizes $a, b, c$, the Voronoi boundary between $C_{T_{AB}}$ and $C_{T_{AC}}$ in $\operatorname{span} K_T$ is spanned by

$$\frac{p_{AB}}{\sqrt{a+b}} + \frac{p_{AC}}{\sqrt{a+c}}.$$

**Theorem (unrooted).** If $T$ is unrooted with one tritomy splitting leaves into blocks of sizes $a,b,c,d$, the Voronoi boundary between $C_{T_{AB}}$ and $C_{T_{AC}}$ is spanned by

$$\frac{p_{AB}}{\sqrt{(a+b)(c+d)}} + \frac{p_{AC}}{\sqrt{(a+c)(b+d)}}.$$

**Theorem (UPGMA).** For a ranked rooted tree with one tritomy, the boundaries between the UPGMA regions for the three resolutions are orthogonal to $\operatorname{span} K_T$, and in $\operatorname{span} K_T$ the boundary between the UPGMA cells of $T_{AC}$ and $T_{BC}$ is the ray spanned by $-p_{AB}$.

Hence UPGMA splits the plane $K_T$ along the rays opposite to the resolution directions, while least squares splits it along angle bisectors weighted by clade sizes; the two methods disagree on an explicit region whenever $a, b, c$ are unequal.

## Depends on

- [Angles between resolution cones at a tritomy](angles-between-resolution-cones-at-a-tritomy.md)

## Expansion

Distance to each resolution cone splits into components in $\operatorname{span} C_T$ and $\operatorname{span} K_T$, and only the second differs between resolutions, so Voronoi boundaries reduce to bisectors in the plane. Normalizing $p_{AB}$ uses $\|p_{AB}\|^2$, which the explicit formula gives as proportional to $a+b$ (rooted) or to $(a+b)(c+d)$ (unrooted); the sum of the two unit vectors spans the bisector. UPGMA first merges the closest pair of clusters; near the tritomy the decision between merging $A$ with $C$ or $B$ with $C$ depends only on the sign of one linear functional, whose kernel in $K_T$ is the line through $p_{AB}$.

## Sources

- Ruth Davidson, Seth Sullivant, "Distance-based phylogenetic methods around a polytomy", arXiv (2013). Section 4 (Proposition 4.1, Theorems 4.2 and 4.3, Proposition 4.4, Theorem 4.5). <https://doi.org/10.48550/arXiv.1307.5908>. Published version: IEEE/ACM Transactions on Computational Biology and Bioinformatics 11(2) (2014), 325–335, <https://doi.org/10.1109/tcbb.2014.2309592>; locators above refer to the arXiv version.
