# Angles between resolution cones at a tritomy

Identify a dissimilarity map on a leaf set $X = [n]$ with a vector in $\mathbb R^{n(n-1)/2}$ (coordinates $e_{ij}$). For disjoint $A_1,\dots,A_k \subseteq X$ let $\delta_{A_1|\cdots|A_k} = \sum e_{ij}$ over pairs $i,j$ in different blocks; for a split $A|B$ this is the split pseudometric, with $\|\delta_{A|B}\|_2^2 = |A|\,|B|$. The tree metrics compatible with a phylogenetic $X$-tree $T$ form a simplicial cone $C_T$ with extreme rays $\{\delta_{A|B} : A|B \text{ a split of } T\}$; equidistant (ultrametric) tree metrics compatible with a ranked rooted tree form a simplicial cone with extreme rays $\delta_{\pi_2},\dots,\delta_{\pi_n}$ along its chain of partitions.

Let $T$ have a single **tritomy** (a node of degree $4$ unrooted, or with three children rooted). Its cone $C_T$ is the common facet of the three cones of its binary resolutions, and near a generic point of $C_T$ tree space looks like $\mathbb R^{\dim C_T} \times K_T$, where $K_T$ is a fan of three rays in a $2$-dimensional plane orthogonal to $C_T$. The **angle between two resolution cones** is the angle between their rays in $K_T$.

**Theorem (equidistant trees).** If the tritomy of a ranked rooted tree has daughter clades $A, B, C$ of sizes $a, b, c$, and $T_{XY}$ denotes the resolution in which $X \cup Y$ is a clade, then the angle between $C_{T_{AC}}$ and $C_{T_{BC}}$ is

$$\arccos\Big(\frac{-c}{\sqrt{(a+c)(b+c)}}\Big).$$

**Theorem (unrooted trees).** If the tritomy of an unrooted tree splits the leaves into $A|B|C|D$ with sizes $a,b,c,d$, and $T_{XY}$ is the resolution with the split $X \cup Y \,|\, \text{rest}$, then the angle between $C_{T_{AB}}$ and $C_{T_{AC}}$ is

$$\arccos\Big(-\frac{bc + ad}{\sqrt{(a+b)(a+c)(b+d)(c+d)}}\Big).$$

In both cases $\operatorname{span} K_T$ is $2$-dimensional. For equidistant trees the three angles are equal ($120^\circ$) only when $a = b = c$; otherwise the angles are unequal, so the regions of data space mapped to each resolution have unequal size. For unrooted trees equality of the angles is not tied to balanced sizes: for sizes $(a,b,c,d) = (k,1,1,1)$ the formula gives cosine $-\frac{1+k}{2(k+1)} = -\frac12$ for each of the three pairs, so all three angles are $120^\circ$ for every $k$.

## Expansion

In the rooted case, $\operatorname{span} C_{T_{AB}}$ adds to $\operatorname{span} C_T$ one direction, whose component orthogonal to $C_T$ is the rejection of $\delta_{A|C} + \delta_{B|C}$ from $\delta_{A|B} + \delta_{A|C} + \delta_{B|C}$. Because $\delta_{A|B}, \delta_{A|C}, \delta_{B|C}$ have disjoint supports, this is

$$p_{AB} = -\frac{ac + bc}{ab + ac + bc}\,\delta_{A|B} + \frac{ab}{ab+ac+bc}\,(\delta_{A|C} + \delta_{B|C}),$$

and $p_{AB} + p_{AC} + p_{BC} = 0$, so $K_T$ is planar. The angle formula is the normalized inner product of two of these vectors, computed using $\|\delta_{X|Y}\|^2 = |X||Y|$. The unrooted case is the same computation after choosing an orthogonal basis of $\operatorname{span} C_T$ adapted to the four clades.

## Sources

- Ruth Davidson, Seth Sullivant, "Distance-based phylogenetic methods around a polytomy", arXiv (2013). Section 2 (Propositions 2.2 and 2.4, local structure $\mathbb R^k \times K_T$), Section 3 (Lemma 3.3, Corollary 3.4, Theorem 3.5, Theorem 3.8, Corollary 3.9). <https://doi.org/10.48550/arXiv.1307.5908>. Published version: IEEE/ACM Transactions on Computational Biology and Bioinformatics 11(2) (2014), 325–335, <https://doi.org/10.1109/tcbb.2014.2309592>; locators above refer to the arXiv version.
