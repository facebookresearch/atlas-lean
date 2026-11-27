# Shape polynomial of interacting RNA complexes over two backbones

**Setting.** A diagram over $b$ backbones places $n$ vertices on a line, partitioned into $b$ consecutive backbones (RNA strands), with base pairs drawn as arcs in the upper half-plane. Gluing the backbones and arcs as ribbons gives a fatgraph with a topological genus $g$. A *shape* is the topological core of a structure: start from a *preshape*, a diagram with no $1$-arcs $(i,i+1)$, no stacks of parallel arcs and no isolated vertices; remove any rainbow; then add one rainbow arc per backbone. Equivalently, a shape is obtained from a structure by iteratively collapsing stacks and removing hairpin loops and unpaired bases.

**Theorem (finiteness and the one-backbone shape polynomial).** Throughout, arc counts include the rainbow arcs (one per backbone). A $1$-backbone shape of genus $g \ge 1$ with $n$ arcs has $2g + 1 \le n \le 6g - 1$, so there are finitely many shapes of each genus. Their generating polynomial, with $z$ marking arcs, is

$$ S_g(z) = \sum_{t=1}^{g}\kappa_t^{(g)}z^{2g+t}(1+z)^{2g+t-1}, $$

(for example $S_1(z) = z^3 + 2z^4 + z^5$), where the positive integers $\kappa_t^{(g)}$ satisfy $\kappa_1^{(1)} = 1$, $\kappa_t^{(g)} = 0$ for $t < 1$ or $t > g$, and

$$ (2g+t)\,\kappa_t^{(g)} = \big(2(2g+t)-3\big)\big(2(2g+t)-5\big)\Big((2g+t-2)\,\kappa_t^{(g-1)} + 2\big(2(2g+t)-7\big)\kappa_{t-1}^{(g-1)}\Big). $$

**Theorem (two backbones).** One-backbone shapes of genus $g$ split into $A$-shapes and $B$-shapes, with a bijection $\theta : \mathcal{A}_g(n+2) \to \mathcal{B}_g(n+1)$. The genus of a two-backbone diagram with $n$ arcs and $r$ boundary components is defined by $2 - 2g - r = 2 - n$, so a concatenation of two one-backbone shapes of genera $i$ and $j$ has genus $i + j - 1$. Let $\mathcal{Q}_g$ be the two-backbone shapes of genus $g$ that are not such concatenations, and $\mathcal{Q}'_g$ the union of $\mathcal{Q}_g$ with the concatenations of genus $g$ (genera $i \ge 1$ and $g + 1 - i \ge 1$). Then $\mathcal{Q}'_g$ is in arc-count-shifting bijection $\eta_n : \mathcal{Q}'_g(n+2) \to \mathcal{A}_{g+1}(n+3)$ with $A$-shapes of genus $g+1$ (a two-backbone shape with $\ell$ multiloops maps to an $A$-shape with $\ell + 1$ multiloops). Consequently the polynomial of genus-$g$ shapes over two backbones, $z$ marking arcs including both rainbows, is

$$ Q_g(z) = \frac{S_{g+1}(z)}{1+z} - \sum_{i=1}^{g}S_i(z)\,S_{g+1-i}(z), \qquad \frac{S_{g+1}(z)}{1+z} = \sum_{t=1}^{g+1}\kappa_t^{(g+1)}z^{2g+t+2}(1+z)^{2g+t} . $$

(The source's Theorem 4.5 prints the exponent $2g+t+1$, which counts one rainbow fewer than its own $S_{g+1}$ and $\eta_n$; the exponent above follows from $S_{g+1} = (1 + 1/z)A_{g+1}$ and $\mathcal{Q}'_g(z) = A_{g+1}(z)/z$.)

Inverting $\eta$ applied to a uniform $A$-shape gives a linear-time uniform sampler of two-backbone shapes of fixed genus.

**Theorem (fibers).** For a two-backbone shape $\mathfrak{s}_{l,g}$ with $l$ arcs besides its two rainbows, the matchings of genus $g$ projecting to it have generating function

$$ Q_{\mathfrak{s}_{l,g}}(z) = C_0(z)^{2l+2}\,\frac{z^{l+2}}{\big(1 - zC_0(z)^2\big)^{l+2}}, \qquad C_0(z) = \frac{1 - \sqrt{1-4z}}{2z}, $$

which depends only on $l$, and their number of length $n$ grows like $\frac{k}{(l+1)!}n^{l+1}4^{n-l-2}$ for a constant $k > 0$.

## Depends on

- [Genus-filtered topological RNA structures: generating functions and arc statistics](genus-filtered-topological-rna-structures-generating-functions-and-arc-statistics.md)

## Expansion

The bound $n \le 6g - 1$ follows from Euler's formula for the fatgraph. A shape has $v_1 = 1$ (only the boundary component through the plant has length 1) and $v_2 = 0$ (no stacks), so the remaining boundary components have length at least $3$. Hence $2n \ge 3(r-1) + 1$, and with $2n = 4g + 2r - 2$ this gives $r \le 4g$. The bijection $\eta$ joins the two backbones of an interacting complex into one by an extra arc, which raises the genus by one and lands in the $A$-class. Subtracting products $S_iS_{g+1-i}$ removes the disconnected complexes, where the two strands do not interact. Each shape arc inflates into a nonempty stack and each gap into a genus-$0$ structure, which gives the fiber generating function as a substitution into $C_0$.

## Sources

- Benjamin MingMing Fu and Christian M. Reidys, "Shapes of interacting RNA complexes", arXiv:1405.3390 (2014), Section 3 (Lemma 3.1, Theorem 3.2, Proposition 3.3), Section 4 (Lemma 4.1, Theorem 4.2, Corollaries 4.3–4.4, Theorem 4.5), Section 5 (Theorem 5.1, Corollary 5.2), <https://doi.org/10.48550/arXiv.1405.3390>.
