# High-resolution expression purification is underdetermined

Let $M \in \mathbb{R}^{n \times k}_{\ge 0}$ and $F \in \mathbb{R}^{c \times k}_{\ge 0}$ be as in [group-mode purification](group-mode-expression-purification-by-nonnegative-least-squares.md). Sample-resolved purification asks, for each gene $i$, for a matrix $G_i \in \mathbb{R}^{k \times c}_{\ge 0}$ whose entry $(G_i)_{j,t}$ is the expression of gene $i$ in cell type $t$ *within sample $j$*, subject to

$$\operatorname{diag}\bigl(G_i F\bigr) = M_{i,\bullet}, \qquad (G_i)_{j,t} \ge 0,$$

equivalently $\sum_{t=1}^{c} (G_i)_{j,t} F_{t,j} = M_{i,j}$ for $1 \le j \le k$.

**Claim.** The constraint decouples across samples: the feasible set is the product

$$\mathcal{G}_i = \prod_{j=1}^{k} \Bigl\{ g \in \mathbb{R}^{c}_{\ge 0} : \textstyle\sum_{t} g_t F_{t,j} = M_{i,j} \Bigr\}.$$

Assume $F_{t,j} > 0$ for all $t,j$. If $M_{i,j} > 0$ for every $j$, then $\mathcal{G}_i$ is a nonempty compact convex polytope of dimension $k(c-1)$; in particular, for $c \ge 2$ the system is not identifiable: it has infinitely many solutions, although explicit ones exist, such as the vertices described below. More generally $\dim \mathcal{G}_i = (c-1)\,\#\{j : M_{i,j} > 0\}$, so if $M_{i,j} = 0$ for every $j$ the unique solution is $G_i = 0$.

## Depends on

- [Group-mode expression purification by nonnegative least squares](group-mode-expression-purification-by-nonnegative-least-squares.md)

## Proof sketch

Each diagonal entry of $G_i F$ involves only row $j$ of $G_i$ and column $j$ of $F$, which is why the constraints separate by sample. For a fixed $j$ the set $\{g \ge 0 : \langle g, F_{\bullet,j}\rangle = M_{i,j}\}$ is the intersection of the nonnegative orthant of $\mathbb{R}^c$ with an affine hyperplane whose normal $F_{\bullet,j}$ has all coordinates positive; it is therefore a bounded simplex with vertices $(M_{i,j}/F_{t,j})e_t$, nonempty and of dimension $c-1$ when $M_{i,j} > 0$ and a single point $\{0\}$ when $M_{i,j} = 0$. A product of $k$ such simplices has dimension $k(c-1)$.

Identifiability therefore has to come from outside the linear system. Two structural assumptions make the problem tractable: genes are treated independently, so the decomposition is solved one gene at a time; and expression is assumed to vary smoothly across samples ordered by their bulk expression, so that cell-type profiles are imputed on sliding windows of samples, each window again solved by nonnegative least squares. A window of length $w$ turns the single underdetermined equation per sample into $w$ equations in $c$ unknowns, which requires $c < w$, and $w \le k/2$ keeps two disjoint groups of samples available for contrasts.

## Sources

- A. M. Newman, C. B. Steen, C. L. Liu, A. J. Gentles, A. A. Chaudhuri, F. Scherer, M. S. Khodadoust, M. S. Esfahani, B. A. Luca, D. Steiner, M. Diehn, A. A. Alizadeh, "Determining cell type abundance and expression from bulk tissues with digital cytometry", Nature Biotechnology 37 (2019) 773-782, Methods, "Rationale for high-resolution expression purification", Equation (3) and the window bound $c < w \le k/2$, <https://doi.org/10.1038/s41587-019-0114-2> (PMC6610714).
