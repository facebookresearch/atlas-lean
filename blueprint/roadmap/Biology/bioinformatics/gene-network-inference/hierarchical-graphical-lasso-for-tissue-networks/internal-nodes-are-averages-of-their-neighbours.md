# Internal nodes of the hierarchy are averages of their neighbours

Let a finite tree have node set $V = \mathcal{L} \cup \mathcal{I}$, with leaves $\mathcal{L} \neq \emptyset$ and internal nodes $\mathcal{I}$, every node joined to the others through tree edges $E$. Fix real symmetric matrices $S^{(l)}$ for the leaves $l \in \mathcal{L}$ and, with $\lVert\cdot\rVert_F$ the Frobenius norm (so $\lVert X \rVert_F^2$ is the sum of the squared entries of $X$), consider

$$\Phi\big((S^{(u)})_{u \in \mathcal{I}}\big) = \sum_{\{a, b\} \in E} \lVert S^{(a)} - S^{(b)} \rVert_F^2 .$$

Then $\Phi$ has a unique minimizer over internal-node matrices, characterized by

$$S^{(u)} = \frac{1}{\deg(u)} \sum_{v \sim u} S^{(v)} \qquad \text{for every } u \in \mathcal{I},$$

where $v \sim u$ ranges over the tree neighbours of $u$ (its parent, if any, and its children). Each minimizing $S^{(u)}$ is a convex combination of the leaf matrices; in particular, if every $S^{(l)}$ is positive semidefinite, so is every $S^{(u)}$. Holding one internal node's neighbours fixed, the minimizer over that node alone is the same neighbour average.

## Expansion

$\Phi$ is a sum of squared entrywise differences, so it decouples over matrix entries; for one entry it is the Dirichlet energy of a function on the tree with boundary values prescribed on the leaves. Setting the gradient with respect to $S^{(u)}$ to zero gives $\sum_{v \sim u} (S^{(u)} - S^{(v)}) = 0$, the stated averaging (discrete harmonic) condition. The energy is strictly convex in the internal values because every internal node is connected to a leaf: the graph Laplacian restricted to $\mathcal{I}$ is positive definite, so the linear system has exactly one solution. The harmonic extension at $u$ equals the expected leaf value at which a simple random walk started at $u$ first hits $\mathcal{L}$, which exhibits it as a convex combination of leaf matrices. In the hierarchical graphical lasso across related tissues the internal nodes appear only in the parent-similarity penalty, so with the leaves fixed their update is this closed-form linear solve, which is why the internal-node step is essentially instantaneous.

## Sources

- E. Pierson, D. Koller, A. Battle, S. Mostafavi et al. (GTEx Consortium), "Sharing and specificity of co-expression networks across 35 human tissues", PLoS Computational Biology 11 (2015), e1004220, <https://doi.org/10.1371/journal.pcbi.1004220> (PMC4430528). Results (Algorithm) and Materials and Methods.
- D. A. Spielman, *Spectral and Algebraic Graph Theory*, Chapter 11, Lemma 11.5.3 and Theorem 11.6.1 (existence and uniqueness of the harmonic minimizer).
- R. Lyons and Y. Peres, *Probability on Trees and Networks* (Cambridge University Press, 2016), Section 2.1 (convex-combination representation of harmonic functions via hitting probabilities).
