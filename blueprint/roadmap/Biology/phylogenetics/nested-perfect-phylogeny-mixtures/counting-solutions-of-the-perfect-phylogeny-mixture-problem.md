# Counting solutions of the perfect phylogeny mixture problem

Let $F = (f_{p,c}) \in [0,1]^{m \times n}$ give the frequency of mutation $c \in [n]$ in bulk sample $p \in [m]$. A solution of the **perfect phylogeny mixture (PPM) problem** is a pair $(U, B)$ with $F = UB$, where $B$ is a complete perfect phylogeny matrix (one row per vertex of a rooted tree whose edges are labelled by the non-founder mutations) and $U$ a nonnegative mixture matrix with rows summing to one. The **ancestry graph** $G_F$ on $[n]$ has an edge $(c,d)$ iff $f_{p,c} \ge f_{p,d}$ for all samples $p$; solutions correspond to spanning arborescences of $G_F$ satisfying the sum condition.

**Facts.**

1. $G_F$ is transitively closed: a path from $c$ to $d$ implies $(c,d) \in E(G_F)$.
2. Neither $(c,d)$ nor $(d,c)$ is an edge iff there are samples $p, q$ with $f_{p,c} > f_{p,d}$ and $f_{q,c} < f_{q,d}$; such pairs lie on distinct branches of every solution. The **branching coefficient** $\gamma(G_F)$ is the fraction of unordered pairs of this kind; $\gamma(G_F) = 0$ for a single sample.
3. $G_F$ is acyclic iff $F$ has no repeated columns; then every spanning arborescence is rooted at the unique source $r$, the founder mutation with $f_{p,r} \ge f_{p,c}$ for all $p, c$.

**Theorem (upper bound).** If $F$ has no repeated columns, the number of PPM solutions is at most

$$\prod_{c \ne r} \deg^{\mathrm{in}}_{G_F}(c).$$

**Theorem (hardness).** Counting PPM solutions (#PPM) is #P-complete, even for $m = 2$ samples.

Thus solutions are typically non-unique: with few samples the ancestry graph is dense ($\gamma$ near zero) and many arborescences satisfy the sum condition, and adding samples raises $\gamma$ and shrinks the solution space.

## Expansion

By Tutte's directed matrix-tree theorem, the number of spanning arborescences rooted at $r$ is $\det \hat L_r$, where $L$ has diagonal entries $\deg^{\mathrm{in}}$ and $-1$ for each edge, and $\hat L_r$ deletes row and column $r$. Ordering vertices topologically makes $\hat L_r$ upper triangular, so the determinant is the product of in-degrees, which bounds the solutions since only arborescences satisfying the sum condition count. Hardness is proved by a reduction from Subset Sum, strengthening the NP-completeness of deciding PPM with two samples.

## Sources

- Y. Qi, D. Pradhan and M. El-Kebir, "Implications of non-uniqueness in phylogenetic deconvolution of bulk DNA samples of tumors", Algorithms for Molecular Biology 14 (2019), Definition 6, Facts 3–8, Lemma 9 and Theorems 10–11, <https://doi.org/10.1186/s13015-019-0155-6>, PMCID: PMC6719395.
