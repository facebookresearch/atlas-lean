# Integer hulls and bit sizes of polyhedra

The *integer hull* of a rational polyhedron $P \subseteq \mathbb{Q}^n$ is $P_I = \mathrm{conv}(P \cap \mathbb{Z}^n)$, the convex hull of its integer points; it is again a rational polyhedron. The bit size of an integer $x$ is $\|x\| = 1 + \lceil \log(|x| + 1) \rceil$, of a vector $a \in \mathbb{Z}^n$ it is $\|a\| = n + \sum_i \|a_i\|$, and of an inequality $a \cdot x \le c$ it is $1 + \|c\| + \|a\|$. The *facet size* $\|P\|_f$ is the least $\varphi \ge n$ such that $P$ is described by a system $Ax \le b$ each of whose inequalities fits in $\varphi$ bits. The *vertex size* $\|P\|_v$ is the least $\psi \ge n$ such that $P$ has a generator representation, as the convex hull of points $x_i$ plus the cone of rays $y_j$, in which each $x_i$ and $y_j$ fits in $\psi$ bits; for integer polyhedra the generators are required to be integer.

## Sources

- A. M. Ben-Amram and S. Genaim, "Ranking functions for linear-constraint loops", *Journal of the ACM* 61(4), Article 26, 2014, <https://doi.org/10.1145/2629488>, numbered as in the journal version (the revised arXiv:1208.4041v4, <https://arxiv.org/abs/1208.4041v4>, keeps this numbering and adds Lemma 5.31), Section 2.1 (integer hull; bit size, facet size and vertex size).
