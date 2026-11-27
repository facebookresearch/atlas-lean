# Bit-size bounds for integer hulls

Let $P$ be a rational polyhedron in $\mathbb{Q}^n$, $n \ge 1$, with [facet size and vertex size](integer-hulls-and-bit-sizes-of-polyhedra.md) $\|P\|_f$ and $\|P\|_v$. Then

$$\|P\|_v \le 4n^2 \|P\|_f, \qquad \|P\|_f \le 4n^2 \|P\|_v,$$

and its integer hull $P_I$ satisfies

$$\|P_I\|_v \le 6n^3 \|P\|_f, \qquad \|P_I\|_f \le 24 n^5 \|P\|_f .$$

These bounds keep the integer points needed as witnesses for or against an integer ranking function polynomially sized.

## Depends on

- [Integer hulls and bit sizes of polyhedra](integer-hulls-and-bit-sizes-of-polyhedra.md)

## Sources

- A. M. Ben-Amram and S. Genaim, "Ranking functions for linear-constraint loops", *Journal of the ACM* 61(4), Article 26, 2014, <https://doi.org/10.1145/2629488>, numbered as in the journal version (the revised arXiv:1208.4041v4, <https://arxiv.org/abs/1208.4041v4>, keeps this numbering and adds Lemma 5.31), Section 2.1, Theorems 2.7 and 2.8, quoting A. Schrijver, *Theory of Linear and Integer Programming*, Wiley, 1986, Theorem 10.2 and Corollaries 17.1a and 17.1b (after Karp and Papadimitriou).
