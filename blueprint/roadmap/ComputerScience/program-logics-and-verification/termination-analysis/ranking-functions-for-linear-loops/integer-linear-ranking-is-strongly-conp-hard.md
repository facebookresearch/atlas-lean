# Integer linear ranking is strongly coNP-hard

$\mathrm{LinRF}(\mathbb{Z})$, the existence of a [linear ranking function](linear-ranking-functions.md) for an integer [linear-constraint loop](linear-constraint-loops.md), is strongly coNP-hard, already for single-path loops with affine-linear updates. Given $B \in \mathbb{Z}^{m \times n}$ and $b \in \mathbb{Z}^m$, the integer loop

$$\mathbf{while}\ (Bx - Iz \le b,\ -z \le 0)\ \mathbf{do}\ x' = x,\ z' = 0$$

over variables $x \in \mathbb{Z}^n$, $z \in \mathbb{Z}^m$ has a linear ranking function (namely $z_1 + \dots + z_m$) if $Bx \le b$ has no integer solution, and does not terminate from $(x, 0)$ if $Bx \le b$ has an integer solution $x$. The reduction creates only numbers polynomially bounded in the input size, and the loop constructed either has a linear ranking function or fails to terminate, so the same reduction shows hardness for any termination certificate expressive enough to capture this loop, lexicographic-linear ranking functions included.

## Depends on

- [Linear ranking functions](linear-ranking-functions.md)
- [The class coNP](../../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/co-np.md)
- [Linear-constraint loops](linear-constraint-loops.md)

## Proof depends on

- [Integer emptiness of polyhedra is coNP-hard](integer-emptiness-of-polyhedra-is-conp-hard.md)

## Sources

- A. M. Ben-Amram and S. Genaim, "Ranking functions for linear-constraint loops", *Journal of the ACM* 61(4), Article 26, 2014, <https://doi.org/10.1145/2629488>, numbered as in the journal version (the revised arXiv:1208.4041v4, <https://arxiv.org/abs/1208.4041v4>, keeps this numbering and adds Lemma 5.31), Section 3.1, Theorem 3.1, its proof and the notes after it.
