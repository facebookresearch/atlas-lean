# Hermitian dilation

Let the entries lie in a set with a zero and a conjugation $x \mapsto x^*$, such as $\mathbb{R}$ or $\mathbb{C}$. For a rectangular $m \times n$ matrix $B$, the Hermitian dilation of $B$ is the $(m + n) \times (m + n)$ block matrix

$$\mathscr{H}(B) = \begin{bmatrix} 0 & B \\ B^* & 0 \end{bmatrix},$$

indexed by the disjoint union of the row and column index sets of $B$, where $B^*$ is the conjugate transpose.

## Idea

Many results about eigenvalues hold only for Hermitian matrices. The dilation embeds any rectangular matrix into a Hermitian one without losing information: for a finite real or complex matrix $B$, $\mathscr{H}(B)$ is Hermitian, depends linearly on $B$ over the reals, and its square is the block-diagonal matrix with blocks $BB^*$ and $B^*B$. Its eigenvalues are therefore plus and minus the singular values of $B$, together with zeros, and the spectrum is symmetric about $0$. In particular, when $B$ has at least one row or column, the largest eigenvalue of $\mathscr{H}(B)$ is the spectral norm of $B$. This is how concentration inequalities for sums of random Hermitian matrices yield bounds on sums of random rectangular matrices.

## Statements

- [Hermitian dilation](dilation.md)
- [The Hermitian dilation is Hermitian](is-hermitian-dilation.md): the dilation is Hermitian
- [The Hermitian dilation is additive](dilation-add.md): additivity
- [The Hermitian dilation commutes with real scalars](dilation-smul.md): homogeneity for real scalars
- [Square of the Hermitian dilation](dilation-mul-self.md): its square is $\operatorname{diag}(BB^*, B^*B)$
- [The spectrum of the Hermitian dilation is symmetric](signature-mul-dilation-mul-signature.md): its spectrum is symmetric about $0$
