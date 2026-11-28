# Pseudoinverse

Let $V$ and $W$ be inner product spaces over $\mathbb F = \mathbb R$ or $\mathbb C$, with $V$ finite-dimensional, and
let $T \colon V \to W$ be a linear map. The pseudoinverse of $T$ is the linear map $T^\dagger \colon W \to V$ that sends
$w \in W$ to the unique vector of $(\operatorname{null} T)^\perp$ that $T$ maps to the orthogonal projection of $w$ onto
$\operatorname{range} T$.

## Idea

The pseudoinverse solves $Tv = w$ as well as possible: $T(T^\dagger w)$ is the point of $\operatorname{range} T$ closest
to $w$, and among the vectors $v$ that minimize $\lVert Tv - w \rVert$, $T^\dagger w$ is the one of smallest norm. If $T$
is invertible, $T^\dagger = T^{-1}$; in general $T T^\dagger$ is the orthogonal projection of $W$ onto
$\operatorname{range} T$, and $T^\dagger T$ that of $V$ onto $(\operatorname{null} T)^\perp$. For example, for
$T \colon \mathbb R \to \mathbb R^2$, $x \mapsto (x, x)$, the point of the range closest to $(a, b)$ is
$\tfrac{a + b}{2} (1, 1)$, so $T^\dagger(a, b) = (a + b)/2$: the least-squares fit of one number to two observations is
their mean. When $W$ is finite-dimensional too and $Tv = \sum_k s_k \langle v, e_k\rangle f_k$ for orthonormal lists
$(e_k)$, $(f_k)$ and the positive singular values $s_k$ of $T$, then $T^\dagger w = \sum_k s_k^{-1} \langle w, f_k\rangle e_k$.
For a matrix, with the standard inner products, $T^\dagger$ is the Moore–Penrose inverse.

## Statements

- [Pseudoinverse of a linear map](moore-penrose-pseudoinverse.md)

## Sources

- S. Axler, *Linear Algebra Done Right*, 4th ed., 6.68, with 6.69, 6.70 and 7.75 (version read: the open-access PDF dated 4 November 2026).
