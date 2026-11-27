# A Householder reflection maps a vector to a multiple of the first unit vector

For a unit vector $u \in \mathbb{R}^n$, the Householder reflection $H = I - 2uu^{\mathsf T}$ is symmetric and orthogonal, $H H^{\mathsf T} = I$; it reflects in the hyperplane orthogonal to $u$. For $x \in \mathbb{R}^n$, $x \ne 0$, let $c \in \{\|x\|_2, -\|x\|_2\}$ with $x \ne c e_1$, $y = x - c e_1$ and $u = y/\|y\|_2$. Then

$$H x = c\, e_1 .$$

The choice $c = -\operatorname{sign}(x_1)\|x\|_2$, with $\operatorname{sign}(0) = 1$, that is $y = (x_1 + \operatorname{sign}(x_1)\|x\|_2, x_2, \dots, x_n)$, avoids cancellation when $y$ is formed in floating-point arithmetic.

## Related topics

- [Spectrum, determinant and norm of a generalized Householder matrix](../../special-matrices/generalized-householder-matrices/spectrum-one-sub-smul-vec-mul-vec.md)

## Sources

- J. W. Demmel, Math 221 (Applied Numerical Linear Algebra), University of California, Berkeley, Fall 2024, typed notes of Lecture 7 (least squares, 4 October 2024), the section on Householder transformations: orthogonality of $H$, the derivation $u = (x - c e_1)/(2u^{\mathsf T}x)$ with $|c| = \|x\|_2$, and the sign choice. <https://people.eecs.berkeley.edu/~demmel/ma221_Fall24/Lectures/Lecture_07.txt>
