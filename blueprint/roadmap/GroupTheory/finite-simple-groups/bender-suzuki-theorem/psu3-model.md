# The group $\mathrm{PSU}(3, 2^n)$

Let $n \ge 1$, let $q = 2^n$ and let $J$ be the
$3 \times 3$ matrix with ones on the antidiagonal and zeros elsewhere. Then $\mathrm{PSU}(3, q)$
is the image in the projective general linear group $\mathrm{PGL}(3, \mathrm{GF}(q^2))$ of the
group of matrices $A \in \mathrm{GL}(3, \mathrm{GF}(q^2))$ with $\det A = 1$ and
$\bar{A}^{\mathsf{T}} J A = J$, where $\bar{A}$ is obtained from $A$ by applying $z \mapsto z^q$ to
every entry. For $n = 0$ the same construction is taken over $\mathrm{GF}(2)$ instead, with
$z \mapsto z^q$ the identity.

The map $z \mapsto z^q$ is the involution of $\mathrm{GF}(q^2)$ whose fixed field is
$\mathrm{GF}(q)$, so these are the isometries of determinant one of the Hermitian form with Gram
matrix $J$, taken modulo scalars.
