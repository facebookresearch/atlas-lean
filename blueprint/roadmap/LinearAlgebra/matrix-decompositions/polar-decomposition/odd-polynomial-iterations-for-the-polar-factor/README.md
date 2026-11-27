# Odd polynomial iterations for the polar factor

Let $X$ be a real $m \times n$ matrix with compact singular value decomposition
$X = U_r \Sigma_r V_r^{\mathsf{T}}$, $r = \operatorname{rank} X$, and canonical polar factor
$P(X) = U_r V_r^{\mathsf{T}}$ ($P(0) = 0$). An odd polynomial $p(x) = \sum_{j=0}^{q} a_j x^{2j+1}$ acts on
$X$ by $p(X) = \sum_{j=0}^{q} a_j X (X^{\mathsf{T}} X)^j$, and $p(X) = U_r \, p(\Sigma_r) \, V_r^{\mathsf{T}}$,
with $(p \circ p')(X) = p(p'(X))$ for odd $p, p'$. The cubic Newton–Schulz iteration
$X_{t+1} = \tfrac{3}{2} X_t - \tfrac{1}{2} X_t X_t^{\mathsf{T}} X_t$ converges to $P(X_0)$ when every positive
singular value of $X_0$ lies in $(0, \sqrt{3})$, which holds for $X_0 = G/\|G\|_F$ when $G \ne 0$, and
then $P(X_0) = P(G)$. For a fixed odd polynomial $p$, integers $m, n \ge 1$ and $0 < \ell \le u$, the largest
value of $\|P(M) - p(M)\|_2$ over real $m \times n$ matrices $M$ with all singular values in $[\ell, u]$ is
$\max_{x \in [\ell, u]} |1 - p(x)|$.

## Idea

Odd polynomials act on a rectangular matrix through its singular values: $X (X^{\mathsf T} X)^j$ has
the singular vectors of $X$ and the singular values $\sigma_i^{2j+1}$. So the iteration
$X \mapsto p(X)$ runs the scalar iteration $x \mapsto p(x)$ on every positive singular value at once,
zero singular values stay zero, and the iterates converge to the polar factor exactly when the scalar
iterations of the positive singular values converge to $1$. For the cubic map $(3x - x^3)/2$ the values
in $(0, 1)$ increase to $1$ and those in $[1, \sqrt{3})$ land in $(0, 1]$. The method needs only matrix
products, which is why optimizers that orthogonalize their updates use such iterations.

## Statements

- [Odd polynomial iterations for the polar factor](odd-polynomial-polar-iterations.md)

## Background

- [Polar decomposition](../polar-decomposition-theorem/README.md): the canonical polar factor
