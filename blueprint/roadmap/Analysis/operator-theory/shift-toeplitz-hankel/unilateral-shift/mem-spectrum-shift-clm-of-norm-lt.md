# The open unit ball lies in the spectrum of the unilateral shift

Let $\mathbb{K}$ be
$\mathbb{R}$ or $\mathbb{C}$ and let $S$ be the unilateral shift on
$\ell^2(\mathbb{N}, \mathbb{K})$. Every $\mu \in \mathbb{K}$ with $\|\mu\| < 1$ lies in the
spectrum of $S$ in the algebra of bounded operators on $\ell^2(\mathbb{N}, \mathbb{K})$.

Indeed, write $I$ for the identity operator. If $\mu I - S$ were invertible it would be
surjective, so $(\mu I - S)x = v$ for some $x$, where $v = (1, \bar\mu, \bar\mu^2, \dots)$ is the
geometric vector of the conjugate $\bar\mu$. Since the adjoint of $S$ is the backward shift $B$
and $Bv = \bar\mu v$, pairing $(\mu I - S)x = v$ with $v$ gives $\|v\|^2 = 0$, contradicting
$v \neq 0$.
